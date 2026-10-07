"""Shared helpers for the witness-search scripts (PARI/GP via cypari2).

These scripts only *find* candidate witness fields.  Nothing here is trusted:
every polynomial must still be added to data/witnesses/witnesses.txt and
re-proved by magma/verify_witnesses_<ordering>.m.

Conventions
-----------
* Polynomials are PARI objects in the variable x.  Number-field arithmetic is
  done with the field polynomial in y (PARI variable priority).
* "Legendre coordinates": an element g of a number field K is mapped to the
  F2-vector of quadratic residue symbols of g at many degree-1 primes of a
  Galois field P containing all conjugates of K.  On a finitely generated
  group of S-units modulo squares this map is injective once enough primes
  are used (Chebotarev), which turns Kummer theory into F2 linear algebra.
"""
import collections
import itertools
import math
import os

import cypari2
import numpy as np

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)

HERE = os.path.dirname(os.path.abspath(__file__))
TABLES = os.path.join(HERE, "tables")

_legendre_vec = pari('(f,R,p)->[kronecker(lift(Mod(subst(f,x,r),p)),p) | r<-R]')
_subgroup_order = pari('(H)->vecprod(Vec(H[2]))')


# --------------------------------------------------------------------------
# F2 linear algebra
# --------------------------------------------------------------------------
def gf2_rank(A):
    A = np.array(A, dtype=np.uint8) % 2
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        p = next((i for i in range(r, rows) if A[i, c]), None)
        if p is None:
            continue
        A[[r, p]] = A[[p, r]]
        for i in range(rows):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == rows:
            break
    return r


def gf2_kernel(M):
    """Basis (list of uint8 vectors) of the right kernel of M over F2."""
    M = np.array(M, dtype=np.uint8) % 2
    rows, cols = M.shape
    piv, r = [], 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if M[i, c]), None)
        if p is None:
            continue
        M[[r, p]] = M[[p, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        piv.append(c)
        r += 1
        if r == rows:
            break
    basis = []
    for f in (c for c in range(cols) if c not in piv):
        v = np.zeros(cols, dtype=np.uint8)
        v[f] = 1
        for i, pc in enumerate(piv):
            if M[i, f]:
                v[pc] = 1
        basis.append(v)
    return basis


def span_combinations(basis, length, limit, rng):
    """Nonzero F2-combinations of `basis`: all of them if there are at most
    `limit`, otherwise `limit` random ones."""
    k = len(basis)
    if k == 0:
        return
    if 2**k - 1 <= limit:
        coeff_iter = (c for c in itertools.product((0, 1), repeat=k) if any(c))
    else:
        coeff_iter = (tuple(rng.randint(0, 1) for _ in range(k)) for _ in range(limit))
    for c in coeff_iter:
        e = np.zeros(length, dtype=np.uint8)
        for ci, b in zip(c, basis):
            if ci:
                e ^= b
        if e.any():
            yield e


# --------------------------------------------------------------------------
# Number fields
# --------------------------------------------------------------------------
def sunit_generators(Ky, Sprimes):
    """Generators of the S-units of K (torsion, fundamental units, S-units) as
    polynomials in y; their classes span O_{K,S}^x / squares."""
    bnf = pari.bnfinit(Ky, 1)
    S = [P for q in Sprimes for P in pari.idealprimedec(bnf, q)]
    su = pari.bnfsunit(bnf, S)
    gens = [pari.lift(pari('(b)->b.tu')(bnf)[1])]
    gens += [pari.lift(u) for u in pari('(b)->b.fu')(bnf)]
    gens += [pari.lift(pari.nfbasistoalg(bnf, u)) for u in su[0]]
    return gens


def product_of(gens, e, Ky):
    d = pari.Mod(1, Ky)
    for g, x in zip(gens, e):
        if x:
            d *= pari.Mod(g, Ky)
    return pari.lift(d)


def quadratic_extension(Ky, beta):
    """Absolute polynomial (polredbest) of K(sqrt(beta)), or None if not a field."""
    rel = pari('(K,b)->rnfequation(nfinit(K), x^2 - b)')(Ky, beta)
    if not pari.polisirreducible(rel):
        return None
    return pari.polredbest(rel)


def contains_sqrt(S, q):
    return len(pari.nfroots(pari.subst(S, 'x', 'y'), pari(f'x^2-({q})'))) > 0


def contains_zeta(S, m):
    return len(pari.nfroots(pari.subst(S, 'x', 'y'), pari.polcyclo(m))) > 0


# --------------------------------------------------------------------------
# Exact identification for (weakly super-)solvable closures via galoisinit
# --------------------------------------------------------------------------
def closure_group(M):
    """(S, gal, [order, id]) for the Galois closure of M.  Raises if PARI's
    galoisinit cannot handle the group (e.g. groups with an S4 quotient)."""
    S = pari.nfsplitting(M)
    gal = pari.galoisinit(S)
    return S, gal, [int(t) for t in pari.galoisidentify(gal)]


def subgroup_fixing_sqrt(S, gal, q=5):
    """SmallGroup id of Gal(S/Q(sqrt q)), or None if sqrt(q) is not in S."""
    n = int(pari.poldegree(S))
    target = pari.polredabs(pari(f'x^2-({q})'))
    for H in pari.galoissubgroups(gal):
        if int(_subgroup_order(H)) != n // 2:
            continue
        if pari.polredabs(pari.galoisfixedfield(gal, H, 1)) == target:
            return [int(t) for t in pari.galoisidentify(H)]
    return None


def octic_subfields(M1):
    """Closure P of M1 and its degree-8 subfields on which Gal(P/Q) acts
    faithfully, up to isomorphism."""
    P = pari.nfsplitting(M1)
    n = int(pari.poldegree(P))
    gal = pari.galoisinit(P)
    out = []
    for U in pari.galoissubgroups(gal):
        if int(_subgroup_order(U)) != n // 8:
            continue
        K = pari.polredbest(pari.galoisfixedfield(gal, U, 1))
        if int(pari.poldegree(pari.nfsplitting(K))) == n and \
                all(not pari.nfisisom(K, k0) for k0 in out):
            out.append(K)
    return P, out


# --------------------------------------------------------------------------
# Statistical identification in degree 16 (for closures galoisinit cannot do)
# --------------------------------------------------------------------------
def _parse_dist(text):
    d = collections.Counter()
    for cyc, n in eval(text.replace(' ', '')):
        d[tuple(sorted(cyc))] += n
    tot = sum(d.values())
    return {c: n / tot for c, n in d.items()}


def _load_tables():
    groups, subs = [], collections.defaultdict(list)
    path = os.path.join(TABLES, 'cycle_types_deg16.txt')
    for ln in open(path).read().replace('\\\n', '').replace('\n ', ' ').splitlines():
        if ln.strip():
            k, sz, gid, dist = ln.split('|')
            groups.append((int(k), int(sz), tuple(eval(gid.replace(' ', ''))), _parse_dist(dist)))
    path = os.path.join(TABLES, 'index2_subgroups_deg16.txt')
    for ln in open(path).read().replace('\\\n', '').replace('\n ', ' ').splitlines():
        if ln.strip():
            k, gid, dist = ln.split('|')
            subs[int(k)].append((tuple(eval(gid.replace(' ', ''))), _parse_dist(dist)))
    return groups, subs


_TABLES = None


def tables():
    global _TABLES
    if _TABLES is None:
        _TABLES = _load_tables()
    return _TABLES


def frobenius_cycle_types(f, nprimes, split_in=None, start=7):
    """Counter of factorisation patterns of f mod p over unramified p.  With
    split_in=q, only primes p with (q/p) = 1 are used (Frobenius in the
    index-2 subgroup fixing sqrt(q))."""
    disc = int(pari.poldisc(f))
    cnt, p, n = collections.Counter(), start, 0
    while n < nprimes:
        p = int(pari.nextprime(p + 1))
        if disc % p == 0:
            continue
        if split_in is not None and pari.kronecker(split_in, p) != 1:
            continue
        fa = pari.factormod(f, p)
        degs = []
        for j in range(len(fa[0])):
            degs += [int(pari.poldegree(fa[0][j]))] * int(fa[1][j])
        cnt[tuple(sorted(degs))] += 1
        n += 1
    return cnt


def identify(f, order, nprimes=1500):
    """Rank the degree-16 transitive groups of the given order by the
    log-likelihood of f's Frobenius cycle types.  Groups whose class support
    misses an observed cycle type are excluded.  Returns [(loglik, k, id)]."""
    groups, _ = tables()
    cnt = frobenius_cycle_types(f, nprimes)
    res = []
    for k, sz, gid, dist in groups:
        if sz != order or any(c not in dist for c in cnt):
            continue
        res.append((sum(n * math.log(dist[c]) for c, n in cnt.items()), k, gid))
    return sorted(res, reverse=True)


def quadratic_subgroup(f, k, q=5, nprimes=1500):
    """Which index-2 subgroup of 16Tk is Gal(closure/Q(sqrt q))?  Ranked list
    [(loglik or None if excluded by support, id)]."""
    _, subs = tables()
    cnt = frobenius_cycle_types(f, nprimes, split_in=q)
    res = []
    for gid, dist in subs[k]:
        if any(c not in dist for c in cnt):
            res.append((None, gid))
        else:
            res.append((sum(n * math.log(dist[c]) for c, n in cnt.items()), gid))
    return sorted(res, key=lambda t: -1e300 if t[0] is None else t[0], reverse=True)


# --------------------------------------------------------------------------
# Galois base field: S-units mod squares as an F2[Gal]-module
# --------------------------------------------------------------------------
class GaloisBase:
    """A Galois number field E with its S-units modulo squares, represented by
    Legendre coordinates at degree-1 primes.  Automorphisms act by permuting
    those primes, so the F2[Gal(E/Q)]-module structure is available without
    ever applying an automorphism to an S-unit."""

    def __init__(self, E, Sprimes, nprimes=60):
        self.E = E
        self.Ey = pari.subst(E, 'x', 'y')
        self.gens = sunit_generators(self.Ey, Sprimes)
        self.auts = pari.nfgaloisconj(E)
        self.n = len(self.auts)
        if self.n != int(pari.poldegree(E)):
            raise ValueError("base field is not Galois over Q")
        pts, perms = [], [[] for _ in self.auts]
        p, used, disc = 2, 0, int(pari.poldisc(E))
        while used < nprimes:
            p = int(pari.nextprime(p + 1))
            if p in Sprimes or disc % p == 0:
                continue
            R = [int(pari.lift(r)) for r in pari.polrootsmod(E, p)]
            if len(R) != self.n:
                continue
            base, idx = len(pts), {r: i for i, r in enumerate(R)}
            for a, s in enumerate(self.auts):
                for r in R:
                    perms[a].append(base + idx[int(pari.lift(pari.Mod(pari.subst(s, 'x', r), p)))])
            pts += [(p, r) for r in R]
            used += 1
        self.perms = [np.array(P) for P in perms]
        C = np.zeros((len(pts), len(self.gens)), dtype=np.uint8)
        for j, g in enumerate(self.gens):
            gx = pari.subst(g, 'y', 'x')
            for k, (p, r) in enumerate(pts):
                v = int(pari.lift(pari.Mod(pari.subst(gx, 'x', r), p)))
                C[k, j] = 0 if pari.kronecker(v, p) == 1 else 1
        if gf2_rank(C) != len(self.gens):
            raise RuntimeError("Legendre coordinates not injective; increase nprimes")
        self.C = C

    def subgroups(self):
        """All subgroups of Gal(E/Q), as frozensets of automorphism indices."""
        n, E, auts = self.n, self.E, self.auts
        ident = next(k for k in range(n) if auts[k] == pari('x'))
        comp = {}
        for i in range(n):
            for j in range(n):
                c = pari.lift(pari.Mod(pari.subst(auts[i], 'x', auts[j]), E))
                comp[(i, j)] = next(k for k in range(n) if auts[k] == c)
        subs = set()
        for gs in itertools.chain.from_iterable(itertools.combinations(range(n), k) for k in range(3)):
            S = {ident} | set(gs)
            while True:
                new = S | {comp[(a, b)] for a in S for b in S}
                if new == S:
                    break
                S = new
            subs.add(frozenset(S))
        return sorted(subs, key=len)

    def fixed_space(self, autidx):
        """Basis of the classes fixed by the given automorphisms."""
        rows = [self.C[self.perms[a]] ^ self.C for a in autidx]
        if not rows:
            return [np.eye(len(self.gens), dtype=np.uint8)[i] for i in range(len(self.gens))]
        return gf2_kernel(np.vstack(rows))

    def orbit_span(self, e):
        """(dimension, matrix) of the F2-span of the Galois conjugates of e."""
        v = (self.C.astype(np.int64) @ e.astype(np.int64)) % 2
        V = np.array([v[P] for P in self.perms], dtype=np.uint8)
        return gf2_rank(V), V

    def element(self, e):
        return product_of(self.gens, e, self.Ey)


# --------------------------------------------------------------------------
# Non-Galois base field K: Legendre data of all conjugates inside a closure P
# --------------------------------------------------------------------------
class ConjugateData:
    """S-units of K (not necessarily Galois) together with the Legendre
    coordinates of each of their conjugates, evaluated at the degree-1 primes
    of a Galois field P containing K.  A[j, i, t] is the symbol of the i-th
    conjugate of generator j at point t."""

    def __init__(self, K, P, Sprimes, nprimes=20):
        self.K, self.P = K, P
        self.Ky = pari.subst(K, 'x', 'y')
        self.gens = sunit_generators(self.Ky, Sprimes)
        self.embs = pari.nfisincl(K, P)
        NP, ne = int(pari.poldegree(P)), len(self.embs)
        imgs = [[pari.lift(pari.Mod(pari.subst(g, 'y', e), P)) for e in self.embs] for g in self.gens]
        blocks, p, used, disc = [], 2, 0, int(pari.poldisc(P))
        while used < nprimes:
            p = int(pari.nextprime(p + 1))
            if p in Sprimes or disc % p == 0:
                continue
            R = pari.polrootsmod(P, p)
            if len(R) != NP:
                continue
            R = pari.lift(R)
            used += 1
            blocks.append(np.array([[[0 if int(v) == 1 else 1 for v in _legendre_vec(imgs[j][i], R, p)]
                                     for i in range(ne)] for j in range(len(self.gens))], dtype=np.uint8))
        self.A = np.concatenate(blocks, axis=2)

    def conjugate_rank(self, e):
        """Dimension of the span of the conjugates of e modulo squares in P."""
        M = np.zeros(self.A.shape[1:], dtype=np.uint8)
        for j in np.nonzero(e)[0]:
            M ^= self.A[j]
        return gf2_rank(M)

    def invariant_classes(self):
        """Basis of classes whose conjugates are all equal mod squares in P
        (so that P(sqrt(e)) is Galois over Q)."""
        D = self.A[:, 1:, :] ^ self.A[:, :1, :]
        return gf2_kernel(D.reshape(len(self.gens), -1).T)

    def classes_killed_by(self, Z, labels):
        """Basis of classes e with prod_i delta_i^{z_i} a square for every z in
        Z, where Z is given in label coordinates and labels[i] is the label of
        embedding i."""
        lab2emb = {lab: i for i, lab in enumerate(labels)}
        rows = []
        for z in Z:
            acc = np.zeros((len(self.gens), self.A.shape[2]), dtype=np.uint8)
            for lab, zz in enumerate(z):
                if zz:
                    acc ^= self.A[:, lab2emb[lab], :]
            rows.append(acc.T)
        return gf2_kernel(np.vstack(rows))

    def element(self, e):
        return product_of(self.gens, e, self.Ky)
