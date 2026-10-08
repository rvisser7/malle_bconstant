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


def quadratic_extension(Ky, beta, reduce=True):
    """Absolute polynomial of K(sqrt(beta)) (polredbest unless reduce=False),
    or None if not a field."""
    rel = pari('(K,b)->rnfequation(nfinit(K), x^2 - b)')(Ky, beta)
    if not pari.polisirreducible(rel):
        return None
    return pari.polredbest(rel) if reduce else rel


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


def _load_tables(degree=16):
    groups, subs = [], collections.defaultdict(list)
    path = os.path.join(TABLES, f'cycle_types_deg{degree}.txt')
    for ln in open(path).read().replace('\\\n', '').replace('\n ', ' ').splitlines():
        if ln.strip():
            k, sz, gid, dist = ln.split('|')
            groups.append((int(k), int(sz), tuple(eval(gid.replace(' ', ''))), _parse_dist(dist)))
    path = os.path.join(TABLES, f'index2_subgroups_deg{degree}.txt')
    if os.path.exists(path):
        for ln in open(path).read().replace('\\\n', '').replace('\n ', ' ').splitlines():
            if ln.strip():
                k, gid, dist = ln.split('|')
                subs[int(k)].append((tuple(eval(gid.replace(' ', ''))), _parse_dist(dist)))
    return groups, subs


_TABLES = {}


def tables(degree=16):
    """Cycle-type tables for transitive groups of the given degree (regenerate
    with gap/cycle_types.g for degree 16, gap/cycle_types_deg24.g for 24)."""
    if degree not in _TABLES:
        _TABLES[degree] = _load_tables(degree)
    return _TABLES[degree]


def frobenius_cycle_types(f, nprimes, split_in=None, start=7):
    """Counter of factorisation patterns of f mod p over unramified p.  With
    split_in=q, only primes p with (q/p) = 1 are used (Frobenius in the
    index-2 subgroup fixing sqrt(q))."""
    # p is unramified for f exactly when f mod p is squarefree of full degree,
    # so no discriminant is needed (expensive for large f).
    lc, deg = int(pari.pollead(f)), int(pari.poldegree(f))
    cnt, p, n = collections.Counter(), start, 0
    while n < nprimes:
        p = int(pari.nextprime(p + 1))
        if lc % p == 0:
            continue
        if split_in is not None and pari.kronecker(split_in, p) != 1:
            continue
        fa = pari.factormod(f, p)
        if any(int(m) > 1 for m in fa[1]):
            continue
        degs = []
        for j in range(len(fa[0])):
            degs += [int(pari.poldegree(fa[0][j]))] * int(fa[1][j])
        cnt[tuple(sorted(degs))] += 1
        n += 1
    return cnt


def identify(f, order, nprimes=1500):
    """Rank the transitive groups of degree deg(f) and the given order by the
    log-likelihood of f's Frobenius cycle types.  Groups whose class support
    misses an observed cycle type are excluded.  Returns [(loglik, k, id)]."""
    groups, _ = tables(int(pari.poldegree(f)))
    cnt = frobenius_cycle_types(f, nprimes)
    res = []
    for k, sz, gid, dist in groups:
        if sz != order or any(c not in dist for c in cnt):
            continue
        res.append((sum(n * math.log(dist[c]) for c, n in cnt.items()), k, gid))
    return sorted(res, reverse=True)


def quadratic_subgroup(f, k, q=5, nprimes=1500):
    """Which index-2 subgroup of nTk (n = deg f) is Gal(closure/Q(sqrt q))?
    Ranked list [(loglik or None if excluded by support, id)]."""
    _, subs = tables(int(pari.poldegree(f)))
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


# --------------------------------------------------------------------------
# Permutation modules: submodules of F2[conjugates] of a given dimension
# --------------------------------------------------------------------------
def embedding_permutations(K, P, embs=None, auts=None):
    """Permutations of the embeddings K -> P induced by Gal(P/Q) (P Galois).

    Computed modulo a prime p splitting completely in P, with the embeddings
    distinguished by their values at one root r0: the automorphism s sends
    e_i to the e_j with e_j(r0) = e_i(s(r0))."""
    if embs is None:
        embs = pari.nfisincl(K, P)
    if auts is None:
        gal = pari.galoisinit(P)
        auts = [pari.galoispermtopol(gal, g) for g in pari('(g)->g.group')(gal)]
    n, disc = int(pari.poldegree(P)), int(pari.poldisc(P))
    p = 1000
    while True:
        p = int(pari.nextprime(p + 1))
        if disc % p == 0:
            continue
        R = [int(pari.lift(r)) for r in pari.polrootsmod(P, p)]
        if len(R) != n:
            continue
        r0 = R[0]
        ev = lambda f, r: int(pari.lift(pari.Mod(pari.subst(pari.lift(f), 'x', r), p)))
        at_r0 = [ev(e, r0) for e in embs]
        if len(set(at_r0)) == len(embs):
            break
    index = {v: i for i, v in enumerate(at_r0)}
    perms = []
    for s_ in auts:
        rs = ev(s_, r0)
        perms.append([index[ev(e, rs)] for e in embs])
    return perms


def _span(vecs, n):
    rows = [int(''.join(map(str, v)), 2) for v in vecs]
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r:
            basis.append(r)
    return frozenset(basis), len(basis)


def submodules_of_dim(perms, n, r):
    """All F2[G]-submodules of dimension r of the permutation module F2^n,
    G generated by the given permutations.  Returned as lists of 0/1 vectors."""
    def act(v, p):                      # v as int; coordinate i -> p[i]
        w = 0
        for i in range(n):
            if (v >> (n - 1 - i)) & 1:
                w |= 1 << (n - 1 - p[i])
        return w

    def closure(gens):
        basis = set()
        todo = list(gens)
        span = {0}
        while todo:
            v = todo.pop()
            if v in span:
                continue
            new = {x ^ v for x in span}
            span |= new
            for p in perms:
                w = act(v, p)
                if w not in span:
                    todo.append(w)
            if len(span) > 2 ** r:
                return None
        return frozenset(span)

    found = set()
    small = set()
    for v in range(1, 2 ** n):
        S = closure([v])
        if S is not None:
            small.add(S)
    # sums of small submodules until no new ones of dimension <= r appear
    changed = True
    while changed:
        changed = False
        cur = list(small)
        for i in range(len(cur)):
            for j in range(i + 1, len(cur)):
                if len(cur[i]) * len(cur[j]) > 2 ** (2 * r):
                    continue
                S = frozenset(a ^ b for a in cur[i] for b in cur[j])
                if len(S) <= 2 ** r and S not in small:
                    small.add(S)
                    changed = True
    for S in small:
        if len(S) == 2 ** r:
            found.add(S)
    out = []
    for S in found:
        vecs = sorted(S - {0})
        _, d = _span([list(map(int, format(v, f'0{n}b'))) for v in vecs], n)
        out.append([list(map(int, format(v, f'0{n}b'))) for v in vecs])
    return out


def orthogonal_complement_basis(vectors, n):
    """Basis of N^perp (standard dot product) for N spanned by vectors."""
    if not vectors:
        return [list(r) for r in np.eye(n, dtype=np.uint8)]
    ker = gf2_kernel(np.array(vectors, dtype=np.uint8))
    return [list(map(int, v)) for v in ker]


# --------------------------------------------------------------------------
# Exact Galois group of K(sqrt delta) by Kummer theory over a Galois field P
# --------------------------------------------------------------------------
def kummer_galois_group(K, P, delta, q=5):
    """Exact Gal(L/Q) for L = Galois closure of K(sqrt delta), K a subfield of
    the Galois field P, delta in K (polynomial in y) whose conjugates are not
    squares.  L = P(sqrt delta_1, ..., sqrt delta_n), delta_i = e_i(delta) for
    the embeddings e_i : K -> P.  Returns (gens, chi) where gens are
    permutations of the 2n points (i, +/-) -> index 2*i + (0 or 1) (0-based)
    generating Gal(L/Q), and chi[g] = 0/1 says whether the generator moves
    sqrt(q) (q = None to skip).

    Each sigma in Gal(P/Q) lifts as sqrt(delta_i) -> s_i sqrt(delta_pi(i)); the
    sign vectors s are cut out by the multiplicative relations among the
    delta_i, which are certified to be exact squares in P with nfroots.
    """
    Py = pari.subst(P, 'x', 'y')
    nfP = pari.nfinit(Py)
    gal = pari.galoisinit(P)
    auts = [pari.galoispermtopol(gal, g) for g in pari('(g)->g.gen')(gal)]
    embs = [pari.lift(pari.Mod(e, P)) for e in pari.nfisincl(K, P)]
    n = len(embs)
    perms = embedding_permutations(K, P, embs, auts)
    dl = [pari.subst(pari.lift(delta), 'y', pari.Mod(e, P)) for e in embs]      # delta_i in P (var x)

    # relations mod squares, from Legendre symbols at split primes of P
    disc, deg, p, cols = int(pari.poldisc(P)), int(pari.poldegree(P)), 2, []
    while len(cols) < 40 * n:
        p = int(pari.nextprime(p + 1))
        if disc % p == 0:
            continue
        R = pari.polrootsmod(P, p)
        if len(R) != deg:
            continue
        for r in pari.lift(R):
            vals = [int(pari.lift(pari.subst(pari.lift(d), 'x', pari.Mod(r, p)))) for d in dl]
            if any(v == 0 for v in vals):
                cols = cols                              # ramified-ish; skip this root
                continue
            cols.append([0 if pari.kronecker(v, p) == 1 else 1 for v in vals])
    A = np.array(cols, dtype=np.uint8).T                 # n x m
    rels = gf2_kernel(A.T)                               # R with sum_i R_i v_i = 0
    rank = n - len(rels)
    # basis indices B (independent mod squares) and, for each j not in B, a relation R_j = {j} + subset of B
    B = []
    for i in range(n):
        if gf2_rank(A[B + [i]]) > len(B):
            B.append(i)
    assert len(B) == rank
    Rj = {}
    for j in range(n):
        if j in B:
            continue
        for v in rels:
            if v[j] and all(v[i] == 0 or i in B or i == j for i in range(n)):
                Rj[j] = [i for i in range(n) if v[i]]
                break
        else:
            # combine: find relation through linear algebra on columns B + [j]
            sub = gf2_kernel(A[B + [j]].T)
            v = sub[0]
            Rj[j] = [([*B, j])[t] for t in range(len(v)) if v[t]]
    def sqrt_in_P(a):
        rts = pari.nfroots(nfP, pari('x^2') - pari.subst(pari.lift(a), 'x', 'y'))
        if len(rts) == 0:
            raise ValueError("relation is not a square in P (increase primes)")
        return pari.Mod(pari.subst(pari.lift(rts[0]), 'y', 'x'), P)
    gam = {}
    for j, R in Rj.items():
        prod = pari.Mod(1, P)
        for i in R:
            prod *= dl[i]
        gam[j] = sqrt_in_P(prod)

    def Gamma(Rset):
        """prod_{i in Rset} r_i expressed in P, where r_j := gam_j / prod_{b in R_j, b != j} r_b."""
        Rset = set(Rset)
        expo = {b: (1 if b in Rset else 0) for b in B}
        val = pari.Mod(1, P)
        for j in Rset:
            if j in B:
                continue
            val *= gam[j]
            for b in Rj[j]:
                if b != j:
                    expo[b] -= 1
        for b, e in expo.items():
            assert e % 2 == 0, "not a relation"
            val *= dl[b] ** (e // 2)
        return val

    def lift(s_aut, pi, sB):
        s = {b: sB[t] for t, b in enumerate(B)}
        for j, R in Rj.items():
            img = pari.subst(pari.lift(gam[j]), 'x', pari.Mod(s_aut, P))   # evaluate mod P (no blow-up)
            ratio = img / Gamma([pi[i] for i in R])
            c = 1 if ratio == 1 else -1 if ratio == -1 else None
            assert c is not None, "inconsistent lift"
            prod = 1
            for b in R:
                if b != j:
                    prod *= s[b]
            s[j] = c * prod
        perm = [0] * (2 * n)
        for i in range(n):
            for e in (0, 1):
                tgt_sign = e if s[i] == 1 else 1 - e
                perm[2 * i + e] = 2 * pi[i] + tgt_sign
        return perm

    sq = None
    if q is not None:
        rts = pari.nfroots(nfP, pari(f'x^2-({q})'))
        sq = pari.Mod(pari.subst(pari.lift(rts[0]), 'y', 'x'), P) if len(rts) else None
    gens, chi = [], []
    ident = pari.Mod(pari('x'), P)
    for a, pi in zip(auts, perms):
        gens.append(lift(a, pi, [1] * rank))
        chi.append(0 if sq is None or pari.subst(pari.lift(sq), 'x', pari.Mod(a, P)) == sq else 1)
    idperm = list(range(n))
    for t in range(rank):
        sB = [1] * rank
        sB[t] = -1
        gens.append(lift(pari('x'), idperm, sB))
        chi.append(0)
    return gens, chi, rank


def gap_identify(gens, chi, degree, gap='gap'):
    """IdGroup of the group generated by gens (0-based images), its transitive
    identification, and IdGroup of the kernel of chi (IdGroup replaced by
    [order, 0] where GAP has no identification, e.g. order 768).  Uses GAP
    via subprocess.  Output: "RESULT size [id] nTk index [id of kernel] SIGPOS p".
    SIGPOS p: the kernel is the p-th index-2 normal subgroup of the library
    group TransitiveGroup(degree, k), the subgroups sorted by their cycle-type
    signature (sorted list of [cycle type, class size]); p = 0 when the
    kernel's signature is shared by another index-2 subgroup.  This names H0 where IdGroup cannot (order 768)."""
    import subprocess, tempfile
    cyc = lambda g: 'PermList([' + ','.join(str(x + 1) for x in g) + '])'
    script = f'''LoadPackage("transgrp");; LoadPackage("smallgrp");;
gens := [{','.join(cyc(g) for g in gens)}];;
chi := {chi};;
H := Group(gens);;
C2 := CyclicGroup(IsPermGroup, 2);;
hom := GroupHomomorphismByImages(H, C2, gens, List(chi, c -> C2.1^c));;
H0 := Kernel(hom);;
SafeId := G -> function() if IdGroupsAvailable(Size(G)) then return IdGroup(G); else return [Size(G), 0]; fi; end;;
Sig := S -> SortedList(List(ConjugacyClasses(S), c -> [SortedList(CycleLengths(Representative(c), [1..{degree}])), Size(c)]));;
T := TransitiveGroup({degree}, TransitiveIdentification(H));;
sigs := SortedList(List(Filtered(NormalSubgroups(T), N -> Index(T, N) = 2), Sig));;
s0 := Sig(H0);; pos := Position(sigs, s0);; if pos = fail or Number(sigs, s -> s = s0) > 1 then pos := 0; fi;
Print("RESULT ", Size(H), " ", SafeId(H)(), " ", TransitiveIdentification(H), " ", Index(H, H0), " ", SafeId(H0)(),
      " SIGPOS ", pos, "\\n");
QUIT;
'''
    with tempfile.NamedTemporaryFile('w', suffix='.g', delete=False) as fh:
        fh.write(script)
        path = fh.name
    out = subprocess.run([gap, '-A', '-q', '-o', '4g', path], capture_output=True, text=True, timeout=600).stdout
    line = next((l for l in out.splitlines() if l.startswith('RESULT')), None)
    return line


def quick_reject(f, support, nprimes=60, start=7):
    """True if some Frobenius cycle type of f (over up to nprimes unramified
    primes) lies outside `support` (a set of sorted cycle-type tuples): then f
    cannot have any group with that support.  Cheap pre-screen for searches."""
    lc = int(pari.pollead(f))
    p, n = start, 0
    while n < nprimes:
        p = int(pari.nextprime(p + 1))
        if lc % p == 0:
            continue
        fa = pari.factormod(f, p)
        if any(int(m) > 1 for m in fa[1]):
            continue
        degs = []
        for j in range(len(fa[0])):
            degs += [int(pari.poldegree(fa[0][j]))] * int(fa[1][j])
        if tuple(sorted(degs)) not in support:
            return True
        n += 1
    return False
