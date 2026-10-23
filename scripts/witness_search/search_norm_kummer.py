#!/usr/bin/env python3
"""Residual witnesses K(sqrt delta) with a norm condition, no Galois closure needed.

For a base field K (e.g. a sextic with Galois group S5 = PGL(2,5) = 6T14 or
S6 = 6T16) whose closure is far too big for PARI galoisinit, delta runs over
S-units of K modulo squares subject to linear conditions on norms:

  N_{K/Q}(delta) in Q*^2,

and delta not in Q* K*^2.  For K of degree n with a doubly transitive
closure group these are exactly the classes whose conjugates span the
(n-1)-dimensional "sum-zero" quotient, so K(sqrt delta) has Galois group an
extension of Gal(K~/Q) by C2^(n-1).  K(sqrt delta) is then identified by
Frobenius cycle-type statistics (tables/cycle_types_deg<2n>.txt).  This is a
filter: the extension class (which of the order-|G| groups occurs) is decided
by local conditions, and the final group must be confirmed exactly (Magma
verifier).

Written for 30T4059 (Oct 2026): H = G/O_5(G) = 12T256 = C2^5 . S5 (order 3840),
H0 = C2^5 : A5 is the unique index-2 subgroup, so K is an S5 sextic (6T14) with
disc in 5*Q^2 (the sextic resolvent of an S5 quintic with disc in 5*Q^2, see
quintic_sextic_resolvent below).  K(sqrt delta) lies in C2 wr S6; with
N(delta) a square its group is the split 12T257, and the non-split 12T256
(sign of the S5 part = parity of the C2^6 part) needs N(delta) in disc(K) Q*^2,
i.e. --norm-class 5.

Example:
  python3 search_norm_kummer.py --base "x^6-x^5-10*x^4+32*x^3-41*x^2-140*x+380" \\
      --order 3840 --targets 256 --norm-class 5
"""
import argparse
import itertools
import random
import sys
import time

import numpy as np

import wslib
from wslib import pari


def quintic_sextic_resolvent(f):
    """Sextic field (6T14 for an S5 quintic) fixed by F20 = AGL(1,5) inside the
    S5 closure of the quintic f: product of (X - theta_c) over the six cosets c
    of F20, theta_c a coset sum of a generic monomial in the roots (numerical,
    rounded).  Returns polredabs of the sextic."""
    def mul(p, q):
        return tuple(p[q[i]] for i in range(len(q)))
    F20, frontier = {tuple(range(5))}, [tuple(range(5))]
    while frontier:
        new = []
        for g in frontier:
            for h in [(1, 2, 3, 4, 0), (0, 2, 4, 1, 3)]:
                x = mul(g, h)
                if x not in F20:
                    F20.add(x)
                    new.append(x)
        frontier = new
    cosets, seen = [], set()
    for g in itertools.permutations(range(5)):
        if g not in seen:
            c = {mul(g, h) for h in F20}
            seen |= c
            cosets.append(sorted(c))
    old = pari.default('realprecision')
    pari.set_real_precision(300)
    try:
        r = pari.polroots(pari(f))
        for mono in [(0, 1, 2, 3, 0), (0, 1, 1, 2, 0), (1, 2, 3, 0, 0)]:
            vals = []
            for c in cosets:
                s = 0
                for g in c:
                    t = 1
                    for i, e in enumerate(mono):
                        t *= r[g[i]] ** e
                    s += t
                vals.append(s)
            X, S = pari('x'), 1
            for v in vals:
                S *= (X - v)
            co = pari.Vec(S)
            if max(abs(float(pari.imag(c))) + abs(float(pari.real(c) - pari.round(pari.real(c)))) for c in co) > 1e-6:
                continue
            S = pari.Pol([pari.round(pari.real(c)) for c in co])
            if pari.poldisc(S) != 0 and pari.polisirreducible(S):
                return pari.polredabs(S)
    finally:
        pari.set_real_precision(int(old))
    raise ValueError("no squarefree resolvent found")


def rational_vector(a, primes):
    """F2 vector (sign, v_p mod 2 for p in primes) of a nonzero rational S-unit a."""
    a = pari(a)
    v = [1 if a < 0 else 0]
    for p in primes:
        v.append(int(pari.valuation(a, p)) % 2)
    return v


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--base', help='polynomial of K (or use --quintic)')
    ap.add_argument('--quintic', help='S5 quintic; K = its sextic resolvent (6T14)')
    ap.add_argument('--S', default='2,3,5', help='primes always in S; primes dividing disc K are added')
    ap.add_argument('--norm-class', type=int, default=1,
                    help='require N_{K/Q}(delta) in a*Q*^2 (default 1; use the discriminant class of K for the '
                         'non-split extension, e.g. 5 for 12T256)')
    ap.add_argument('--order', type=int, required=True)
    ap.add_argument('--targets', required=True, help='comma-separated transitive ids (degree 2 deg K)')
    ap.add_argument('--max', type=int, default=20000)
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    t0 = time.time()
    rng = random.Random(args.seed)
    targets = {int(t) for t in args.targets.split(',')}

    K = quintic_sextic_resolvent(args.quintic) if args.quintic else pari.polredabs(pari(args.base))
    n = int(pari.poldegree(K))
    Ky = pari.subst(K, 'x', 'y')
    Sprimes = sorted({int(t) for t in args.S.split(',')} | {int(p) for p in pari.factor(abs(int(pari.nfdisc(K))))[0]})
    gens = wslib.sunit_generators(Ky, Sprimes)
    r = len(gens)
    print(f"K = {K}, Galois {pari.polgalois(K)}, disc {pari.factor(pari.nfdisc(K))}; S = {Sprimes}; "
          f"{r} S-unit generators; {time.time()-t0:.0f}s", flush=True)

    # Legendre coordinates at degree-1 primes of K (injective on S-units / squares)
    cols, prs, p = [], [], 7
    lc = int(pari.pollead(K))
    while len(cols) < 4 * r + 40:
        p = int(pari.nextprime(p + 1))
        if p in Sprimes or lc % p == 0:
            continue
        for root in pari.lift(pari.polrootsmod(K, p)):
            try:
                vals = [int(pari.lift(pari.subst(pari.lift(g), 'y', pari.Mod(root, p)))) for g in gens]
            except Exception:                                  # p divides a denominator
                continue
            if any(v == 0 for v in vals):
                continue
            cols.append([0 if pari.kronecker(v, p) == 1 else 1 for v in vals])
            prs.append(p)
    L = np.array(cols, dtype=np.uint8).T                       # r x m: generator -> Legendre vector
    assert wslib.gf2_rank(L) == r, "Legendre coordinates not injective; increase primes"

    # norm condition: N_{K/Q}(delta) a square
    Nmat = np.array([rational_vector(pari.norm(pari.Mod(g, Ky)), Sprimes) for g in gens], dtype=np.uint8)   # r x (1+|S|)
    ker = wslib.gf2_kernel(Nmat.T)                             # exponent vectors e with e * Nmat = 0
    # particular solution of e * Nmat = vector(norm_class): kernel vector of [Nmat | t] with last entry 1
    t = np.array(rational_vector(args.norm_class, Sprimes), dtype=np.uint8)
    aug = np.vstack([Nmat, t[None, :]])
    e0 = next((np.array(v[:r], dtype=np.uint8) for v in wslib.gf2_kernel(aug.T) if v[r]), None)
    if e0 is None:
        print(f"no S-unit has norm in {args.norm_class} Q*^2 (enlarge S)")
        return 1
    # rational classes -1 and p in S, as elements of K, at the same primes
    R = np.array([[0 if pari.kronecker(a, q) == 1 else 1 for q in prs] for a in [-1] + Sprimes], dtype=np.uint8)
    rankR = wslib.gf2_rank(R)
    print(f"  norm-square subspace of dimension {len(ker)}; rational classes span {rankR}", flush=True)

    stats, seen = {}, set()
    for e in wslib.span_combinations([np.array(v, dtype=np.uint8) for v in ker], r, args.max, rng):
        e = (e + e0) % 2
        key = e.tobytes()
        if key in seen or not e.any():
            continue
        seen.add(key)
        vec = (e @ L) % 2
        if wslib.gf2_rank(np.vstack([R, vec])) == rankR:      # delta in Q* K*^2
            continue
        delta = wslib.product_of(gens, e, Ky)
        M = wslib.quadratic_extension(Ky, delta, reduce=False)
        if M is None:
            continue
        top = wslib.identify(M, args.order, 300)
        if not top:
            stats['other'] = stats.get('other', 0) + 1
            continue
        k = top[0][1]
        stats[k] = stats.get(k, 0) + 1
        if len(seen) % 200 == 0:
            print(f"    ... {len(seen)} classes, {time.time()-t0:.0f}s, stats {stats}", flush=True)
        if k not in targets:
            continue
        M = pari.polredbest(M)
        top = wslib.identify(M, args.order, 3000)
        if top[0][1] not in targets:
            continue
        margin = top[0][0] - top[1][0] if len(top) > 1 else float('inf')
        print(f"FOUND {M}\n  coeffs {list(map(int, pari.Vecrev(M)))}\n"
              f"  best match {2*n}T{top[0][1]}, log-likelihood margin {margin:.0f}; {time.time()-t0:.0f}s; "
              f"stats {stats}", flush=True)
        return 0
    print(f"NOT FOUND; best-match groups seen: {stats}")
    return 1


if __name__ == '__main__':
    sys.exit(main())
