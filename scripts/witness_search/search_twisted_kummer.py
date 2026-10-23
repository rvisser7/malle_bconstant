#!/usr/bin/env python3
"""Residual witnesses K(sqrt c)(sqrt(d * mu)): d in K, mu in Q(sqrt c).

For closures far too big for PARI galoisinit (A5, S5, A6, S6 sextics).  K has
degree n, K' = K(sqrt c) has degree 2n, and delta = d * mu with

  * d an S-unit of K with N_{K/Q}(d) in a * Q*^2 (a from --norm-class), d not
    in Q* K*^2, and
  * mu from a short list of elements of Q(sqrt c) (--mu, in the variable s
    with s^2 = c), e.g. mu = 1, s, or mu with N(mu) in c * Q*^2 so that
    Q(sqrt c, sqrt mu) is cyclic quartic.

Then the conjugates of delta span an (n-1)-dimensional quotient of the
permutation module, and the group of K'(sqrt delta) (degree 4n) is an
extension of Gal(K~(sqrt c)/Q) by C2^(n-1).  Which extension depends on a
and mu: for N(mu) in c Q*^2 the lift of Gal(Q(sqrt c)/Q) squares to the
central element (a C4 in O_2(H)), for mu = 1 the extension is a direct
product.  Exactly: L lies in the compositum of the closure of K(sqrt d) and
Q(sqrt c, sqrt mu), so Gal(L/Q) is a fibre product computed in
gap/twisted_fiber_groups.g (which also lists which (a, mu) gives which 24Tk).
The statistics only filter (24T7242/7243/7246 are exact twins).

Written for the A5/S5/A6/S6 leaves of the degree-30 O_5 family (Oct 2026),
e.g. 30T4064/4065: H = (C4 x C2^4) : A5 = 24T7243/7242, block quotient
C2 x A5 = 12T75, K an A5 sextic, c = 5.

Example (30T4064 -> 24T7243; --norm-class 5 gives 24T7242 for 30T4065):
  python3 search_twisted_kummer.py --base "x^6-2*x^5+3*x^4-4*x^2+4*x-3" --quad 5 \\
      --mu "(5+s)/2" --norm-class 1 --order 3840 --targets 7242,7243,7246 --per 10
"""
import argparse
import math
import random
import sys
import time

import numpy as np

import wslib
from wslib import pari
from search_norm_kummer import rational_vector


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--base', required=True, help='polynomial of K')
    ap.add_argument('--quad', type=int, required=True, help='c: K\' = K(sqrt c)')
    ap.add_argument('--mu', default='1', help='comma-separated elements of Q(sqrt c) in the variable s')
    ap.add_argument('--norm-class', default='1', help='comma-separated a: N_{K/Q}(d) in a Q*^2')
    ap.add_argument('--S', default='2,3,5', help='primes always in S; primes dividing disc K are added')
    ap.add_argument('--order', type=int, required=True)
    ap.add_argument('--targets', required=True, help='comma-separated transitive ids (degree 4 deg K)')
    ap.add_argument('--per', type=int, default=60, help='candidates per (a, mu) combination')
    ap.add_argument('--all', action='store_true', help='keep going after a target is found')
    ap.add_argument('--no-d-check', action='store_true', help='skip the check that K(sqrt d) has the full group')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    t0 = time.time()
    rng = random.Random(args.seed)
    targets = {int(t) for t in args.targets.split(',')}

    K = pari.polredabs(pari(args.base))
    n = int(pari.poldegree(K))
    Ky = pari.subst(K, 'x', 'y')
    Sprimes = sorted({int(t) for t in args.S.split(',')} | {int(p) for p in pari.factor(abs(int(pari.nfdisc(K))))[0]})
    gens = wslib.sunit_generators(Ky, Sprimes)
    r = len(gens)
    print(f"K = {K}, Galois {pari.polgalois(K) if n <= 11 else '?'}, disc {pari.factor(pari.nfdisc(K))}; "
          f"S = {Sprimes}; {r} S-unit generators", flush=True)

    # Legendre coordinates of the generators (and of rational S-units) at degree-1 primes of K
    cols, prs, p = [], [], 7
    while len(cols) < 4 * r + 40:
        p = int(pari.nextprime(p + 1))
        if p in Sprimes:
            continue
        for root in pari.lift(pari.polrootsmod(K, p)):
            try:
                vals = [int(pari.lift(pari.subst(pari.lift(g), 'y', pari.Mod(root, p)))) for g in gens]
            except Exception:
                continue
            if any(v == 0 for v in vals):
                continue
            cols.append([0 if pari.kronecker(v, p) == 1 else 1 for v in vals])
            prs.append(p)
    Lg = np.array(cols, dtype=np.uint8).T
    R = np.array([[0 if pari.kronecker(a, q) == 1 else 1 for q in prs] for a in [-1] + Sprimes], dtype=np.uint8)
    rankR = wslib.gf2_rank(R)
    Nmat = np.array([rational_vector(pari.norm(pari.Mod(g, Ky)), Sprimes) for g in gens], dtype=np.uint8)
    ker = [np.array(v, dtype=np.uint8) for v in wslib.gf2_kernel(Nmat.T)]

    # K' = K(sqrt c) and the images of K's generator and of sqrt c
    cmp = pari.polcompositum(K, pari(f'x^2-({args.quad})'), 1)[0]
    Kp, a_img, b_img = cmp[0], cmp[1], cmp[2]
    Kpy = pari.subst(Kp, 'x', 'y')
    nfKp = pari.nfinit(Kpy)
    a_y = pari.subst(pari.lift(a_img), 'x', 'y')
    b_y = pari.subst(pari.lift(b_img), 'x', 'y')
    mus = [pari(m.strip()) for m in args.mu.split(',')]

    # The fibre-product argument needs the conjugates of d to be as independent as the norm class
    # allows: Gal(K(sqrt d)) must have order 2^(n-1)|G| (N(d) in Q*^2 or disc Q*^2) or 2^n |G|.
    # A d in Q* eta K*^2 with K(sqrt eta) inside the closure of K collapses it (30T4064, Oct 2026:
    # the first witness had a group of order 240).  Checked by cycle-type likelihood over ALL
    # transitive groups of degree 2n (needs tables/cycle_types_deg<2n>.txt).
    G_order = int(pari.polgalois(K)[0]) if n <= 11 else None
    disc_class = int(pari.core(pari.nfdisc(K)))
    check_d = G_order is not None and not args.no_d_check
    if check_d:
        all_groups = wslib.tables(2 * n)[0]

    def d_part_ok(d, acls):
        Md = wslib.quadratic_extension(Ky, d, reduce=False)
        if Md is None:
            return False
        cnt = wslib.frobenius_cycle_types(Md, 600)
        best = max(((sum(m * math.log(dist[c]) for c, m in cnt.items()), sz)
                    for k_, sz, gid, dist in all_groups if all(c in dist for c in cnt)), default=None)
        sq = int(pari.core(acls)) in (1, disc_class)
        want = G_order * 2 ** (n - 1 if sq else n)
        return best is not None and best[1] == want

    found = set()
    for acls in [int(t) for t in args.norm_class.split(',')]:
        t = np.array(rational_vector(acls, Sprimes), dtype=np.uint8)
        e0 = next((np.array(v[:r], dtype=np.uint8) for v in wslib.gf2_kernel(np.vstack([Nmat, t[None, :]]).T) if v[r]), None)
        if e0 is None:
            print(f"  norm class {acls}: no S-unit (enlarge S)", flush=True)
            continue
        for mu, mtxt in zip(mus, args.mu.split(',')):
            mu_y = pari.Mod(pari.subst(pari.subst(mu, 's', b_y), 'x', 'y'), Kpy) if 's' in str(mu) else pari.Mod(mu, Kpy)
            stats, tries = {}, 0
            for e in wslib.span_combinations(ker, r, 10 * args.per, rng):
                e = (e + e0) % 2
                if wslib.gf2_rank(np.vstack([R, (e @ Lg) % 2])) == rankR:
                    continue
                tries += 1
                if tries > args.per:
                    break
                d = wslib.product_of(gens, e, Ky)
                if check_d and not d_part_ok(d, acls):
                    stats['d-degenerate'] = stats.get('d-degenerate', 0) + 1
                    continue
                delta = pari.lift(pari.subst(pari.lift(d), 'y', pari.Mod(a_y, Kpy)) * mu_y)
                M = pari('(nf,b)->rnfequation(nf, x^2 - b)')(nfKp, delta)
                if not pari.polisirreducible(M):
                    continue
                top = wslib.identify(M, args.order, 300)
                k = top[0][1] if top else 'other'
                stats[k] = stats.get(k, 0) + 1
                if k in targets and k not in found:
                    M = pari.polredbest(M)
                    top = wslib.identify(M, args.order, 3000)
                    if top and top[0][1] == k:
                        margin = top[0][0] - top[1][0] if len(top) > 1 else float('inf')
                        print(f"FOUND (norm class {acls}, mu = {mtxt.strip()}) {M}\n"
                              f"  coeffs {list(map(int, pari.Vecrev(M)))}\n"
                              f"  best match {4*n}T{k}, log-likelihood margin {margin:.0f}; {time.time()-t0:.0f}s", flush=True)
                        found.add(k)
                        if not args.all:
                            return 0
            print(f"  norm class {acls}, mu = {mtxt.strip()}: {stats}; {time.time()-t0:.0f}s", flush=True)
    print("FOUND targets " + ','.join(map(str, sorted(found))) if found else "NOT FOUND")
    return 0 if found else 1


if __name__ == '__main__':
    sys.exit(main())
