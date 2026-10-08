#!/usr/bin/env python3
"""Residual witnesses K(sqrt delta) over a fixed field K of a Galois field P.

Generalises search_octic_kummer.py.  P is built as the Galois closure of
--base (e.g. an A4 quartic) composed with the quadratic fields --quad
(e.g. "5" or "5,-1").  For every core-free subgroup U of Gal(P/Q) of order
--sub-order, up to isomorphism of fixed fields, K = P^U is used as the base:
delta runs over S-units of K (all classes if few, else a random sample) with
conjugate rank --rank modulo squares in P, and K(sqrt delta) is identified by
Frobenius cycle-type statistics against tables/cycle_types_deg<n>.txt, then
the subgroup fixing sqrt(q) against tables/index2_subgroups_deg<n>.txt.

Written for the degree-30 O_5 family (Oct 2026): H = G/O_5(G) has a faithful
24-point representation with 2-blocks, elementary block kernel C2^3, and
block quotient C2 x A4 (12T6/7) or C2^2 x A4 (12T25/26); so K has degree 12
and P = (A4 closure)(sqrt 5) or (A4 closure)(sqrt 5, sqrt c).

Statistics can tie (degree 24, order 192: 24T298/301/308 and
24T299/305/309/310/312).  With --exact-kummer every statistical hit in the
twin class of a target is decided exactly: the Galois group is computed from
the Kummer data (wslib.kummer_galois_group: lifts of Gal(P/Q) to
P(sqrt delta_1, ..., sqrt delta_n), with the relations among the delta_i
certified as squares in P) and identified with GAP (IdGroup of H and of the
subgroup fixing sqrt q).  PARI galoisinit cannot handle these closures.

Real place first: for 24T894/908 complex conjugation must act trivially on
the A4 part, so the A4 quartic must be totally real; x^4+8*x+12 fails.

Example (30T2848, H = [384,5776] = 24T898, H0 = [192,194]):
  python3 search_kummer_fixed_field.py --base "x^4+8*x+12" --quad 5,-1 \
      --sub-order 4 --rank 3 --order 384 --targets "898:192,194;904:192,194"

Example (30T2778/2843, H = [384,5765] = 24T894/908, H0 = [192,197]):
  python3 search_kummer_fixed_field.py --base "x^4+8*x+12" --quad 5,-1 \\
      --sub-order 4 --rank 3 --order 384 --targets "894:192,197;908:192,197"
"""
import argparse
import random
import sys
import time

import numpy as np

import wslib
from wslib import pari
from search_octic_kummer import parse_targets


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--base', required=True, help='polynomial whose Galois closure is the base of P (e.g. an A4 quartic)')
    ap.add_argument('--quad', required=True, help='comma-separated squarefree integers c; P = closure(base)(sqrt c, ...)')
    ap.add_argument('--q', type=int, default=5, help='the quadratic field F = Q(sqrt q) (default 5)')
    ap.add_argument('--sub-order', type=int, required=True, help='order of the core-free subgroup U; deg K = [P:Q]/order')
    ap.add_argument('--S', default='2,3,5', help='primes always in S; primes dividing disc K are added')
    ap.add_argument('--rank', type=int, required=True)
    ap.add_argument('--order', type=int, required=True, help='order of H')
    ap.add_argument('--targets', required=True, help='nTk targets with required sqrt(q)-subgroup ids, e.g. "894:192,197"')
    ap.add_argument('--max', type=int, default=20000, help='classes sampled per base field (or per submodule with --linear)')
    ap.add_argument('--exact-kummer', action='store_true',
                    help='confirm each statistical hit by computing the Galois group exactly from the Kummer '
                         'data (wslib.kummer_galois_group + GAP IdGroup); needed when the statistics tie')
    ap.add_argument('--exact-skip', type=int, default=0,
                    help='with --exact-kummer: after this many consecutive exact rejections move on to the next '
                         'submodule / base (the group tends to be constant on each); 0 = never')
    ap.add_argument('--linear', action='store_true',
                    help='make the rank condition linear: for each r-dimensional submodule N of the permutation '
                         'module on the conjugates of K, search the classes killed by N^perp')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()

    targets = parse_targets(args.targets)
    rng = random.Random(args.seed)
    t0 = time.time()

    P = pari.nfsplitting(pari(args.base))
    for c in args.quad.split(','):
        P = pari.polcompositum(P, pari(f'x^2-({int(c)})'))[0]
    P = pari.polredbest(P)
    n = int(pari.poldegree(P))
    gal = pari.galoisinit(P)
    auts = [pari.galoispermtopol(gal, g) for g in pari('(g)->g.group')(gal)]
    print(f"P of degree {n}, group {list(map(int, pari.galoisidentify(gal)))}; {time.time()-t0:.0f}s", flush=True)

    bases = []
    for U in pari.galoissubgroups(gal):
        if int(pari('(H)->vecprod(Vec(H[2]))')(U)) != args.sub_order:
            continue
        K = pari.polredbest(pari.galoisfixedfield(gal, U, 1))
        if int(pari.poldegree(pari.nfsplitting(K))) != n:     # U not core-free
            continue
        if any(pari.nfisisom(K, K0) for K0 in bases):
            continue
        bases.append(K)
    print(f"{len(bases)} base fields K of degree {n // args.sub_order}", flush=True)

    # exact mode: accept (IdGroup(H), IdGroup(H0)) of any target; gate on targets and their statistical twins
    deg = 2 * n // args.sub_order
    gid_of = {kk: gid for kk, sz, gid, dist in wslib.tables(deg)[0]}
    dist_of = {kk: dist for kk, sz, gid, dist in wslib.tables(deg)[0]}
    accept = {(gid_of[k], need) for k, need in targets.items()}
    gate = {kk for kk in dist_of for k in targets if dist_of[kk] == dist_of[k]}

    def parse_result(res):
        # "RESULT 192 [ 192, 199 ] 312 2 [ 96, 3 ]"
        if res is None:
            return None
        import re
        ids = re.findall(r'\[\s*(\d+),\s*(\d+)\s*\]', res)
        if len(ids) != 2:
            return None
        return (tuple(map(int, ids[0])), tuple(map(int, ids[1])))

    base_S = {int(t) for t in args.S.split(',')}
    for K in bases:
        Sprimes = sorted(base_S | {int(p) for p in pari.factor(abs(int(pari.nfdisc(K))))[0]})
        cd = wslib.ConjugateData(K, P, Sprimes, nprimes=12)
        r = len(cd.gens)
        print(f"K = {K}: {r} S-unit generators; {time.time()-t0:.0f}s", flush=True)
        if args.linear:
            perms = wslib.embedding_permutations(K, P, cd.embs, auts)
            nK = len(perms[0])
            subs = wslib.submodules_of_dim(perms, nK, args.rank)
            bases_e = [cd.classes_killed_by(wslib.orthogonal_complement_basis(N, nK), list(range(nK)))
                       for N in subs]
            print(f"  {len(subs)} submodules of dimension {args.rank}; search dimensions "
                  f"{[len(b) for b in bases_e]}", flush=True)
        else:
            bases_e = [[row for row in np.eye(r, dtype=np.uint8)]]
        stats, seen = {}, set()
        streak = [0]
        def candidates():
            for basis in bases_e:
                streak[0] = 0
                for e in wslib.span_combinations(basis, r, args.max, rng):
                    if args.exact_skip and streak[0] >= args.exact_skip:
                        print(f"  {streak[0]} exact rejections in a row: next submodule", flush=True)
                        break
                    yield e
        for e in candidates():
            if cd.conjugate_rank(e) != args.rank:
                continue
            key = e.tobytes()
            if key in seen:
                continue
            seen.add(key)
            M = wslib.quadratic_extension(cd.Ky, cd.element(e), reduce=False)
            if M is None:
                continue
            top = wslib.identify(M, args.order, 300)
            if not top:
                continue
            k = top[0][1]
            stats[k] = stats.get(k, 0) + 1
            if args.exact_kummer:
                # statistics cannot separate twins: gate on the twin class, decide exactly
                if k not in gate:
                    continue
                gens, chi, rk = wslib.kummer_galois_group(K, P, cd.element(e), args.q)
                res = wslib.gap_identify(gens, chi, 2 * len(cd.embs))
                print(f"  exact (Kummer): {res}", flush=True)
                parsed = parse_result(res)
                if parsed is None or (parsed[0], parsed[1]) not in accept:
                    stats['exact-reject'] = stats.get('exact-reject', 0) + 1
                    streak[0] += 1
                    continue
            else:
                if k not in targets:
                    continue
                need = targets[k]
                if need is not None:
                    sub = wslib.quadratic_subgroup(M, k, args.q, 800)
                    if sub[0][0] is None or tuple(sub[0][1]) != need:
                        continue
            M = pari.polredbest(M)
            top = wslib.identify(M, args.order, 2500)
            margin = top[0][0] - top[1][0] if len(top) > 1 else float('inf')
            print(f"FOUND {M}\n  coeffs {list(map(int, pari.Vecrev(M)))}\n"
                  f"  best match {n // args.sub_order * 2}T{top[0][1]} = {top[0][2]}, "
                  f"log-likelihood margin {margin:.0f}; {time.time()-t0:.0f}s", flush=True)
            if margin == 0 and not args.exact_kummer:
                print("  WARNING: margin 0 -- statistical twin; rerun with --exact-kummer", flush=True)
            if args.exact_kummer:
                print("  group confirmed exactly by Kummer theory", flush=True)
            return 0
        print(f"  not found over this K; best-match groups seen: {stats}", flush=True)
    print("NOT FOUND")
    return 1


if __name__ == '__main__':
    sys.exit(main())
