#!/usr/bin/env python3
"""Residual witnesses of the form K8(sqrt delta), K8 = L(sqrt q), L a quartic.

Covers the residuals with an S4 or A4 block quotient (20T782/785/789,
20T879/884).  If the residual H acts on 16 points with blocks of size 2 whose
kernel is elementary abelian of rank r, and the block action is the action of
Gal(L~(sqrt q)/Q) on the 8 embeddings of K8, then the H-field is the closure
of K8(sqrt delta) for delta whose 8 conjugates span an r-dimensional space
modulo squares in the closure of K8.  Closure order = |Gal(K8~/Q)| * 2^r.

PARI's galoisinit cannot handle these groups, so candidates are identified by
Frobenius cycle-type statistics against tables/cycle_types_deg16.txt, and the
subgroup fixing sqrt(q) by statistics over primes split in Q(sqrt q).  This
is only a filter: magma/verify_witnesses_disc.m proves the group.

Modes
  default      enumerate delta (all S-unit classes if few, else a random
               sample) and keep those with conjugate rank --rank.
  --linear     (K8 = L(sqrt q), Gal = S4 x C2 untwisted, rank 3 only) impose
               the unique 5-dimensional submodule Z of the 8-point
               permutation module as linear conditions, so large S is cheap.

Local conditions matter more than S.  For 20T879/884 the Frobenius of L at 5
must have cycle type (1,1,1,1), (1,1,2) or (1,3) (gap/local_lift.g);
x^4-x-1 fails, x^4-x+1 works.

Examples
  20T782/785:  --L "x^4-14*x^2-20*x-5" --S 2,5,17 --rank 3 --order 192 --targets 441,443,446
  20T789:      --L "x^4+8*x+12"        --S 2,3,5    --rank 3 --order 192 --targets 426,428
  20T879/884:  --L "x^4-x+1" --S 2,3,5,7,11,229 --linear --order 384 \\
               --targets "749:192,1493;759:192,1493;740:192,1494"
"""
import argparse
import random
import sys
import time

import wslib
from wslib import pari

# The unique 5-dim submodule of F2[(S4 x C2)/S3] (points labelled 2*i + s,
# i = root of L, s = sign of sqrt q); delta in its annihilator <=> rank 3.
Z_S4xC2 = [[1, 0, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 0, 1, 1, 0, 0, 0, 0],
           [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1]]


def parse_targets(text):
    """'426,428' or '749:192,1493;740:192,1494' -> {k: required sub-id or None}."""
    out = {}
    for part in text.split(';'):
        if ':' in part:
            k, sub = part.split(':')
            out[int(k)] = tuple(int(t) for t in sub.split(','))
        else:
            for k in part.split(','):
                out[int(k)] = None
    return out


def labels_for(K8, a_expr, b_expr, Lpol, q, P):
    """Label each embedding K8 -> P by (index of the image of L's root, sign of sqrt q)."""
    Py = pari.subst(P, 'x', 'y')
    Lroots = [pari.subst(pari.lift(r), 'y', 'x') for r in pari.nfroots(Py, Lpol)]
    sroots = [pari.subst(pari.lift(r), 'y', 'x') for r in pari.nfroots(Py, pari(f'x^2-({q})'))]
    labels = []
    for e in pari.nfisincl(K8, P):
        ia = pari.lift(pari.Mod(pari.subst(pari.lift(a_expr), 'x', e), P))
        ib = pari.lift(pari.Mod(pari.subst(pari.lift(b_expr), 'x', e), P))
        labels.append(2 * Lroots.index(ia) + sroots.index(ib))
    return labels


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--L', required=True)
    ap.add_argument('--q', type=int, default=5)
    ap.add_argument('--twist', action='store_true', help='use K8 = L(sqrt(q*disc L)) instead of L(sqrt q)')
    ap.add_argument('--S', required=True)
    ap.add_argument('--rank', type=int, default=3)
    ap.add_argument('--order', type=int, required=True, help='order of H (for the statistical filter)')
    ap.add_argument('--targets', required=True, help='16Tk targets, optionally with the required sqrt(q)-subgroup id')
    ap.add_argument('--linear', action='store_true')
    ap.add_argument('--max', type=int, default=2**16, help='max classes enumerated (random sample beyond this)')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()

    Lpol = pari(args.L)
    Sprimes = [int(t) for t in args.S.split(',')]
    targets = parse_targets(args.targets)
    rng = random.Random(args.seed)
    t0 = time.time()

    qq = args.q * int(pari.core(pari.poldisc(Lpol))) if args.twist else args.q
    comp = pari.polcompositum(Lpol, pari(f'x^2-({qq})'), 1)[0]
    K8, a_expr, b_expr = comp[0], comp[1], comp[2]
    P = pari.polredbest(pari.nfsplitting(K8))
    cd = wslib.ConjugateData(K8, P, Sprimes, nprimes=12 if args.linear else 20)
    print(f"K8 = {K8}; closure degree {pari.poldegree(P)}; {len(cd.gens)} generators; "
          f"{time.time()-t0:.0f}s", flush=True)

    if args.linear:
        if args.twist or args.rank != 3:
            sys.exit("--linear is implemented for K8 = L(sqrt q), rank 3")
        basis = cd.classes_killed_by(Z_S4xC2, labels_for(K8, a_expr, b_expr, Lpol, qq, P))
    else:
        basis = [row for row in __import__('numpy').eye(len(cd.gens), dtype='uint8')]
    print(f"search space dimension {len(basis)}", flush=True)

    stats = {}
    for e in wslib.span_combinations(basis, len(cd.gens), args.max, rng):
        if cd.conjugate_rank(e) != args.rank:
            continue
        M = wslib.quadratic_extension(cd.Ky, cd.element(e))
        if M is None:
            continue
        top = wslib.identify(M, args.order, 400)
        if not top:
            continue
        k = top[0][1]
        stats[k] = stats.get(k, 0) + 1
        if k not in targets:
            continue
        need = targets[k]
        if need is not None:
            sub = wslib.quadratic_subgroup(M, k, args.q, 800)
            if sub[0][0] is None or tuple(sub[0][1]) != need:
                continue
        M = pari.polredabs(M)
        top = wslib.identify(M, args.order, 2500)
        margin = top[0][0] - top[1][0] if len(top) > 1 else float('inf')
        print(f"FOUND {M}\n  coeffs {list(map(int, pari.Vecrev(M)))}\n"
              f"  best match 16T{top[0][1]} = {top[0][2]}, log-likelihood margin {margin:.0f}; "
              f"{time.time()-t0:.0f}s", flush=True)
        return 0
    print("NOT FOUND; best-match groups seen:", stats)
    return 1


if __name__ == '__main__':
    sys.exit(main())
