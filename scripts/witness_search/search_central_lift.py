#!/usr/bin/env python3
"""Residual witnesses needing a central C2 step on top of a Kummer step.

For residuals H whose derived subgroup is not elementary abelian (20T612:
H = [64,35], [H,H] = C4 x C2), peel off the unique central C2 = Z(H) and work
in two steps:

  step 1  find H1 = H/Z(H) fields E(sqrt W) over E = L(sqrt q), exactly as in
          search_abelian_base.py;
  step 2  for each step-1 field, take its octic subfields K on which Gal acts
          faithfully, compute the classes delta in K whose conjugates are all
          equal modulo squares in the closure (linear algebra), and test
          K(sqrt delta), whose closure is a central C2 extension of H1.

Which central extensions occur in step 2 depends on the local behaviour of
the step-1 field, not on S.  For 20T612 all complex step-1 fields gave only
[64,23] / [64,90]; requiring the step-1 field to be totally real (complex
conjugation must lift to an involution of H) gave [64,35] at once.  Hence
--totally-real.

Example (finds 20T612; step 1 then tries step-1 fields in turn):
  python3 search_central_lift.py --L "x^4 - x^3 - 54*x^2 + 9*x + 81" \
      --S 2,3,5,29 --step1-dim 2 --step1-group 32,6 --step1-sub 16,3 \
      --group 64,35 --sub 32,6 --totally-real --fixed-order 4

Being totally real is necessary but not sufficient: expect several step-1
fields to give only other central extensions before one works (each costs
a couple of minutes).  To lift the step-1 field that worked for 20T612:
  python3 search_central_lift.py --S2 2,3,5,29 --group 64,35 --sub 32,6 \
      --step1-field "x^16 - 108*x^14 + 3683*x^12 - 42336*x^10 + 195085*x^8 - 336366*x^6 + 179568*x^4 - 33048*x^2 + 1296" \
      --step1-dim 2 --step1-group 32,6 --step1-sub 16,3 --octics 4 --lifts 64
"""
import argparse
import random
import sys
import time

import numpy as np

import wslib
from wslib import pari


def ids(text):
    return [[int(t) for t in s.split(',')] for s in text.split(';')]


def lift(M1, args, want, wantsub, S2, rng, t0):
    """Step 2: central C2 lifts of the step-1 field M1 over its faithful octic subfields."""
    print(f"step-1 field {M1}  ({time.time()-t0:.0f}s)", flush=True)
    P, octs = wslib.octic_subfields(M1)
    groups = {}
    for Koct in octs[:args.octics]:
        cd = wslib.ConjugateData(Koct, P, S2, nprimes=15)
        for d in wslib.span_combinations(cd.invariant_classes(), len(cd.gens), args.lifts, rng):
            M = wslib.quadratic_extension(cd.Ky, cd.element(d))
            if M is None:
                continue
            try:
                S_, gal_, g2 = wslib.closure_group(M)
            except Exception:
                continue
            groups[tuple(g2)] = groups.get(tuple(g2), 0) + 1
            if g2 != want:
                continue
            sub = wslib.subgroup_fixing_sqrt(S_, gal_, args.q)
            if sub in wantsub and not (args.zeta and wslib.contains_zeta(S_, args.zeta)):
                M = pari.polredabs(M)
                print(f"FOUND {M}\n  coeffs {list(map(int, pari.Vecrev(M)))}\n"
                      f"  group {g2}, Gal(K~/Q(sqrt {args.q})) = {sub}; {time.time()-t0:.0f}s", flush=True)
                return True
    print(f"  lifts seen: {groups}  ({time.time()-t0:.0f}s)", flush=True)
    return False


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--L', default=None)
    ap.add_argument('--step1-field', default=None,
                    help='skip step 1 and lift this H/Z(H) field (degree-16 polynomial)')
    ap.add_argument('--q', type=int, default=5)
    ap.add_argument('--S', default='2,3,5', help='primes for the step-1 S-units')
    ap.add_argument('--S2', default=None, help='primes for the step-2 S-units (default: --S)')
    ap.add_argument('--step1-dim', type=int, required=True)
    ap.add_argument('--step1-group', required=True)
    ap.add_argument('--step1-sub', required=True)
    ap.add_argument('--group', required=True)
    ap.add_argument('--sub', required=True)
    ap.add_argument('--totally-real', action='store_true', help='only use totally real step-1 fields')
    ap.add_argument('--fixed-order', type=int, default=0,
                    help='only use classes fixed by subgroups of Gal(E/Q) of this order (0 = all)')
    ap.add_argument('--zeta', type=int, default=5)
    ap.add_argument('--octics', type=int, default=2, help='octic subfields tried per step-1 field')
    ap.add_argument('--lifts', type=int, default=25, help='invariant classes tried per octic')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()

    S1 = [int(t) for t in args.S.split(',')]
    S2 = [int(t) for t in (args.S2 or args.S).split(',')]
    g1, sub1 = ids(args.step1_group)[0], ids(args.step1_sub)
    want, wantsub = ids(args.group)[0], ids(args.sub)
    rng = random.Random(args.seed)
    t0 = time.time()

    if args.step1_field:
        return 0 if lift(pari(args.step1_field), args, want, wantsub, S2, rng, t0) else 1
    E = pari.polredbest(pari.polcompositum(pari(args.L), pari(f'x^2-({args.q})'))[0])
    base = wslib.GaloisBase(E, S1)
    seen = set()
    for K in base.subgroups():
        if len(K) == base.n or (args.fixed_order and len(K) != args.fixed_order):
            continue
        for e in wslib.span_combinations(base.fixed_space(sorted(K)), len(base.gens), 4000, rng):
            dim, V = base.orbit_span(e)
            if dim != args.step1_dim:
                continue
            key = frozenset(np.packbits(row).tobytes() for row in V)
            if key in seen:
                continue
            seen.add(key)
            M1 = wslib.quadratic_extension(base.Ey, base.element(e))
            if M1 is None:
                continue
            S, gal, gid = wslib.closure_group(M1)
            if gid != g1 or wslib.subgroup_fixing_sqrt(S, gal, args.q) not in sub1:
                continue
            if args.zeta and wslib.contains_zeta(S, args.zeta):
                continue
            if args.totally_real and int(pari.polsturm(M1)) != int(pari.poldegree(M1)):
                continue
            if lift(M1, args, want, wantsub, S2, rng, t0):
                return 0
    print("NOT FOUND")
    return 1


if __name__ == '__main__':
    sys.exit(main())
