#!/usr/bin/env python3
"""Binary octahedral (2O = [48,28]) fields with quadratic subfield Q(sqrt q).

Residual of 20T550: H = 2O, H0 = SL(2,3), F = Q(sqrt 5).  The H-field is
L~(sqrt delta) for an S4 quartic L with Q(sqrt disc L) = Q(sqrt q), and its
degree-16 subfield is K8(sqrt delta) with K8 = L(sqrt q) and delta in K8.

The script runs over S4 quartics with small coefficients, keeps those with
disc in q*Q^2 that are TOTALLY REAL (complex conjugation must map to the
centre of 2O, so it is trivial on L~), computes the classes delta in K8
whose 8 conjugates agree modulo squares in L~ (linear algebra), and decides
which central extension of S4 each gives from the orders of Frobenius
elements: in 2O both transpositions and double transpositions lift to
elements of order 4.  A hit is then confirmed with galoisidentify.

Example (finds 20T550 with L = x^4 - 14x^2 - 20x - 5):
  python3 search_binary_octahedral.py --q 5 --S-extra 2,3
  python3 search_binary_octahedral.py --L "x^4 - 14*x^2 - 20*x - 5"   (skips the quartic search)
"""
import argparse
import itertools
import math
import random
import sys
import time

import wslib
from wslib import pari


def s4_quartics(q, box, real):
    seen = {}
    for a, b, c, d in itertools.product((0, 1), range(-box, 1), range(-box, box + 1), range(-box, box + 1)):
        if d == 0:
            continue
        f = pari(f'x^4+{a}*x^3+{b}*x^2+{c}*x+{d}')
        if real and int(pari.polsturm(f)) != 4:
            continue
        if int(pari.core(pari.poldisc(f))) != q or not pari.polisirreducible(f):
            continue
        if int(pari.polgalois(f)[0]) != 24:
            continue
        g = pari.polredabs(f)
        seen.setdefault(str(g), int(pari.nfdisc(g)))
    return sorted(seen.items(), key=lambda t: abs(t[1]))


def lift_orders(Lpol, M, nprimes=40):
    """{quartic factorisation pattern of p: set of orders of Frob_p on roots of M}."""
    out, p, n, disc = {}, 2, 0, int(pari.poldisc(M))
    while n < nprimes:
        p = int(pari.nextprime(p + 1))
        if disc % p == 0:
            continue
        pat = tuple(sorted(int(pari.poldegree(f)) for f in pari.factormod(Lpol, p)[0]))
        o = 1
        for f in pari.factormod(M, p)[0]:
            o = math.lcm(o, int(pari.poldegree(f)))
        out.setdefault(pat, set()).add(o)
        n += 1
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--q', type=int, default=5)
    ap.add_argument('--L', default=None, help='use this S4 quartic instead of searching')
    ap.add_argument('--box', type=int, default=20, help='coefficient box for the quartic search')
    ap.add_argument('--S-extra', default='2,3', help='primes added to those dividing disc L')
    ap.add_argument('--fields', type=int, default=6, help='how many quartics to try')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    t0 = time.time()

    if args.L:
        quartics = [(args.L, int(pari.nfdisc(pari(args.L))))]
    else:
        quartics = s4_quartics(args.q, args.box, real=True)
    print(f"{len(quartics)} totally real S4 quartics with resolvent Q(sqrt {args.q}); {time.time()-t0:.0f}s", flush=True)
    for Lstr, disc in quartics[:args.fields]:
        Lpol = pari(Lstr)
        Sprimes = sorted({int(p) for p in pari.factor(abs(disc))[0]} | {int(t) for t in args.S_extra.split(',')})
        K8 = pari.polredbest(pari.polcompositum(Lpol, pari(f'x^2-({args.q})'))[0])
        P = pari.polredbest(pari.nfsplitting(Lpol))
        cd = wslib.ConjugateData(K8, P, Sprimes, nprimes=30)
        basis = cd.invariant_classes()
        print(f"L = {Lstr} (disc {disc}): invariant dimension {len(basis)}", flush=True)
        for e in wslib.span_combinations(basis, len(cd.gens), 512, rng):
            M = wslib.quadratic_extension(cd.Ky, cd.element(e))
            if M is None:
                continue
            lo = lift_orders(Lpol, M)
            if lo.get((1, 1, 2)) != {4} or lo.get((2, 2)) != {4}:
                continue
            M = pari.polredabs(M)
            S, gal, gid = wslib.closure_group(M)
            if gid == [48, 28] and wslib.contains_sqrt(S, args.q):
                print(f"FOUND {M}\n  coeffs {list(map(int, pari.Vecrev(M)))}\n"
                      f"  closure group {gid}; {time.time()-t0:.0f}s", flush=True)
                return 0
    print("NOT FOUND")
    return 1


if __name__ == '__main__':
    sys.exit(main())
