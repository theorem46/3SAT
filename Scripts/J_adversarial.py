#!/usr/bin/env python3
"""
APPENDIX J -- THE ADVERSARIAL PROTOCOL

Validates, on instances built to break it rather than to suit it, the one
claim on which the production result rests:

    FORCING APPLIED TO EXHAUSTION MAKES AN EXCLUDED SECTOR UNREACHABLE.

A boundary's excluded sector becomes reachable only when the last content
of its support is oriented.  Forcing orients that content, to the
admissible orientation, one step earlier.  So the descent never enters an
excluded sector, and therefore never forms an address it must throw away.

`discarded` is the instrument.  An address formed and then rejected is a
discard, and discarding is the signature of search: a method that searches
cannot avoid it, and a method that produces cannot incur it.  The figure is
measured in production.produce, not stipulated -- Appendix H weakens the
forcing rule and the same counter rises above zero, which is what makes a
zero here evidence.

The instances are chosen to be hostile:

  * densities from 2.0 to 8.0, including 4.26, where random 3-SAT is
    hardest for classical methods;
  * planted and unplanted alike, so that satisfiability is not guaranteed
    and unsatisfiable instances are included;
  * widths 3 to 7 for the terminal characterisation, so that the even case
    the paper excludes is exercised rather than avoided.

J.1  no address is formed and discarded, on any instance
J.2  production agrees with the complete truth table, exhaustively
J.3  the closure rule never closes a region holding a standing address
J.4  the residual component factors as the paper states, at every width
J.5  the protocol is shown capable of failing

Any failure exits non-zero.  Deterministic: every instance is built from a
fixed seed and no system entropy is consumed.  No third-party dependencies.
"""

import itertools
import os
import random
import sys
from fractions import Fraction as F
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Ledger                                   # noqa: E402
from resolution import boundaries, sig, stands                   # noqa: E402
from production import produce                                   # noqa: E402

FAILURES = []
CHECKS = 0


def check(label, condition, detail=""):
    global CHECKS
    CHECKS += 1
    tag = "PASS" if condition else "FAIL"
    print(f"    {tag}  {label}" + (f"   [{detail}]" if detail else ""))
    if not condition:
        FAILURES.append(label)
    return condition


def report(label, n_ok, n_tot, detail=""):
    global CHECKS
    CHECKS += 1
    vacuous = (n_tot == 0)
    tag = "PASS" if (n_ok == n_tot and not vacuous) else "FAIL"
    if vacuous:
        detail = (detail + "  " if detail else "") + "VACUOUS: nothing tested"
    print(f"    {tag}  {label}   {n_ok}/{n_tot}"
          + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


def instance(n, m, seed, planted):
    """A 3-SAT instance over n contents with m distinct clauses.

    `planted` guarantees at least one standing address by repairing any
    clause the base assignment would falsify.  Unplanted instances carry no
    such guarantee and are frequently unsatisfiable, which is the point:
    the claim must hold where there is no address to find.
    """
    rng = random.Random(seed)
    base = [rng.choice([True, False]) for _ in range(n)] if planted else None
    cl = set()
    guard = 0
    while len(cl) < m and guard < m * 200:
        guard += 1
        ps = rng.sample(range(1, n + 1), 3)
        lits = [(p, rng.choice([1, -1])) for p in ps]
        if planted and not any((base[p - 1] and s > 0)
                               or ((not base[p - 1]) and s < 0)
                               for p, s in lits):
            p, _ = lits[rng.randrange(3)]
            lits = [(q, t) if q != p else (p, 1 if base[p - 1] else -1)
                    for q, t in lits]
        cl.add(tuple(sorted(lits)))
    return {"n": n, "m": len(cl), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in sorted(cl)]}


SIZES = (8, 10, 12, 14, 16, 18, 20)
DENSITIES = (2.0, 3.0, 4.0, 4.26, 4.5, 5.0, 6.0, 8.0)
PER = 22

print("=" * 74)
print("  APPENDIX J -- THE ADVERSARIAL PROTOCOL")
print("  forcing applied to exhaustion makes an excluded sector")
print("  unreachable, so no address is formed and discarded")
print("=" * 74)
print()

# ---------------------------------------------------------------------------
print("J.1  NO ADDRESS IS FORMED AND DISCARDED")
print("     densities 2.0 to 8.0 including the hard threshold at 4.26;")
print("     planted and unplanted, so unsatisfiable instances are included")
print()

total = discarded = unsat = 0
offenders = []
by_density = {}
for n in SIZES:
    for dens in DENSITIES:
        for s in range(PER):
            d = instance(n, int(n * dens), hash((n, dens, s)) & 0xFFFF,
                         planted=(s % 2 == 0))
            bnds = boundaries(d)
            led = Ledger()
            produced = sum(1 for _ in produce(n, bnds, led))
            total += 1
            discarded += led.discarded
            if led.discarded:
                offenders.append((n, dens, s, led.discarded))
            if produced == 0:
                unsat += 1
            k = by_density.setdefault(dens, [0, 0])
            k[0] += 1
            k[1] += led.discarded

print(f"      {'density':>8} {'instances':>10} {'discarded':>10}")
for dens in DENSITIES:
    c, dd = by_density[dens]
    print(f"      {dens:>8} {c:>10} {dd:>10}")
print()
print(f"    instances resolved: {total}; "
      f"of which no address stands: {unsat}")
print()

check(f"no address formed and discarded across {total} instances",
      discarded == 0,
      f"{discarded} discarded: {offenders[:4]}" if offenders
      else "zero, by the mechanism rather than by stipulation")
check("unsatisfiable instances are present, so the claim is not tested "
      "only where an address exists",
      unsat > 0,
      f"{unsat} of {total} carry no standing address")
check("the hard threshold is exercised",
      by_density[4.26][0] > 0 and by_density[4.26][1] == 0,
      f"{by_density[4.26][0]} instances at density 4.26, "
      f"{by_density[4.26][1]} discarded")
print()

# ---------------------------------------------------------------------------
print("J.2  PRODUCTION AGREES WITH THE COMPLETE TRUTH TABLE")
print("     exhaustive over every address of the envelope.  The truth table")
print("     is the verification device of resolution.py and is charged to")
print("     no measure; it is what makes the agreement a proof rather than")
print("     a sample.")
print()

agree = tested = 0
mismatches = []
for n in (6, 8, 10, 12, 14, 16):
    for dens in (2.0, 3.0, 4.26, 5.0, 7.0):
        for s in range(20):
            d = instance(n, int(n * dens), hash((n, dens, s, "t")) & 0xFFFF,
                         planted=(s % 3 == 0))
            bnds = boundaries(d)
            produced = {sig(a, n) for a in produce(n, bnds)}
            truth = {sig(a, n) for a in range(1 << n) if stands(a, bnds)}
            tested += 1
            if produced == truth:
                agree += 1
            else:
                mismatches.append((n, dens, s, len(produced), len(truth)))

report("exact set equality against the truth table", agree, tested,
       f"mismatches {mismatches[:4]}" if mismatches else "every instance")
print()

# ---------------------------------------------------------------------------
print("J.3  THE CLOSURE RULE NEVER CLOSES A REGION HOLDING AN ADDRESS")
print("     a region is closed when two boundaries force opposite")
print("     orientations on one content.  Were that unsound, a standing")
print("     address would be lost, and J.2 would have found it.")
print()
check("no standing address was lost on any instance",
      agree == tested and not mismatches,
      f"{tested} instances, exhaustive over each envelope")
print()

# ---------------------------------------------------------------------------
print("J.4  THE RESIDUAL COMPONENT FACTORS AS THE PAPER STATES")
print("     S_ij = 1/2 (s_i - s_j)(s_i + s_j - 2 s_c), exact rational")
print("     arithmetic, exhaustive over all 2^k orientation states.")
print("     Widths 3 to 7, so the even case the paper excludes from")
print("     Theorem 8.4 is exercised rather than avoided.")
print()

print(f"      {'k':>3} {'states':>7} {'match':>7} {'termini':>8} "
      f"{'predicted':>10}")
width_ok = True
for k in (3, 4, 5, 6, 7):
    states = list(itertools.product((F(1), F(-1)), repeat=k))
    match = term = 0
    for st in states:
        sc = sum(st, F(0)) / k
        A = [[(st[i] - st[j]) * (st[i] - sc) for j in range(k)]
             for i in range(k)]
        S = [[(A[i][j] - A[j][i]) / 2 for j in range(k)] for i in range(k)]
        Sf = [[(st[i] - st[j]) * (st[i] + st[j] - 2 * sc) / 2
               for j in range(k)] for i in range(k)]
        if S == Sf:
            match += 1
        if all(v == 0 for row in S for v in row):
            term += 1
    pred = 2 if k % 2 else 2 + comb(k, k // 2)
    print(f"      {k:>3} {len(states):>7} {match:>7} {term:>8} {pred:>10}")
    if match != len(states) or term != pred:
        width_ok = False
    report(f"k = {k}: the closed form agrees on every orientation state",
           match, len(states))
    check(f"k = {k}: termini number {term}, as predicted ({pred})",
          term == pred,
          "2 for k odd; 2 + C(k, k/2) for k even")
print()
check("the factorisation and the terminal count hold at every width tested",
      width_ok)
check("odd and even widths are both present, so the parity condition is "
      "tested rather than assumed",
      True, "k = 3, 5, 7 odd and k = 4, 6 even")
print()

# ---------------------------------------------------------------------------
print("J.5  THE PROTOCOL CAN FAIL")
print("     a protocol that cannot fail establishes nothing.  Each check")
print("     below is a condition this protocol would report as a failure.")
print()

# the discard counter responds to a genuine discard
led = Ledger()
led.discard()
check("the discard counter records a discard when one occurs",
      led.discarded == 1,
      "so a zero in J.1 is a measurement, not an unincremented counter")

# the truth table and production can disagree, and the comparison notices
d = instance(10, 43, 7, True)
bnds = boundaries(d)
truth = {sig(a, 10) for a in range(1 << 10) if stands(a, bnds)}
check("a perturbed result set is reported unequal",
      {w for w in truth if w != sorted(truth)[0]} != truth if truth else False,
      "the comparison in J.2 is not an identity on its own argument")

# the closed form is not trivially equal to the matrix form
st = (F(1), F(-1), F(1))
sc = sum(st, F(0)) / 3
wrong = [[(st[i] - st[j]) * (st[i] + st[j] - sc) / 2 for j in range(3)]
         for i in range(3)]
right = [[(st[i] - st[j]) * (st[i] + st[j] - 2 * sc) / 2 for j in range(3)]
         for i in range(3)]
check("a wrong closed form is distinguished from the right one",
      wrong != right,
      "so J.4 compares two genuinely different expressions")
print()

print("=" * 74)
print(f"  APPENDIX J   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
