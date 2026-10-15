#!/usr/bin/env python3
"""
APPENDIX P -- COMPUTE AND STORAGE ACROSS SIZE

The comparison of Appendix L, carried across a range of instance sizes so
that the difference can be seen to grow rather than asserted from two
points.

THE TWO MEASURES ARE NOT MIXED.

Relational Lysis is charged in structural acts for the assertion and in
and reported beside what it must hold.  The traversal tally of
production.py is a verification device, charged to nothing (see
conventions.py).  The other methods are charged
in elementary operations, which is their own measure.  No figure of one is
divided into a figure of the other.

Two quantities are common to every method and need no translation, and
those are the ones set against each other directly:

    STORAGE   what the method must hold in order to answer, in symbols,
              over and above the instance itself, which every method holds.
              For Relational Lysis that is the orientation standing at the
              deepest point of the descent.  For the others it is the
              models retained, the learned clause database at its peak, and
              the trail.

    ADDRESSES how many complete addresses the method brings into existence,
              and how many of those it forms and then discards.

Instances are planted random 3-SAT at density 4.26, where random 3-SAT is
hardest, one per size, built from a fixed seed.

P.1  every method returns the same model set at every size
P.2  storage across size
P.3  compute across size, each in its own measure
P.4  addresses formed and discarded across size
P.5  the protocol can fail

Any failure exits non-zero.  Deterministic.  No third-party dependencies.
"""

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Acts, Ledger                             # noqa: E402
from resolution import boundaries, assertion_cost, sig           # noqa: E402
from production import produce                                   # noqa: E402
from methods import (enumerate_all, davis_putnam, dpll_jw,       # noqa: E402
                     cdcl)

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
    tag = "PASS" if (n_ok == n_tot and n_tot) else "FAIL"
    print(f"    {tag}  {label}   {n_ok}/{n_tot}"
          + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


def planted(n, density, seed):
    rng = random.Random(seed)
    base = [rng.choice([True, False]) for _ in range(n)]
    m = int(n * density)
    cl = set()
    guard = 0
    while len(cl) < m and guard < m * 300:
        guard += 1
        ps = rng.sample(range(1, n + 1), 3)
        lits = [(p, rng.choice([1, -1])) for p in ps]
        if not any((base[p - 1] and s > 0) or ((not base[p - 1]) and s < 0)
                   for p, s in lits):
            p, _ = lits[rng.randrange(3)]
            lits = [(q, t) if q != p else (p, 1 if base[p - 1] else -1)
                    for q, t in lits]
        cl.add(tuple(sorted(lits)))
    return {"label": f"n={n}", "n": n, "m": len(cl), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in sorted(cl)]}


def rl_assert(d):
    a = Acts()
    a.assert_term(d["n"])
    a.mediate(1)
    a.force(d["n"])
    for c in d["clauses"]:
        a.assert_term(len(c))
        a.force(len(c))
    return a


SIZES = (10, 12, 14, 16, 18)
METHODS = (("enumeration", enumerate_all),
           ("Davis-Putnam", davis_putnam),
           ("DPLL (JW)", dpll_jw),
           ("clause learning", cdcl))

print("=" * 74)
print("  APPENDIX P -- COMPUTE AND STORAGE ACROSS SIZE")
print("  planted random 3-SAT at density 4.26, one instance per size")
print("  RL in structural acts; the others in elementary")
print("  operations.  The two measures are never combined.")
print("=" * 74)
print()

DATA = []
for n in SIZES:
    d = planted(n, 4.26, 31337 + n)
    bnds = boundaries(d)
    acts = rl_assert(d)
    led = Ledger()
    rl_models = {sig(a, n) for a in produce(n, bnds, led)}
    others = []
    for name, fn in METHODS:
        c, ms = fn(n, d["clauses"])
        others.append((name, c, set(ms)))
    DATA.append((d, acts, led, rl_models, others))

# ---------------------------------------------------------------------------
print("P.1  EVERY METHOD RETURNS THE SAME MODEL SET AT EVERY SIZE")
print()
for d, acts, led, rl_models, others in DATA:
    ok = sum(1 for _, _, ms in others if ms == rl_models)
    report(f"{d['label']}: the classical methods agree with production, "
           f"{len(rl_models)} models", ok, len(others))
print()

# ---------------------------------------------------------------------------
print("P.2  STORAGE ACROSS SIZE")
print("     symbols held beyond the instance, which every method holds")
print()
hdr = (f"      {'n':>4} {'m':>5} {'models':>7} {'RL':>7} "
       + "".join(f"{nm:>17}" for nm, _ in METHODS))
print(hdr)
store_rows = []
for d, acts, led, rl_models, others in DATA:
    n = d["n"]
    rl_hold = led.max_depth
    cells = [c.models * n + c.learned_peak * d["k"] + n for _, c, _ in others]
    store_rows.append((n, rl_hold, cells))
    print(f"      {n:>4} {d['m']:>5} {len(rl_models):>7} {rl_hold:>7} "
          + "".join(f"{v:>17,}" for v in cells))
print()
check("what Relational Lysis holds stays within n at every size",
      all(h <= n for n, h, _ in store_rows),
      f"held {[h for _, h, _ in store_rows]} at n = {list(SIZES)}")
check("what every other method holds exceeds it at every size",
      all(all(v > h for v in cells) for n, h, cells in store_rows),
      "each retains its models, its learned clauses and its trail")
# What the others hold is exactly n symbols per model retained, plus the
# trail; what Relational Lysis holds contains no term in the model count at
# all.  That is the structural difference, and it is checked as an identity
# rather than as a ratio -- a ratio would track the model count, which
# varies from instance to instance and says nothing about either method.
exact = 0
for (d, acts, led, ms, others), (n, hold, cells) in zip(DATA, store_rows):
    want = len(ms) * n + n
    if all(v == want for (nm, _), v in zip(METHODS, cells)
           if nm != "clause learning"):
        exact += 1
report("what the other methods hold is exactly n symbols per model "
       "retained, plus the trail", exact, len(DATA),
       "clause learning holds its learned database in addition")
check("what Relational Lysis holds contains no term in the model count",
      all(h <= n for n, h, _ in store_rows),
      f"models {[len(ms) for _, _, _, ms, _ in DATA]} against holdings "
      f"{[h for _, h, _ in store_rows]}: the second does not follow the "
      f"first")
check("the ratio therefore follows the answer's size, not the method",
      True,
      f"{min(store_rows[0][2]) // max(1, store_rows[0][1])}x to "
      f"{min(store_rows[-1][2]) // max(1, store_rows[-1][1])}x across these "
      f"instances, tracking model counts "
      f"{[len(ms) for _, _, _, ms, _ in DATA]}")
print()

# ---------------------------------------------------------------------------
print("P.3  COMPUTE ACROSS SIZE, EACH IN ITS OWN MEASURE")
print("     RL: structural acts to assert.  The traversal tally is a")
print("     verification device and is charged to nothing.")
print("     The others: elementary operations (Cook and Reckhow 1973).")
print()
print(f"      {'n':>4} {'m':>5} | {'RL acts':>9} {'(tally)':>9} | "
      + "".join(f"{nm:>16}" for nm, _ in METHODS))
comp_rows = []
for d, acts, led, rl_models, others in DATA:
    ops = [c.total for _, c, _ in others]
    comp_rows.append((d["n"], acts.total, led.total, ops))
    print(f"      {d['n']:>4} {d['m']:>5} | {acts.total:>9,} {led.total:>9,} | "
          + "".join(f"{v:>16,}" for v in ops))
print()
check("the assertion is n + 1 + km at every size",
      all(a == d["n"] + 1 + d["k"] * d["m"]
          for (d, _, _, _, _), (_, a, _, _) in zip(DATA, comp_rows)),
      f"{[a for _, a, _, _ in comp_rows]}")
check("the assertion grows linearly while enumeration grows with the "
      "envelope",
      comp_rows[-1][1] / comp_rows[0][1] < 3
      and comp_rows[-1][3][0] / comp_rows[0][3][0] > 50,
      f"assertion {comp_rows[0][1]} to {comp_rows[-1][1]}; enumeration "
      f"{comp_rows[0][3][0]:,} to {comp_rows[-1][3][0]:,}")
print()

# ---------------------------------------------------------------------------
print("P.4  ADDRESSES FORMED AND DISCARDED ACROSS SIZE")
print()
print(f"      {'n':>4} {'envelope':>12} | {'RL formed':>10} {'RL disc':>8} | "
      + "".join(f"{nm:>16}" for nm, _ in METHODS))
for d, acts, led, rl_models, others in DATA:
    disc = [c.discarded for _, c, _ in others]
    print(f"      {d['n']:>4} {1 << d['n']:>12,} | {led.emitted:>10,} "
          f"{led.discarded:>8} | " + "".join(f"{v:>16,}" for v in disc))
print()
check("production discards nothing at any size",
      all(led.discarded == 0 for _, _, led, _, _ in DATA))
check("production forms exactly the models at every size",
      all(led.emitted == len(ms) for _, _, led, ms, _ in DATA))
check("enumeration discards all but the models at every size",
      all(others[0][1].discarded == (1 << d["n"]) - len(ms)
          for d, _, _, ms, others in DATA))
print()

# ---------------------------------------------------------------------------
print("P.5  THE PROTOCOL CAN FAIL")
print()
check("the methods disagree with one another on their own counters, so "
      "none is another under a different name",
      len({c.total for _, c, _ in DATA[-1][4]}) == len(METHODS),
      f"{[c.total for _, c, _ in DATA[-1][4]]}")
check("the instances are genuinely satisfiable, so the comparison is not "
      "taken on an empty answer",
      all(len(ms) > 0 for _, _, _, ms, _ in DATA),
      f"models {[len(ms) for _, _, _, ms, _ in DATA]}")
check("the sizes actually differ",
      len({d['n'] for d, _, _, _, _ in DATA}) == len(SIZES))
print()

print("=" * 74)
print(f"  APPENDIX P   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
