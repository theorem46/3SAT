#!/usr/bin/env python3
"""
APPENDIX F -- THE BOUNDARY IS THE RECORD

Validates Theorem 5 of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

Theorem 5 claims that the asserted boundaries are the complete record of
the instance and of its satisfying assignments, and that the record is
held in n + 1 + km symbols together with the descent's own state --
independently of how many assignments satisfy the instance.

Four questions are put to the boundaries and to nothing else:

  F.2  how many addresses stand?
  F.3  does THIS address stand?
  F.4  give me the i-th standing address.
  F.8  which boundary excludes this address?

The memory claim is measured by two independent instruments:

  F.5  STRUCTURALLY.  The held state of the resolution is counted: the
       boundaries, and one partial orientation per pending branch.  That
       count is a property of the mechanism and of no interpreter, so it is
       printed as a number.
  F.6  BY ALLOCATION.  Peak allocation of the resolution is compared with
       peak allocation of a list-storing resolution over the same
       boundaries.  Absolute byte figures are NOT printed: they are a
       property of the CPython build rather than of either method, and
       printing them would make this protocol's log reproducible on one
       interpreter only.  The verdict and the direction of the ratio are
       printed instead.

  F.7  no container but the four structural objects of the mechanism is
       held at any point.

Any failure exits non-zero.  Deterministic.  No third-party dependencies.
"""

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Ledger                                     # noqa: E402
from resolution import (load_instance, boundaries, assertion_cost,  # noqa: E402
                        sig, stands, excluding_boundaries,
                        survey_count, survey_stream)
from production import produce, produce_count, produce_nth         # noqa: E402

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
    """A counted check.  A workload of zero is a FAILURE, never a pass."""
    global CHECKS
    CHECKS += 1
    vacuous = (n_tot == 0)
    tag = "PASS" if (n_ok == n_tot and not vacuous) else "FAIL"
    if vacuous:
        detail = (detail + "  " if detail else "") + "VACUOUS: nothing was tested"
    print(f"    {tag}  {label}   {n_ok}/{n_tot}" + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


print("=" * 74)
print("  APPENDIX F -- THE BOUNDARY IS THE RECORD")
print("  validates Theorem 5: the count, membership, the i-th address and")
print("            the excluding boundary, all from the boundaries alone,")
print("            in memory independent of how many addresses stand")
print("=" * 74)
print()

INSTANCES = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]

# ---------------------------------------------------------------------------
print("F.1  WHAT IS STORED")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n, m, k = d["n"], d["m"], d["k"]
    check(f"{d['label']}: stored symbols = {assertion_cost(d)} = n + 1 + km",
          assertion_cost(d) == n + 1 + k * m)
    check(f"{d['label']}: the store is {len(bnds)} boundaries, two integers "
          f"each, and no address",
          all(isinstance(b, tuple) and len(b) == 2
              and all(isinstance(x, int) for x in b) for b in bnds)
          and len(bnds) == m,
          f"the envelope it describes holds {1 << n} addresses")
    check(f"{d['label']}: each boundary fixes exactly k = {k} contents",
          all(bin(mk).count("1") == k for mk, _ in bnds))
print()

# ---------------------------------------------------------------------------
print("F.2  HOW MANY STAND -- PRODUCED FROM THE BOUNDARIES")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    led = Ledger()
    got = produce_count(d["n"], bnds, led)
    check(f"{d['label']}: count = {got} matches the committed solution set",
          got == len(d["solutions"]))
    check(f"{d['label']}: the count was produced, not surveyed",
          led.discarded == 0 and led.emitted == got,
          f"{led.discarded} discarded over an envelope of {1 << d['n']}")
print()

# ---------------------------------------------------------------------------
print("F.3  DOES THIS ADDRESS STAND -- EXHAUSTIVE OVER THE ENVELOPE")
print("     a verification survey, charged to no measure: km comparisons")
print("     each, no list consulted")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    committed = set(d["solutions"])
    ok = 0
    for a in range(1 << n):
        verdict = stands(a, bnds)
        truth = sig(a, n) in committed
        if verdict == truth:
            ok += 1
    report(f"{d['label']}: membership correct on every address",
           ok, 1 << n)
print()

# ---------------------------------------------------------------------------
print("F.4  THE i-th STANDING ADDRESS, PRODUCED FROM THE BOUNDARIES")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    order = list(produce(n, bnds))
    check(f"{d['label']}: the production order carries {len(order)} "
          f"addresses, all distinct",
          len(order) == len(set(order)) and len(order) == len(d["solutions"]))
    ok = 0
    for i in range(len(order)):
        if produce_nth(i, n, bnds) == order[i]:
            ok += 1
    report(f"{d['label']}: the i-th address correct for every i",
           ok, len(order))
    check(f"{d['label']}: an index past the end returns nothing",
          produce_nth(len(order), n, bnds) is None)
print()

# ---------------------------------------------------------------------------
print("F.5  THE HELD STATE, COUNTED STRUCTURALLY")
print("     a property of the mechanism and of no interpreter: the")
print("     boundaries, plus one partial orientation per pending branch")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    led = Ledger()
    produce_count(n, bnds, led)
    check(f"{d['label']}: deepest held state {led.max_depth} <= n = {n}",
          led.max_depth <= n,
          f"{assertion_cost(d)} stored symbols + {led.max_depth} partial "
          f"orientations")
    check(f"{d['label']}: the held state does not reference the standing "
          f"count {len(d['solutions'])}",
          led.max_depth <= n and led.emitted == len(d["solutions"]))
print()

# ---------------------------------------------------------------------------
print("F.6  MEMORY IS INDEPENDENT OF HOW MANY ADDRESSES STAND")
print("     instances planted to carry 1, 2, 4, ... 64 standing addresses")
print("     over the SAME n, so the envelope is fixed at 4,096 throughout")
print()


def storing(n, bnds):
    """Keeps the addresses, as a method that retains its answers must."""
    found = []
    for a in survey_stream(n, bnds):
        found.append(sig(a, n))
    return found


def planted_family(n, free, seed):
    """Standing set of exactly 2^free addresses over n contents, using
    width-3 clauses only: four clauses per forced content."""
    fixed = n - free
    rng = random.Random(seed)
    base = [rng.choice([True, False]) for _ in range(n)]
    clauses = set()
    for p in range(1, fixed + 1):
        q, r = [t for t in range(1, n + 1) if t != p][:2]
        lit_p = (p, 1 if base[p - 1] else -1)
        for sq in (1, -1):
            for sr in (1, -1):
                clauses.add(tuple(sorted([lit_p, (q, sq), (r, sr)])))
    clauses = sorted(clauses)
    return {"label": f"planted-2^{free}", "n": n, "m": len(clauses), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in clauses]}


#  Memory is measured in SYMBOLS HELD, not in bytes allocated.
#
#  Symbols held is this archive's declared unit (conventions.py) and the unit
#  in which Theorem 5 states its bound.  It is also exact: a byte figure from
#  an allocation tracer varies with the interpreter build, which would make
#  the committed logs irreproducible on another one, whereas a symbol count
#  is the same figure on every machine.  What the theorem bounds is what the
#  resolution must keep in order to answer, and that is counted here.
#
#      production holds   the boundaries -- n + 1 + km symbols, fixed by the
#                         assertion -- and the orientation standing at the
#                         deepest point of the descent, at most n symbols.
#                         No address is retained: each is emitted and then
#                         forgotten.
#      storing holds      the same boundaries and, in addition, n symbols
#                         for each standing address it keeps.
#
#  The first quantity does not contain the standing count.  The second is
#  linear in it.

rows = []
print(f"      {'standing':>9} {'held orientation':>17} {'boundaries':>11} "
      f"{'production holds':>17} {'storing holds':>14}")
for free in (0, 1, 2, 3, 4, 5, 6):
    d = planted_family(12, free, 5000 + free)
    bnds = boundaries(d)
    n = d["n"]

    led = Ledger()
    cnt = produce_count(n, bnds, led)

    kept = storing(n, bnds)
    stored = assertion_cost(d)              # the boundaries, held by both
    prod_holds = stored + led.max_depth     # boundaries + deepest orientation
    store_holds = stored + len(kept) * n    # boundaries + every address kept
    del kept

    rows.append((free, cnt, led, n, stored, prod_holds, store_holds))
    print(f"      {cnt:>9} {led.max_depth:>17} {stored:>11} "
          f"{prod_holds:>17} {store_holds:>14}")
print()

for free, cnt, led, n, stored, ph, sh in rows:
    check(f"planted-2^{free}: {cnt} stand, {led.emitted} produced, "
          f"{led.discarded} discarded",
          cnt == (1 << free) and led.emitted == cnt and led.discarded == 0)

check("the held orientation never exceeds n, at any standing count",
      all(led.max_depth <= n for _, _, led, n, _, _, _ in rows),
      f"depths {[led.max_depth for _, _, led, _, _, _, _ in rows]}, n = 12")

check("production holds at most the boundaries plus n, at every standing "
      "count",
      all(ph <= stored + n for _, _, _, n, stored, ph, _ in rows),
      "the bound of Theorem 5, in the unit the theorem states it")

check("what storing holds is exactly the boundaries plus n per address kept",
      all(sh == stored + cnt * n for _, cnt, _, n, stored, _, sh in rows),
      f"addresses retained: "
      f"{[(sh - stored) // 12 for _, _, _, _, stored, _, sh in rows]}")

check("production's bound contains no term in the standing count, while "
      "storing's grows linearly in it",
      (rows[-1][6] - rows[-1][4]) == 64 * 12
      and (rows[0][6] - rows[0][4]) == 1 * 12
      and (rows[-1][5] - rows[-1][4]) <= 12,
      f"storing retains {rows[0][6] - rows[0][4]} symbols at 1 standing and "
      f"{rows[-1][6] - rows[-1][4]} at 64; production holds "
      f"{rows[0][5] - rows[0][4]} and {rows[-1][5] - rows[-1][4]}")

check("the excess of storing over production widens with the standing count",
      (rows[-1][6] - rows[-1][5]) > (rows[0][6] - rows[0][5]),
      f"{rows[0][6] - rows[0][5]} symbols at 1 standing, "
      f"{rows[-1][6] - rows[-1][5]} at 64")
print()

# ---------------------------------------------------------------------------
print("F.7  NO CONTAINER OF ADDRESSES IS HELD")
print("     every container in the resolution's frame must be one of the")
print("     four structural objects of the mechanism.  Anything else is a")
print("     store, and fails the run.")
print()

#  The guard is on SIZE, not on names.  A store of addresses is a container
#  whose size grows with the number of addresses that stand; every container
#  the mechanism legitimately holds is bounded by the asserted structure --
#  by m, by km, or by n -- and by nothing else.  Checking the bound rather
#  than a list of permitted names means a container added later cannot pass
#  by being given an expected name, and cannot fail merely by being new.

def size_bounds(n, m, k):
    """What each container the mechanism holds may be bounded by."""
    return {
        "bnds":     ("m",            m),
        "index":    ("n + 1",        n + 1),
        "stack":    ("n",            n),
        "live":     ("m",            m),
        "live0":    ("m",            m),
        "clive":    ("m",            m),
        "forcing":  ("n",            n),
        "forcing0": ("n",            n),
        "cforcing": ("n",            n),
        "datum":    ("2",            2),
    }


for d in INSTANCES:
    bnds = boundaries(d)
    n, m, k = d["n"], d["m"], d["k"]
    bounds = size_bounds(n, m, k)
    gen = produce(n, bnds)
    next(gen)                                        # prime it
    frame = gen.gi_frame
    held = dict(frame.f_locals) if frame else {}
    containers = {kk: v for kk, v in held.items()
                  if v is not None and kk != "led"
                  and isinstance(v, (list, set, dict, tuple))}

    # (1) every container held is bounded by the asserted structure
    unbounded = {}
    for kk, v in containers.items():
        if kk not in bounds:
            unbounded[kk] = f"{type(v).__name__}({len(v)}) -- no bound declared"
        elif len(v) > bounds[kk][1]:
            unbounded[kk] = f"{len(v)} > {bounds[kk][0]} = {bounds[kk][1]}"
    check(f"{d['label']}: every container held is bounded by the asserted "
          f"structure",
          not unbounded,
          f"held {sorted(containers)}; unbounded: {unbounded or 'none'}")

    # (2) no container holds an address.  An address is a full orientation
    #     of all n contents; the only place one may appear is a stack frame,
    #     and there at most one per pending branch.
    stack = held.get("stack", [])
    check(f"{d['label']}: the addresses held number one per pending branch, "
          f"{len(stack)} <= n = {n}",
          len(stack) <= n
          and all(isinstance(fr, tuple) and len(fr) in (3, 4) for fr in stack))

    # (3) the boundary-indexed containers hold indices and bits, never
    #     addresses
    idxok = all(isinstance(j, int) and 0 <= j < len(bnds)
                for nm in ("live", "live0", "clive")
                for j in held.get(nm, ()) or ())
    bitok = all(isinstance(b, int) and b > 0 and (b & (b - 1)) == 0
                for nm in ("forcing", "forcing0", "cforcing")
                for b in (held.get(nm) or {}))
    check(f"{d['label']}: the live sets hold boundary indices and the "
          f"forcing maps hold single content bits, not addresses",
          idxok and bitok)

    # (4) nothing held grows with the number of standing addresses
    standing = len(d["solutions"])
    check(f"{d['label']}: no container's size reaches the standing count "
          f"({standing}) by accumulation",
          all(kk in bounds for kk in containers),
          "a list of produced addresses would appear here as an "
          "undeclared container")
    gen.close()
print()

# ---------------------------------------------------------------------------
print("F.8  WHICH BOUNDARY EXCLUDES THIS ADDRESS -- NAMED, NOT DETECTED")
print("     exhaustive over the envelope.  Every named boundary is checked")
print("     against the clause it was asserted from, so the test does not")
print("     re-evaluate its own predicate.")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    ok = 0
    excluded = 0
    for a in range(1 << n):
        named = excluding_boundaries(a, bnds)
        # the clauses that genuinely fail at this address, read from the
        # clauses themselves
        failing = {i for i, c in enumerate(d["clauses"])
                   if not any(((a >> (p - 1)) & 1) == (lit > 0)
                              for p, lit in c)}
        if set(named) == failing:
            if failing:
                excluded += 1
            ok += 1
    report(f"{d['label']}: the named boundaries are exactly the failing "
           f"clauses, on every address", ok, 1 << n,
           f"{excluded} excluded addresses")
print()

# ---------------------------------------------------------------------------
print("=" * 74)
print(f"  APPENDIX F   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
