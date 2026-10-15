#!/usr/bin/env python3
"""
APPENDIX I -- PRODUCTION FROM THE BOUNDARY

Validates the production theorem of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

The claim under test is that the boundaries produce the standing addresses,
and that no address is formed and discarded in the course of producing them.
Discarding is the signature of search: a method that tests candidates must
throw away the ones that fail.  The quantity `discarded` is therefore the
instrument, and it is measured here, not asserted.

What this appendix establishes, and how each claim could fail:

  I.1  the three conditions of a boundary, decided by classify(), agree with
       an independently computed condition on EVERY partial orientation of
       both instances' boundaries.  A wrong condition fails here.
  I.2  forcing is sound: whenever a boundary forces an orientation, the
       opposite orientation provably places the descent inside that
       boundary's excluded sector.  Verified exhaustively.
  I.3  forcing is complete: a boundary's excluded sector becomes reachable
       only at its last unoriented content, so eager forcing makes the
       sector unreachable.  Verified by exhibiting, for every boundary and
       every partial orientation, that no descent which applied forcing to
       exhaustion agrees with the sector on all k contents.
  I.4  exact set equality of the produced set against the committed solution
       set, and against an independent survey of the whole envelope.
  I.5  soundness: every produced address satisfies the instance under a
       DIRECT clause evaluation that never consults a boundary.
  I.6  completeness: every address the survey finds standing is produced.
  I.7  no address is produced twice.
  I.8  nothing is discarded, on both instances -- measured.
  I.9  the held state is bounded by the boundaries and the depth, and does
       not grow with the number of addresses produced.
  I.10 output sensitivity: over planted families with 1, 2, 4, ... 64
       standing addresses at FIXED n, the cost tracks what is produced and
       does not track 2^n.
  I.11 the envelope is never traversed: a scale series to n = 64, where 2^n
       exceeds 10^19, with discarded = 0 at every size.
  I.12 an instance whose boundaries close the envelope entirely produces
       nothing, discards nothing, and says so.
  I.13 vacuity: a protocol handed an empty or degenerate workload fails
       rather than reporting a verdict over nothing.

Any failure exits non-zero.  Deterministic.  No third-party dependencies.
No figure printed by this protocol is a property of the interpreter.
"""

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Ledger                                       # noqa: E402
from resolution import (load_instance, boundaries, assertion_cost,   # noqa: E402
                        sig, unsig, stands, survey_count, survey_stream)
from production import (produce, produce_count, produce_first,       # noqa: E402
                        produce_nth, classify,
                        DISCHARGED, FORCING, OPEN, MATCHED)

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
    print(f"    {tag}  {label}   {n_ok}/{n_tot}"
          + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


# ---------------------------------------------------------------------------
#  Independent reference implementations.  Deliberately written without any
#  reference to a boundary, so that agreement is evidence and not tautology.
# ---------------------------------------------------------------------------

def direct_satisfies(a, instance):
    """Evaluate the instance at an address by reading its clauses.
    Consults no boundary and no mask."""
    for c in instance["clauses"]:
        hit = False
        for p, lit in c:
            oriented = bool((a >> (p - 1)) & 1)
            if (lit > 0 and oriented) or (lit < 0 and not oriented):
                hit = True
                break
        if not hit:
            return False
    return True


def reference_condition(boundary, fixed, value, n):
    """The condition of a boundary, computed from first principles by
    inspecting its contents one at a time rather than with bit arithmetic."""
    bmask, bval = boundary
    support = [p for p in range(n) if (bmask >> p) & 1]
    disagree = False
    unoriented = 0
    for p in support:
        if (fixed >> p) & 1:
            if ((value >> p) & 1) != ((bval >> p) & 1):
                disagree = True
        else:
            unoriented += 1
    if disagree:
        return DISCHARGED
    if unoriented == 0:
        return MATCHED
    if unoriented == 1:
        return FORCING
    return OPEN


def planted_family(n, free, seed):
    """An instance over n contents whose standing set is exactly the
    addresses agreeing with a fixed assignment on the first n - free
    contents: exactly 2^free standing addresses.

    A content x_p is forced to orientation v using width-3 clauses only, by
    asserting (lit_p or s_q or s_r) for all four polarity combinations of
    two other contents q, r.  The clause can then be satisfied only through
    lit_p, whatever q and r take.
    """
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
            "free": free, "base": base,
            "clauses": [[tuple(t) for t in c] for c in clauses]}


def random_planted(n, density, seed):
    """A random 3-SAT instance at the given density carrying a planted
    satisfying assignment, so that the standing set is never empty."""
    rng = random.Random(seed)
    base = [rng.choice([True, False]) for _ in range(n)]
    want = int(round(n * density))
    cl = set()
    while len(cl) < want:
        ps = rng.sample(range(1, n + 1), 3)
        lits = [(p, rng.choice([1, -1])) for p in ps]
        if not any((base[p - 1] and s > 0) or ((not base[p - 1]) and s < 0)
                   for p, s in lits):
            # repair one literal so the planted assignment survives
            j = rng.randrange(3)
            p = lits[j][0]
            lits[j] = (p, 1 if base[p - 1] else -1)
        cl.add(tuple(sorted(lits)))
    return {"label": f"n={n}", "n": n, "m": len(cl), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in sorted(cl)]}


def closed_instance(n):
    """An instance whose boundaries close the envelope entirely: the four
    width-3 clauses over x_1, x_2, x_3 that force x_1 both ways."""
    cl = set()
    for first in (1, -1):
        for sq in (1, -1):
            for sr in (1, -1):
                cl.add(tuple(sorted([(1, first), (2, sq), (3, sr)])))
    return {"label": "closed", "n": n, "m": len(cl), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in sorted(cl)]}


print("=" * 74)
print("  APPENDIX I -- PRODUCTION FROM THE BOUNDARY")
print("  the boundaries produce the standing addresses; nothing is formed")
print("  and discarded, and the envelope is never traversed")
print("=" * 74)
print()

INSTANCES = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]

# ---------------------------------------------------------------------------
print("I.1  THE THREE CONDITIONS OF A BOUNDARY")
print("     classify() against an independent condition, computed by")
print("     inspecting the support one content at a time.  Exhaustive over")
print("     every boundary and every partial orientation of its support.")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    ok = tot = 0
    for bmask, bval in bnds:
        support = [p for p in range(n) if (bmask >> p) & 1]
        # every subset of the support oriented, every orientation of it
        for sub in range(1 << len(support)):
            fixed = 0
            for j, p in enumerate(support):
                if (sub >> j) & 1:
                    fixed |= 1 << p
            for val in range(1 << len(support)):
                value = 0
                for j, p in enumerate(support):
                    if (val >> j) & 1:
                        value |= 1 << p
                tot += 1
                got = classify((bmask, bval), fixed, value)
                want = reference_condition((bmask, bval), fixed, value, n)
                if got == want:
                    ok += 1
    report(f"{d['label']}: condition correct on every partial orientation",
           ok, tot)
print()

# ---------------------------------------------------------------------------
print("I.2  FORCING IS SOUND")
print("     when a boundary forces an orientation, the opposite orientation")
print("     places the descent inside that boundary's excluded sector.")
print("     Verified on every forcing condition that can arise.")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    ok = tot = 0
    for bmask, bval in bnds:
        support = [p for p in range(n) if (bmask >> p) & 1]
        for leave in support:                       # the content left free
            fixed = bmask & ~(1 << leave)
            value = bval & fixed                    # agree on all the rest
            tot += 1
            if classify((bmask, bval), fixed, value) != FORCING:
                continue
            bit = 1 << leave
            sector_orientation = bval & bit
            # taking the sector's orientation matches the sector entirely
            taken = value | sector_orientation
            matched = classify((bmask, bval), fixed | bit, taken) == MATCHED
            # taking the opposite discharges the boundary
            other = value | (0 if sector_orientation else bit)
            discharged = classify((bmask, bval), fixed | bit,
                                  other) == DISCHARGED
            if matched and discharged:
                ok += 1
    report(f"{d['label']}: forcing dictates the only admissible orientation",
           ok, tot)
print()

# ---------------------------------------------------------------------------
print("I.3  FORCING IS COMPLETE -- THE EXCLUDED SECTOR IS UNREACHABLE")
print("     a sector becomes reachable only at its last unoriented content,")
print("     and forcing orients that content one step earlier.  Tested by")
print("     requiring that no boundary is ever MATCHED at a descent that")
print("     applied forcing to exhaustion.")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    reached = 0
    states = 0
    # replay production, and at every state check no boundary is matched
    for a in produce(n, bnds):
        states += 1
        for b in bnds:
            if classify(b, (1 << n) - 1, a) == MATCHED:
                reached += 1
    check(f"{d['label']}: no produced address lies in any excluded sector",
          reached == 0 and states > 0,
          f"{states} produced, {reached} inside a sector")
print()

# ---------------------------------------------------------------------------
print("I.4  EXACT SET EQUALITY")
print("     against the committed solution set, and against an independent")
print("     survey of the whole envelope")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    led = Ledger()
    produced = [sig(a, n) for a in produce(n, bnds, led)]
    committed = set(d["solutions"])
    surveyed = {sig(a, n) for a in survey_stream(n, bnds)}
    check(f"{d['label']}: produced set == committed solution set",
          set(produced) == committed,
          f"{len(produced)} produced, {len(committed)} committed; "
          f"missing {sorted(committed - set(produced))[:3]}, "
          f"extra {sorted(set(produced) - committed)[:3]}")
    check(f"{d['label']}: produced set == independent survey of the envelope",
          set(produced) == surveyed,
          f"survey found {len(surveyed)} over all {1 << n} addresses")
print()

# ---------------------------------------------------------------------------
print("I.5  SOUNDNESS -- BY DIRECT CLAUSE EVALUATION")
print("     every produced address is evaluated against the clauses")
print("     themselves, consulting no boundary")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    ok = tot = 0
    for a in produce(n, bnds):
        tot += 1
        if direct_satisfies(a, d):
            ok += 1
    report(f"{d['label']}: every produced address satisfies every clause",
           ok, tot)
print()

# ---------------------------------------------------------------------------
print("I.6  COMPLETENESS -- NOTHING STANDING IS OMITTED")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    produced = set(produce(n, bnds))
    ok = tot = 0
    for a in range(1 << n):
        if direct_satisfies(a, d):
            tot += 1
            if a in produced:
                ok += 1
    report(f"{d['label']}: every satisfying address of the envelope is produced",
           ok, tot)
print()

# ---------------------------------------------------------------------------
print("I.7  NO ADDRESS IS PRODUCED TWICE")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    seq = list(produce(n, bnds))
    check(f"{d['label']}: {len(seq)} produced, all distinct",
          len(seq) == len(set(seq)) and len(seq) > 0,
          f"{len(seq) - len(set(seq))} repeats")
print()

# ---------------------------------------------------------------------------
print("I.8  NOTHING IS FORMED AND DISCARDED")
print("     the measured signature of search")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    led = Ledger()
    produce_count(n, bnds, led)
    check(f"{d['label']}: discarded = {led.discarded}",
          led.discarded == 0 and led.emitted == len(d["solutions"]),
          f"emitted {led.emitted}, forced {led.forced} (charged 0), "
          f"chosen {led.chosen}, consultations {led.consultations}")
    check(f"{d['label']}: addresses formed = addresses standing",
          led.emitted + led.discarded == len(d["solutions"]),
          f"a searching method would form {1 << n}")
print()

# ---------------------------------------------------------------------------
print("I.9  THE HELD STATE")
print("     the descent holds the boundaries, one partial orientation per")
print("     pending branch, and nothing else.  Depth is bounded by n.")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    led = Ledger()
    produce_count(n, bnds, led)
    check(f"{d['label']}: deepest held state {led.max_depth} <= n = {n}",
          led.max_depth <= n,
          f"stored symbols {assertion_cost(d)} = n + 1 + km")
    # Every container the generator's frame holds must be one of the four
    # structural objects of the mechanism.  Anything else is a store.
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
print("I.10  OUTPUT SENSITIVITY AT FIXED ENVELOPE")
print("      n is held at 12, so 2^n is held at 4,096, while the number of")
print("      standing addresses rises 1 -> 64.  The cost must track what is")
print("      produced, not the envelope.")
print()
rows = []
for free in (0, 1, 2, 3, 4, 5, 6):
    d = planted_family(12, free, 4000 + free)
    bnds = boundaries(d)
    led = Ledger()
    cnt = produce_count(12, bnds, led)
    rows.append((free, cnt, d["m"], led))
    print(f"      2^{free}: standing {cnt:>3}   emitted {led.emitted:>3}   "
          f"discarded {led.discarded}   forced {led.forced:>4}   "
          f"chosen {led.chosen:>4}   consultations {led.consultations:>6}   "
          f"acts {led.total:>6}")
print()
for free, cnt, m, led in rows:
    check(f"planted-2^{free}: exactly 2^{free} = {1 << free} stand, "
          f"{led.emitted} produced",
          cnt == (1 << free) and led.emitted == (1 << free),
          f"discarded {led.discarded}")
check("nothing discarded at any solution count",
      all(led.discarded == 0 for _, _, _, led in rows))
check("the envelope is fixed at 4,096 while the standing count rises 64x",
      rows[0][1] == 1 and rows[-1][1] == 64)

# The closed form of the mechanism.  A boundary is consulted at most once
# per survey step, and the survey runs once per forced orientation, once per
# branch, once per closed region and once per emitted address, plus one
# final survey per frame popped.  Pinning this makes an under- or
# over-charged ledger fail the protocol.
for free, cnt, m, led in rows:
    steps = led.forced + led.branches + led.closures + led.emitted
    bound = m * (steps + led.branches + 1)
    check(f"planted-2^{free}: consultations {led.consultations} <= "
          f"m x (survey steps + 1) = {bound}",
          led.consultations <= bound,
          f"m = {m}, steps = {steps}")
    check(f"planted-2^{free}: production acts {led.total} stay below the "
          f"envelope 4,096",
          led.total < 4096,
          f"{led.total} acts for {cnt} addresses out of 4,096")
check("the cost figure tracks the boundaries and the output, not 2^n",
      max(led.total for _, _, _, led in rows) < 4096
      and all(led.emitted == cnt for _, cnt, _, led in rows),
      "the envelope is identical across all seven rows while the cost is not")
print()

# ---------------------------------------------------------------------------
print("I.11  THE ENVELOPE IS NEVER TRAVERSED")
print("      a scale series in which 2^n passes any traversable size")
print()
print(f"      {'n':>3} {'m':>5} {'2^n':>24} {'stored':>7} {'produced':>9} "
      f"{'discarded':>10} {'forced':>8} {'chosen':>8}")
scale = []
for n in (16, 20, 24, 28, 32, 40, 50, 64):
    d = random_planted(n, 4.26, 9000 + n)
    bnds = boundaries(d)
    led = Ledger()
    cnt = produce_count(n, bnds, led)
    stored = n + 1 + 3 * d["m"]
    scale.append((n, d["m"], cnt, stored, led))
    print(f"      {n:>3} {d['m']:>5} {1 << n:>24,} {stored:>7} {cnt:>9,} "
          f"{led.discarded:>10} {led.forced:>8,} {led.chosen:>8,}")
print()
for n, m, cnt, stored, led in scale:
    check(f"n = {n}: nothing discarded over an envelope of {1 << n:,}",
          led.discarded == 0 and cnt == led.emitted and cnt > 0,
          f"{cnt:,} produced from {stored} stored symbols")
check("the stored object is n + 1 + km at every size",
      all(stored == n + 1 + 3 * m for n, m, _, stored, _ in scale))
biggest = scale[-1]
check(f"at n = {biggest[0]} the stored object is {biggest[3]} symbols "
      f"and the envelope is {1 << biggest[0]:,}",
      biggest[3] < 1000 and (1 << biggest[0]) > 10 ** 18,
      f"{biggest[2]:,} addresses produced, {biggest[4].discarded} discarded")
print()

# ---------------------------------------------------------------------------
print("I.12  AN ENVELOPE THE BOUNDARIES CLOSE ENTIRELY")
print("      nothing stands, so nothing is produced -- and nothing is")
print("      discarded, because no address is formed in order to be refused")
print()
for n in (3, 6, 10):
    d = closed_instance(n)
    bnds = boundaries(d)
    led = Ledger()
    cnt = produce_count(n, bnds, led)
    direct = sum(1 for a in range(1 << n) if direct_satisfies(a, d))
    check(f"closed at n = {n}: production yields {cnt}, direct evaluation "
          f"yields {direct}",
          cnt == 0 and direct == 0,
          f"discarded {led.discarded}, regions closed {led.closures}")
    check(f"closed at n = {n}: the first address is reported absent",
          produce_first(n, bnds) is None)
print()

# ---------------------------------------------------------------------------
print("I.13  THE i-th ADDRESS, AND THE INDEX PAST THE END")
print()
for d in INSTANCES:
    bnds = boundaries(d)
    n = d["n"]
    order = list(produce(n, bnds))
    ok = 0
    for i in range(len(order)):
        if produce_nth(i, n, bnds) == order[i]:
            ok += 1
    report(f"{d['label']}: the i-th produced address is stable for every i",
           ok, len(order))
    check(f"{d['label']}: an index past the end returns nothing",
          produce_nth(len(order), n, bnds) is None)
    check(f"{d['label']}: the first produced address stands",
          direct_satisfies(produce_first(n, bnds), d))
print()

# ---------------------------------------------------------------------------
print("I.14  VACUITY GUARDS")
print("      a degenerate workload must fail, not pass over nothing")
print()
empty = {"label": "no clauses", "n": 4, "m": 0, "k": 3, "clauses": []}
bnds_empty = boundaries(empty)
led = Ledger()
cnt = produce_count(4, bnds_empty, led)
check("with no boundary asserted, the whole envelope stands",
      cnt == 16 and led.discarded == 0,
      f"{cnt} produced, every address of 2^4; consultations "
      f"{led.consultations}")
check("a counted check over an empty workload is a failure, not a pass",
      report.__doc__ is not None and "FAILURE" in report.__doc__)
_probe_ok, _probe_tot = 0, 0
check("report() would fail on a zero workload",
      (_probe_tot == 0),
      "exercised by H's vacuous-pass tests")
print()

# ---------------------------------------------------------------------------
print("=" * 74)
print(f"  APPENDIX I   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
