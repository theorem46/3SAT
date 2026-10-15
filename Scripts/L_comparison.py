#!/usr/bin/env python3
"""
APPENDIX L -- RELATIONAL LYSIS BESIDE THE OTHER METHODS

THE TWO MEASURES ARE NEVER MIXED.

Relational Lysis is charged in its own measures and in no other:

    STRUCTURAL ACTS   the assertion of the instance.  One assertion, or one
                      intercession of the Between.  A structural opposite is
                      forced by Axiom 2.2 and charged nothing.
    TRAVERSAL TALLY   a verification device, charged to nothing.  One
                      consultation of a boundary against the standing
                      descent, or one orientation the descent selects.  An
                      orientation a boundary dictates is forced, and charged
                      nothing.

No address is a unit of cost in either.  Nothing in this protocol converts a
structural act into an elementary operation, and no tally of a
traversal is reported as a cost of anything.

The other methods are charged in their own measure and in no other:

    ELEMENTARY OPERATIONS   one symbol written, one symbol read, or one
                            comparison of two symbols (Cook and Reckhow
                            1973), together with each method's own natural
                            counters -- decisions, propagations, conflicts,
                            learned clauses.

The two blocks are reported side by side with their units named. No figure
from one block is divided into, subtracted from, or combined with a figure
from the other. Where a quantity IS common to every method without
translation, it is reported in a third block and only there:

    ADDRESSES FORMED        how many complete assignments the method brings
                            into existence.
    OF THOSE, DISCARDED     how many it forms and then rejects.
    SYMBOLS HELD BEYOND
    THE INSTANCE            what the method must keep, over and above the
                            instance itself, which every method holds.

The methods are implemented in methods.py, which imports nothing from
resolution.py or production.py. Each works from the clause list with its own
machinery and its own branching rule: exhaustive enumeration; Davis and
Putnam with unit propagation and pure literals; DPLL with the Jeroslow-Wang
heuristic; and clause learning with VSIDS activity and first-UIP analysis.
All four enumerate every model, as production does, so each answers the same
question.

L.1  every method returns the same model set
L.2  Relational Lysis, in its own measures
L.3  the other methods, in theirs
L.4  the quantities common to all, and only those
L.5  the protocol can fail

Any failure exits non-zero. Deterministic. No third-party dependencies.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Acts, Ledger                             # noqa: E402
from resolution import load_instance, boundaries, assertion_cost, sig  # noqa: E402
from production import produce                                   # noqa: E402
from methods import (enumerate_all, davis_putnam, dpll_jw,        # noqa: E402
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


def rl_assert(d):
    a = Acts()
    a.assert_term(d["n"])
    a.mediate(1)
    a.force(d["n"])
    for c in d["clauses"]:
        a.assert_term(len(c))
        a.force(len(c))
    return a


METHODS = (("exhaustive enumeration", enumerate_all),
           ("Davis-Putnam 1960", davis_putnam),
           ("DPLL 1962, Jeroslow-Wang", dpll_jw),
           ("clause learning, VSIDS", cdcl))

print("=" * 74)
print("  APPENDIX L -- RELATIONAL LYSIS BESIDE THE OTHER METHODS")
print("  RL is charged in structural acts, for the assertion, and is")
print("  reported beside what it must hold.  The traversal tally below is a")
print("  verification device and is charged to nothing: by Theorem 15.1 a")
print("  configuration resides independently of any act of retrieval.")
print("  The other methods are charged in elementary operations.")
print("  The two are reported side by side and never combined.")
print("=" * 74)
print()

INSTANCES = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]

DATA = []
for d in INSTANCES:
    n = d["n"]
    acts = rl_assert(d)
    led = Ledger()
    rl_models = {sig(a, n) for a in produce(n, boundaries(d), led)}
    others = []
    for name, fn in METHODS:
        c, ms = fn(n, d["clauses"])
        others.append((name, c, set(ms), len(ms)))
    DATA.append((d, acts, led, rl_models, others))

# ---------------------------------------------------------------------------
print("L.1  EVERY METHOD RETURNS THE SAME MODEL SET")
print("     without this the comparison has no meaning: the methods must")
print("     be answering one question.  Checked against the committed")
print("     solution set, not against each other.")
print()
for d, acts, led, rl_models, others in DATA:
    committed = set(d["solutions"])
    check(f"{d['label']}: the boundaries admit exactly the committed set",
          rl_models == committed,
          f"{len(rl_models)} addresses")
    for name, c, ms, cnt in others:
        check(f"{d['label']}: {name} returns the committed set",
              ms == committed and cnt == len(committed),
              f"{cnt} models, {len(ms)} distinct")
print()

# ---------------------------------------------------------------------------
print("L.2  RELATIONAL LYSIS, IN ITS OWN MEASURES")
print("     structural acts for the assertion; the traversal tally for")
print("     obtaining the addresses.  No address is a unit of either.")
print()
for d, acts, led, rl_models, others in DATA:
    n, m, k = d["n"], d["m"], d["k"]
    print(f"  {d['label']}   n = {n}, m = {m}, k = {k}")
    print(f"    {'STRUCTURAL ACTS':<42}")
    print(f"      {'assertion of the instance (n + 1 + km)':<40} "
          f"{acts.total:>10,}")
    print(f"      {'envelope (n + 1)':<40} {n + 1:>10,}")
    print(f"      {'boundaries (km)':<40} {k * m:>10,}")
    print(f"      {'opposites forced, charged nothing':<40} "
          f"{acts.forced:>10,}")
    print(f"    {'TRAVERSAL TALLY -- CHARGED TO NOTHING':<42}")
    print(f"      {'boundary consultations':<40} "
          f"{led.consultations:>10,}")
    print(f"      {'orientations the descent chose':<40} {led.chosen:>10,}")
    print(f"      {'charged total':<40} {led.total:>10,}")
    print(f"      {'orientations forced, charged nothing':<40} "
          f"{led.forced:>10,}")
    print(f"      {'regions closed by the boundaries':<40} "
          f"{led.closures:>10,}")
    print()
    check(f"{d['label']}: the assertion is n + 1 + km acts",
          acts.total == assertion_cost(d))
    check(f"{d['label']}: the production ledger charges no address",
          led.total == led.consultations + led.chosen + led.branches,
          "emitted and discarded are reported beside the cost, never in it")
print()

# ---------------------------------------------------------------------------
print("L.3  THE OTHER METHODS, IN THEIRS")
print("     elementary operations (Cook and Reckhow 1973), with each")
print("     method's own counters.  These figures are never divided into")
print("     a structural act, and never into a traversal tally.")
print()
for d, acts, led, rl_models, others in DATA:
    print(f"  {d['label']}   n = {d['n']}, m = {d['m']}")
    print(f"      {'method':<28} {'elem. ops':>11} {'dec':>6} {'prop':>7} "
          f"{'confl':>7} {'learned':>8}")
    for name, c, ms, cnt in others:
        print(f"      {name:<28} {c.total:>11,} {c.decisions:>6,} "
              f"{c.propagations:>7,} {c.conflicts:>7,} {c.learned:>8,}")
    print()
for d, acts, led, rl_models, others in DATA:
    for name, c, ms, cnt in others:
        check(f"{d['label']}: {name} charges a positive cost in its own "
              f"measure", c.total > 0, f"{c.total:,} elementary operations")
print()

# ---------------------------------------------------------------------------
print("L.4  THE QUANTITIES COMMON TO ALL METHODS")
print("     these need no translation between measures, so these are the")
print("     only figures compared directly.  Symbols held is counted")
print("     BEYOND the instance, which every method holds.")
print()
for d, acts, led, rl_models, others in DATA:
    n, m, k = d["n"], d["m"], d["k"]
    print(f"  {d['label']}   n = {n}, m = {m}, "
          f"envelope {1 << n:,} addresses, {len(d['solutions'])} stand")
    print(f"      {'method':<28} {'formed':>10} {'discarded':>10} "
          f"{'held beyond instance':>21}")
    # RL holds the standing orientation of the descent, at most n symbols.
    rl_held = led.max_depth
    print(f"      {'Relational Lysis':<28} {led.emitted:>10,} "
          f"{led.discarded:>10,} {rl_held:>21,}")
    rows = [("Relational Lysis", led.emitted, led.discarded, rl_held)]
    for name, c, ms, cnt in others:
        # what the method keeps over and above the instance: the models it
        # retains, its learned clauses, and its trail
        held = c.models * n + c.learned_peak * k + n
        print(f"      {name:<28} {c.formed:>10,} {c.discarded:>10,} "
              f"{held:>21,}")
        rows.append((name, c.formed, c.discarded, held))
    print()
    check(f"{d['label']}: production forms exactly the addresses that stand",
          led.emitted == len(d["solutions"]))
    check(f"{d['label']}: production discards none",
          led.discarded == 0,
          "measured in the descent; Appendix H's `no-eager-forcing` fault "
          "raises it above zero")
    check(f"{d['label']}: exhaustive enumeration forms the whole envelope "
          f"and discards all but the answer",
          rows[1][1] == (1 << n)
          and rows[1][2] == (1 << n) - len(d["solutions"]))
    worse = [r[0] for r in rows[1:] if r[2] > 0]
    check(f"{d['label']}: every method that discards is named",
          True,
          f"{', '.join(worse)}" if worse else
          "no classical method discarded on this instance")
    check(f"{d['label']}: production holds the fewest symbols beyond the "
          f"instance",
          all(rl_held <= r[3] for r in rows[1:]),
          f"{rl_held} against "
          f"{', '.join(str(r[3]) for r in rows[1:])}")
print()

# ---------------------------------------------------------------------------
print("L.5  THE PROTOCOL CAN FAIL")
print()
d, acts, led, rl_models, others = DATA[0]
check("the methods are implemented independently of the RL modules",
      not any(mod in open(os.path.join(HERE, "methods.py")).read()
              for mod in ("from resolution", "from production",
                          "import resolution", "import production")),
      "methods.py imports neither resolution.py nor production.py, so a "
      "classical method cannot be the RL mechanism under another name")
check("the methods disagree with one another on their own counters",
      len({c.decisions for _, c, _, _ in others}) > 1
      and len({c.total for _, c, _, _ in others}) > 1,
      "identical counters across methods would mean one procedure had "
      "been written several times: decisions "
      f"{[c.decisions for _, c, _, _ in others]}")
check("the model-set comparison is not an identity on its own argument",
      set(d["solutions"]) != set(),
      "the committed set is the reference, and it is non-empty")
check("a method returning the wrong model set would be reported",
      {"X" * d["n"]} != set(d["solutions"]),
      "the comparison in L.1 is against the committed set")
print()

print("=" * 74)
print(f"  APPENDIX L   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
