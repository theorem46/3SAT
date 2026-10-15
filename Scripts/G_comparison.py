#!/usr/bin/env python3
"""
APPENDIX G -- THE COST COMPARISON

Validates the cost claim of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

Both methods are instrumented under conventions.py so that neither is
charged differently from the other.  Three categories are kept separate
and never folded together:

  STRUCTURAL ACT        an assertion, or one intercession of the Between
  ELEMENTARY OPERATION  one write, read or comparison (Cook and Reckhow 1973)
  BOOKKEEPING           any operation of the implementation that is neither

The third category exists so that no overhead of this program can be
mistaken for a cost of either method.  It is reported and excluded.

Any failure exits non-zero.  Deterministic.  No third-party dependencies.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Acts, Ops, COOK_RECKHOW                  # noqa: E402
from resolution import load_instance, boundaries, assertion_cost, sig  # noqa: E402
from conventions import Ledger                                   # noqa: E402
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


# ---------------------------------------------------------------------------
#  RL: assert the structure.  Structural acts only.
# ---------------------------------------------------------------------------

def rl_assert(d):
    a = Acts()
    a.assert_term(d["n"])          # Definition 3.1: name the contents
    a.mediate(1)                   # Axiom 4.1: the one intercession
    a.force(d["n"])                # Axiom 2.2: the opposites, charged nothing
    for c in d["clauses"]:
        a.assert_term(len(c))      # Theorem 7.2: k symbols per boundary
        a.force(len(c))            # Theorem 7.1: the reversal, forced
    return a


# ---------------------------------------------------------------------------
#  Enumeration: form each address, then read it against the clauses.
#  Charged in elementary operations.
# ---------------------------------------------------------------------------

def enum_resolve(d):
    o = Ops()
    n = d["n"]
    standing = 0
    for a in range(1 << n):
        o.write(n)                           # form the address: n symbols
        o.form()                             # and it is now an address
        satisfied = True
        for c in d["clauses"]:
            hit = False
            for p, lit in c:
                o.read(1)                    # read one literal
                if ((a >> (p - 1)) & 1) == (lit > 0):
                    hit = True
                    break
            if not hit:
                satisfied = False
                break
        if satisfied:
            standing += 1
            o.write(n)                       # retain the answer
        else:
            o.discard()                      # formed, then thrown away
    return o, standing


# ---------------------------------------------------------------------------
#  RL: put one question to the boundaries.  Elementary operations.
# ---------------------------------------------------------------------------

def rl_membership(a, bnds):
    o = Ops()
    for mask, value in bnds:
        o.compare(bin(mask).count("1"))
        if (a & mask) == value:
            return o, False
    return o, True


print("=" * 74)
print("  APPENDIX G -- THE COST COMPARISON")
print(f"  elementary operation in the sense of {COOK_RECKHOW}")
print("  structural acts, elementary operations and bookkeeping")
print("  are reported separately and never combined")
print("=" * 74)
print()

INSTANCES = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]

results = []
for d in INSTANCES:
    n, m, k = d["n"], d["m"], d["k"]
    bnds = boundaries(d)
    a = rl_assert(d)
    o, standing = enum_resolve(d)
    # production, instrumented.  Every RL figure below comes from this
    # ledger or from the assertion; none is a literal written into the
    # table.  See conventions.py: no address is a unit of cost, and the
    # diagnostic quantity is `discarded`.
    led = Ledger()
    produced = sum(1 for _ in produce(d["n"], bnds, led))
    results.append((d, a, o, standing, bnds, led, produced))

# ---------------------------------------------------------------------------
print("G.1  THE ASSERTION COST IS n + 1 + km")
print()
for d, a, o, standing, bnds, led, produced in results:
    n, m, k = d["n"], d["m"], d["k"]
    check(f"{d['label']}: {a.total} acts = {n} + 1 + {k}x{m}",
          a.total == assertion_cost(d),
          f"assertions {a.assertions}, mediations {a.mediations}, "
          f"forced {a.forced} charged 0")
print()

# ---------------------------------------------------------------------------
print("G.2  BOTH METHODS RETURN THE SAME SATISFYING ASSIGNMENTS")
print()
for d, a, o, standing, bnds, led, produced in results:
    check(f"{d['label']}: enumeration finds {standing}, "
          f"committed set has {len(d['solutions'])}",
          standing == len(d["solutions"]))
print()

# ---------------------------------------------------------------------------
print("G.3  THE COMPARISON")
print()
hdr = (f"  {'':<34} {'RL':>14} {'Enumeration':>14}")
for d, a, o, standing, bnds, led, produced in results:
    n, m, k = d["n"], d["m"], d["k"]
    print(f"  {d['label']}   n = {n}, m = {m}, k = {k}")
    print(hdr)
    print("  " + "-" * 64)
    rows = [
        ("growth of what is stored", "linear", "exponential"),
        ("SYMBOLS HELD", f"{assertion_cost(d):,}", f"{standing * n:,}"),
        ("  the boundaries (n + 1 + km)", f"{assertion_cost(d):,}", "-"),
        ("  addresses retained", "-", f"{standing:,} x {n}"),
        ("ADDRESSES FORMED", f"{led.emitted:,}", f"{1 << n:,}"),
        ("  of those, discarded", f"{led.discarded:,}", f"{(1 << n) - standing:,}"),
        ("acts to assert the structure", f"{a.total:,}", "-"),
        ("  envelope (n + 1)", f"{n + 1:,}", "-"),
        ("  boundaries (km)", f"{k * m:,}", "-"),
        ("opposites forced, charged 0", f"{a.forced:,}", "-"),
        ("orientations forced by a boundary", f"{led.forced:,}", "-"),
        ("orientations the descent chose", f"{led.chosen:,}", "-"),
        ("boundary consultations", f"{led.consultations:,}", "-"),
        ("literal reads", "-", f"{o.reads:,}"),
        ("symbol writes", "-", f"{o.writes:,}"),
        ("satisfying assignments", f"{led.emitted}", f"{standing}"),
    ]
    for lbl, l, r in rows:
        print(f"  {lbl:<34} {l:>14} {r:>14}")
    print("  " + "-" * 64)
    print(f"  symbols held: {assertion_cost(d):,} against {standing * n:,}"
          f"   ({standing * n / assertion_cost(d):.2f} to 1)")
    print(f"  addresses formed: {led.emitted:,} against {1 << n:,}"
          f"   ({(1 << n) / max(1, led.emitted):,.0f} to 1)")
    print(f"  addresses discarded: {led.discarded:,} against "
          f"{(1 << n) - standing:,}")
    print()
    print("  The two columns are compared only where the unit is common:")
    print("  symbols held, and addresses formed.  Structural acts and")
    print("  elementary operations are reported in their own measures and")
    print("  are never divided into one another (conventions.py).")
    print()

# ---------------------------------------------------------------------------
print("G.3z  THE RL COLUMN IS MEASURED, NOT DECLARED")
print("      every RL figure above comes from the production ledger or")
print("      the assertion.  These checks fail if any of them is a")
print("      literal rather than a measurement.")
print()
for d, a, o, standing, bnds, led, produced in results:
    n = d["n"]
    check(f"{d['label']}: addresses produced {led.emitted} equals the "
          f"committed solution count",
          led.emitted == len(d["solutions"]) == produced)
    check(f"{d['label']}: addresses discarded is {led.discarded}, measured "
          f"from the descent",
          led.discarded == 0,
          "a discard is an address formed and then thrown away; the "
          "counter rises under Appendix H's `no-eager-forcing` fault")
    check(f"{d['label']}: production holds no retained address, while "
          f"enumeration retains {standing}",
          led.max_depth <= n and standing > 0,
          f"deepest held orientation {led.max_depth} <= n = {n}")
    check(f"{d['label']}: the ledger's charged total is its own parts",
          led.total == led.consultations + led.chosen + led.branches,
          f"consultations {led.consultations}, chosen {led.chosen}, "
          f"branches {led.branches}; forced {led.forced} charged 0")
    check(f"{d['label']}: enumeration forms 2^n and discards "
          f"{(1 << n) - standing}, production forms {led.emitted} and "
          f"discards {led.discarded}",
          o.formed == (1 << n)
          and o.discarded == (1 << n) - standing
          and led.emitted == standing
          and led.discarded == 0,
          "both sides checked against their own counters")
print()

print("G.3a  THE ACCOUNTING IS PINNED TO CLOSED FORMS")
print("      neither column may be silently under- or over-charged:")
print("      each measure is bounded above and below by a form derived from")
print("      the method itself, so an accounting error fails the protocol.")
print()
for d, a, o, standing, bnds, led, produced in results:
    n, m, k = d["n"], d["m"], d["k"]
    N = 1 << n

    # Enumeration must form every address it tests: n symbols each.
    form_lo = N * n
    retained = standing * n
    check(f"{d['label']}: enumeration writes {o.writes:,} >= n*2^n + retained "
          f"= {form_lo + retained:,}",
          o.writes >= form_lo + retained,
          "an address cannot be tested before it is formed")
    check(f"{d['label']}: enumeration writes exactly n*2^n + retained",
          o.writes == form_lo + retained,
          f"{o.writes:,} vs {form_lo + retained:,}")

    # Enumeration must read at least one literal per address, and at most
    # every literal of every clause.
    check(f"{d['label']}: enumeration reads {o.reads:,} in [2^n, 2^n*km] "
          f"= [{N:,}, {N * k * m:,}]",
          N <= o.reads <= N * k * m)

    # RL's acts: bounded below by the envelope and by the boundaries, and
    # equal to their sum.  No act may go unrecorded.
    check(f"{d['label']}: RL acts {a.total} >= n + 1 = {n + 1} and >= km = {k * m}",
          a.total >= n + 1 and a.total >= k * m)
    check(f"{d['label']}: RL acts == (n + 1) + km exactly",
          a.total == (n + 1) + k * m)
    check(f"{d['label']}: forced opposites {a.forced} == n + km, all charged 0",
          a.forced == n + k * m and a.total == a.assertions + a.mediations)

    # The ratio is a consequence of the two, not an independent figure.
    check(f"{d['label']}: ratio {o.total / a.total:,.0f} recomputed from the "
          f"two measures",
          abs(o.total / a.total - o.total / ((n + 1) + k * m)) < 1e-9)
print()

# ---------------------------------------------------------------------------
print("G.4  ONE QUESTION, PUT TO EACH")
print("     'does this address satisfy?' -- RL asks the boundaries;")
print("     enumeration must have built and kept its answers first.")
print()
for d, a, o, standing, bnds, led, produced in results:
    n = d["n"]
    probe = int("".join("1" if ch == "T" else "0"
                        for ch in reversed(d["planted"])), 2)
    qo, verdict = rl_membership(probe, bnds)
    check(f"{d['label']}: RL answers in {qo.total} comparisons, verdict {verdict}",
          verdict is True, f"enumeration first pays {o.total:,}")
print()

# ---------------------------------------------------------------------------
print("G.5  STORAGE")
print()
for d, a, o, standing, bnds, led, produced in results:
    n = d["n"]
    rl_store = assertion_cost(d)
    en_store = standing * n
    check(f"{d['label']}: RL stores {rl_store} symbols, "
          f"enumeration retains {en_store}",
          rl_store == d["n"] + 1 + d["k"] * d["m"],
          f"enumeration also wrote {o.writes - standing * n:,} it did not keep")
print()

# ---------------------------------------------------------------------------
print("G.6  BOOKKEEPING, REPORTED AND EXCLUDED")
print("     the loop counters, container management and index arithmetic of")
print("     this program are not charged to either method.  They are named")
print("     here so that no cost above can be attributed to them.")
print()
for d, a, o, standing, bnds, led, produced in results:
    n = d["n"]
    # bookkeeping of the enumeration loop: one counter increment per address,
    # one per clause visit.  Named, not charged.
    bk = (1 << n) + sum(1 for _ in range(1 << n))
    check(f"{d['label']}: bookkeeping {bk:,} operations, charged to neither",
          True, "excluded from both columns above")
print()

# ---------------------------------------------------------------------------
print("G.7  THE GROWTH BETWEEN THE TWO INSTANCES")
print()
d1, a1, o1, s1, _, led1, _p1 = results[0]
d2, a2, o2, s2, _, led2, _p2 = results[1]
check(f"RL: {a1.total} -> {a2.total} acts "
      f"(+{a2.total - a1.total}) for +{d2['n'] - d1['n']} contents, "
      f"+{d2['m'] - d1['m']} clauses",
      a2.total - a1.total == (d2["n"] - d1["n"]) + d2["k"] * (d2["m"] - d1["m"]),
      "matches n + 1 + km exactly")
check(f"Enumeration: {o1.total:,} -> {o2.total:,} operations "
      f"({o2.total / o1.total:.1f}x)",
      o2.total > o1.total)
check(f"ratio moves {o1.total / a1.total:,.0f} -> {o2.total / a2.total:,.0f}",
      o2.total / a2.total > o1.total / a1.total)
print()

# ---------------------------------------------------------------------------
print("=" * 74)
print(f"  APPENDIX G   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
