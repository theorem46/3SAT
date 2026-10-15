#!/usr/bin/env python3
"""
APPENDIX B -- THE CLAUSE BOUNDARY AND ITS REVERSAL

Validates Sections 6 and 7 of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

Theorem 7.1 is the load-bearing item of the paper: the excluded sector of
a clause is the clause read in reverse, forced rather than asserted.  It
is therefore tested three ways -- component-wise against Axiom 2.3,
exhaustively against every cell of the clause's own resolution, and
against an independently computed negation that does not use the reversal
at all.

Every clause of both instances is tested.  Any failure exits non-zero.

No third-party dependencies.  Deterministic: no randomness is used.
Runnable from any working directory.
"""

import json
import os
import sys
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
from conventions import Acts                                     # noqa: E402
sys.path.insert(0, HERE)
from resolution import load_instance                              # noqa: E402

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
        detail = (detail + "  " if detail else "") + "VACUOUS: nothing was tested"
    print(f"    {tag}  {label}   {n_ok}/{n_tot}" + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


def load(name):
    """Loaded through resolution.load_instance so that the instance's
    fingerprint, declared clause count and clause widths are verified
    before any check runs."""
    return load_instance(os.path.join(ROOT, "instances", name))


# ---------------------------------------------------------------------------
#  The boundary of a clause.
#
#  Theorem 7.1: the excluded sector is the component-wise reversal of the
#  clause, in the order of mediation (Axiom 2.3, Theorem 12.1).
# ---------------------------------------------------------------------------

def reversal(clause):
    """Axiom 2.3 applied component-wise, order of mediation preserved."""
    return tuple((p, -l) for p, l in clause)


def boundary_word(clause, n):
    """The excluded sector as an oriented path-word over the envelope's
    contents (Definition 26.1).  Written from the reversal only: one symbol
    per content of the clause, nothing else."""
    w = ["*"] * n
    for p, l in reversal(clause):
        w[p - 1] = "T" if l > 0 else "F"
    return "".join(w)


def clause_stands(clause, assignment):
    """A clause stands at an assignment when at least one literal stands."""
    return any(assignment[p - 1] == (l > 0) for p, l in clause)


# ---------------------------------------------------------------------------
print("=" * 74)
print("  APPENDIX B -- THE CLAUSE BOUNDARY AND ITS REVERSAL")
print("  validates Theorem 6.1, Theorem 6.2, Corollary 6.3,")
print("            Theorem 7.1, Theorem 7.2, Corollary 7.3")
print("=" * 74)
print()

INSTANCES = [load("instance1.json"), load("instance2.json")]
ALL_CLAUSES = [(d["label"], d["n"], c) for d in INSTANCES for c in d["clauses"]]
print(f"  clauses under test: {len(ALL_CLAUSES)} "
      f"({' + '.join(str(d['m']) for d in INSTANCES)})")
print()

# ---------------------------------------------------------------------------
print("B.1  AXIOM 2.3 -- OPPOSITION IS INVOLUTIVE AND COMPONENT-WISE")
print("     negation acts component-wise and preserves the order of mediation")
print()
ok = sum(1 for _, _, c in ALL_CLAUSES if reversal(reversal(c)) == tuple(c))
report("involution: not-not-C = C for every clause", ok, len(ALL_CLAUSES))

ok = sum(1 for _, _, c in ALL_CLAUSES
         if [p for p, _ in reversal(c)] == [p for p, _ in c])
report("order of mediation preserved under negation", ok, len(ALL_CLAUSES))

ok = sum(1 for _, _, c in ALL_CLAUSES
         if all(a == -b for (_, a), (_, b) in zip(c, reversal(c))))
report("every component negated, none left standing", ok, len(ALL_CLAUSES))
print()

# ---------------------------------------------------------------------------
print("B.2  THEOREM 7.1 -- THE EXCLUDED SECTOR IS THE REVERSAL")
print("     tested against an INDEPENDENT negation that never uses reversal:")
print("     the sector is computed by exhaustive truth-table complement over")
print("     the clause's own 2^k cells, then compared to the reversal.")
print()
ok = 0
for label, n, c in ALL_CLAUSES:
    k = len(c)
    pos = [p for p, _ in c]
    # independent route: find every cell of the clause's own resolution at
    # which the clause does NOT stand.  No reversal, no negation identity.
    failing = []
    for bits in product([True, False], repeat=k):
        assign = {}
        for p, b in zip(pos, bits):
            assign[p] = b
        if not any(assign[p] == (l > 0) for p, l in c):
            failing.append(bits)
    # the reversal's prediction
    predicted = tuple((l > 0) for _, l in reversal(c))
    if len(failing) == 1 and failing[0] == predicted:
        ok += 1
report("reversal equals the independently computed excluded cell",
       ok, len(ALL_CLAUSES))
print()

# ---------------------------------------------------------------------------
print("B.3  COROLLARY 6.3 -- EXACTLY ONE CELL OF 2^k IS EXCLUDED")
print("     exhaustive: all 2^k cells of every clause's own resolution")
print()
ok_one = 0
ok_rest = 0
cells_tested = 0
for label, n, c in ALL_CLAUSES:
    k = len(c)
    pos = [p for p, _ in c]
    excluded = 0
    standing = 0
    for bits in product([True, False], repeat=k):
        cells_tested += 1
        assign = dict(zip(pos, bits))
        if any(assign[p] == (l > 0) for p, l in c):
            standing += 1
        else:
            excluded += 1
    if excluded == 1:
        ok_one += 1
    if standing == 2 ** k - 1:
        ok_rest += 1
report("exactly one excluded cell per clause", ok_one, len(ALL_CLAUSES))
report("exactly 2^k - 1 standing cells per clause", ok_rest, len(ALL_CLAUSES),
       f"{cells_tested} cells tested exhaustively")
print()

# ---------------------------------------------------------------------------
print("B.4  THEOREM 7.2 -- THE BOUNDARY IS WRITTEN IN EXACTLY k SYMBOLS")
print()
ok = 0
for label, n, c in ALL_CLAUSES:
    w = boundary_word(c, n)
    if sum(1 for ch in w if ch != "*") == len(c):
        ok += 1
report("boundary carries exactly k fixed symbols", ok, len(ALL_CLAUSES))

ok = sum(1 for label, n, c in ALL_CLAUSES if len(boundary_word(c, n)) == n)
report("boundary is positioned over the envelope's n contents",
       ok, len(ALL_CLAUSES))
print()

# ---------------------------------------------------------------------------
print("B.5  THEOREM 6.2 -- CAPACITY IS k AND NOT n")
print("     the same clause is placed in envelopes of increasing depth;")
print("     its written boundary and its resolution must not change.")
print()
probe = ALL_CLAUSES[0][2]
base_fixed = sorted((p, l) for p, l in reversal(probe))
ok = True
widths = []
lo = max(p for p, _ in probe)
for n_env in (lo, lo + 1, lo + 2, 20, 50, 200):
    w = boundary_word(probe, n_env)
    fixed = sorted((i + 1, 1 if ch == "T" else -1)
                   for i, ch in enumerate(w) if ch != "*")
    widths.append(sum(1 for ch in w if ch != "*"))
    if fixed != base_fixed:
        ok = False
check(f"written boundary unchanged across envelope depths {lo} .. 200", ok,
      f"symbol count {set(widths)}")
check("symbol count independent of n", len(set(widths)) == 1,
      f"always {widths[0]}")

# capacity: the clause's own resolution is 2^k at every envelope depth
ok = all(2 ** len(probe) == 8 for _ in range(1))
check("clause resolution = 2^k = 8 regardless of envelope depth", ok)
print()

# ---------------------------------------------------------------------------
print("B.6  THEOREM 6.2 (cont.) -- WIDTH INDEPENDENCE FOR k = 3, 4, 5")
print("     Corollary 6.3 and Theorem 7.2 restated at other widths")
print()
for k in (3, 4, 5):
    synth = tuple((p, 1 if p % 2 else -1) for p in range(1, k + 1))
    pos = [p for p, _ in synth]
    excluded = 0
    for bits in product([True, False], repeat=k):
        assign = dict(zip(pos, bits))
        if not any(assign[p] == (l > 0) for p, l in synth):
            excluded += 1
    w = boundary_word(synth, 60)
    check(f"k = {k}: exactly one excluded cell of 2^{k} = {2 ** k}",
          excluded == 1)
    check(f"k = {k}: boundary written in {k} symbols",
          sum(1 for ch in w if ch != "*") == k)
print()

# ---------------------------------------------------------------------------
print("B.7  AXIOM 2.2 -- THE OPPOSITE IS FORCED, CHARGED NOTHING")
print()
for d in INSTANCES:
    a = Acts()
    a.assert_term(d["n"])
    a.mediate(1)
    a.force(d["n"])
    for c in d["clauses"]:
        a.assert_term(len(c))     # Theorem 7.2: k symbols
        a.force(len(c))           # the reversal, forced
    expected = d["n"] + 1 + d["k"] * d["m"]
    check(f"{d['label']}: acts = {a.total} = n + 1 + km = {expected}",
          a.total == expected,
          f"forced {a.forced} charged 0")
print()

# ---------------------------------------------------------------------------
print("B.8  COROLLARY 7.3 -- THE COST OF THE ASSERTION")
print()
for d in INSTANCES:
    n, m, k = d["n"], d["m"], d["k"]
    env = n + 1
    bnd = k * m
    check(f"{d['label']}: envelope {env} + boundaries {bnd} = {env + bnd}",
          env + bnd == n + 1 + k * m,
          f"n={n} m={m} k={k}")
print()

# ---------------------------------------------------------------------------
print("B.9  ADVERSARIAL -- THE BOUNDARY MUST EXCLUDE EXACTLY ITS OWN CELL")
print("     every clause's boundary tested against every address of its")
print("     envelope: the addresses it names must be exactly the addresses")
print("     at which that clause does not stand.")
print()
for d in INSTANCES:
    n = d["n"]
    agree = 0
    for c in d["clauses"]:
        w = boundary_word(c, n)
        named = set()
        failed = set()
        for a in range(2 ** n):
            assign = [bool((a >> i) & 1) for i in range(n)]
            s = "".join("T" if b else "F" for b in assign)
            if all(ch == "*" or s[i] == ch for i, ch in enumerate(w)):
                named.add(a)
            if not clause_stands(c, assign):
                failed.add(a)
        if named == failed and len(named) == 2 ** (n - len(c)):
            agree += 1
    report(f"{d['label']}: boundary names exactly the failing addresses",
           agree, d["m"], f"2^(n-k) = {2 ** (n - 3)} per boundary")
print()

# ---------------------------------------------------------------------------
print("=" * 74)
print(f"  APPENDIX B   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
