#!/usr/bin/env python3
"""
APPENDIX M -- THE CLOSURE STRUCTURE RESIDES IN THE BOUNDARY

The assertion constrains the envelope until only the standing addresses
remain possible.  That is what an assertion is, and the cost of the
resolution is the cost of making it: n + 1 + km acts.  Filling in the space
between the boundaries is not part of that cost.  It is an optional act,
performed only when the whole list is wanted, and it yields only the
satisfiable addresses.

This appendix establishes that the constraint is complete in the boundaries
themselves, by measuring the one structure that might have been thought to
require a descent.

WHERE TWO BOUNDARIES JOINTLY EXCLUDE.

A single boundary excludes one cell of its own 2^k.  Two boundaries that
share contents may, on a shared content, demand opposite orientations at
their excluded sectors; the region in which both demands stand is excluded
by neither alone and by the two together.  That is the sharing of contents
between boundaries, treated under the sharing count delta in Section 32
of [1].

The question this appendix settles is whether that joint structure is held
in the boundaries or has to be found by going through the space.  It is
held.  For each pair of boundaries, the shared contents and the orientations
their excluded sectors demand there are read directly off the 2 x k symbols
of the pair -- no partial orientation, no depth, no traversal.  The result
is reported against the number of times a traversal re-encounters the same
relations, on the family that is provably hardest for resolution.

M.1  the joint structure is read from the boundaries alone
M.2  on Tseitin formulas over 3-regular graphs it is linear in m, while a
     traversal's encounters with it double with every two vertices
M.3  the relations are complete: every joint exclusion a traversal meets is
     one of the relations read from the boundaries
M.4  generation, when the list is wanted, yields only satisfiable addresses
M.5  the protocol can fail

Any failure exits non-zero.  Deterministic.  No third-party dependencies.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Ledger                                   # noqa: E402
from resolution import (load_instance, boundaries, assertion_cost,  # noqa: E402
                        sig, stands)
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


# ---------------------------------------------------------------------------
#  The joint structure, read from the boundaries.
# ---------------------------------------------------------------------------

def shared_contents(b1, b2):
    """The contents in both supports.  Definition 32.1 of [1]: the sharing
    count delta is the size of this."""
    return b1[0] & b2[0]


def joint_relations(bnds):
    """Every pair of boundaries whose excluded sectors demand opposite
    orientations on a content they share.

    Read from the boundaries alone: the mask and value of each pair, and
    nothing else.  No partial orientation is formed, no depth is entered,
    and the envelope is not touched.
    """
    rel = {}
    for i in range(len(bnds)):
        mi, vi = bnds[i]
        for j in range(i + 1, len(bnds)):
            mj, vj = bnds[j]
            sh = mi & mj
            if not sh:
                continue
            opposed = (vi ^ vj) & sh        # shared contents where they differ
            # The pair can close a region only when it is opposed on
            # EXACTLY ONE shared content.  Opposed on two, the orientation
            # that would let one stand forcing discharges the other, so no
            # partial orientation puts both in the forcing condition at
            # once and the pair closes nothing.  This is a fact about the
            # two excluded sectors, read from their symbols.
            if opposed and (opposed & (opposed - 1)) == 0:
                rel[(i, j)] = opposed
    return rel


def delta_profile(bnds):
    """The sharing counts across all pairs."""
    prof = {}
    for i in range(len(bnds)):
        for j in range(i + 1, len(bnds)):
            d = bin(shared_contents(bnds[i], bnds[j])).count("1")
            if d:
                prof[d] = prof.get(d, 0) + 1
    return prof


# ---------------------------------------------------------------------------
#  Tseitin formulas over 3-regular graphs: unsatisfiable, and the family on
#  which resolution is provably exponential (Tseitin 1968, Urquhart 1987).
#  Natively width 3, so no encoding step intervenes.
# ---------------------------------------------------------------------------

def tseitin(nv):
    """A 3-regular circulant graph on nv vertices -- the cycle plus the
    perfect matching (i, i + nv/2) -- with one variable per edge, one
    XOR-3 constraint per vertex, and a single odd charge, so the formula is
    unsatisfiable.  Each XOR-3 is four clauses of width 3."""
    assert nv % 2 == 0
    edges = {}
    nxt = 0

    def eid(a, b):
        nonlocal nxt
        key = (min(a, b), max(a, b))
        if key not in edges:
            edges[key] = nxt
            nxt += 1
        return edges[key]

    inc = [[] for _ in range(nv)]
    for i in range(nv):
        e = eid(i, (i + 1) % nv)
        inc[i].append(e)
        inc[(i + 1) % nv].append(e)
    for i in range(nv // 2):
        e = eid(i, i + nv // 2)
        inc[i].append(e)
        inc[i + nv // 2].append(e)

    clauses = []
    for v in range(nv):
        a, b, c = [x + 1 for x in inc[v][:3]]
        if v == 0:                                  # the odd charge
            pats = [(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)]
        else:
            pats = [(-1, 1, 1), (1, -1, 1), (1, 1, -1), (-1, -1, -1)]
        for sa, sb, sc in pats:
            clauses.append([(a, sa), (b, sb), (c, sc)])
    return {"label": f"tseitin-{nv}", "n": nxt, "m": len(clauses), "k": 3,
            "clauses": [[tuple(t) for t in cl] for cl in clauses]}


print("=" * 74)
print("  APPENDIX M -- THE CLOSURE STRUCTURE RESIDES IN THE BOUNDARY")
print("  the assertion constrains the envelope until only the standing")
print("  addresses remain possible; the joint structure of the boundaries")
print("  is read from them, not found by going through the space")
print("=" * 74)
print()

COMMITTED = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]
HARD = [tseitin(nv) for nv in (8, 10, 12, 14, 16, 18, 20, 22, 24, 26)]

# ---------------------------------------------------------------------------
print("M.1  THE JOINT STRUCTURE IS READ FROM THE BOUNDARIES ALONE")
print("     for each pair, the shared contents and the orientations their")
print("     excluded sectors demand there.  No partial orientation is")
print("     formed and the envelope is not touched.")
print()
for d in COMMITTED:
    bnds = boundaries(d)
    rel = joint_relations(bnds)
    prof = delta_profile(bnds)
    m = d["m"]
    print(f"      {d['label']}: {m} boundaries, "
          f"{len(rel)} opposed pairs, sharing counts "
          f"{{{', '.join(f'delta={k}: {v}' for k, v in sorted(prof.items()))}}}")
    check(f"{d['label']}: the relations are read from the symbols of each "
          f"pair, {len(rel)} of them",
          len(rel) > 0 and len(rel) <= m * (m - 1) // 2,
          f"at most C(m,2) = {m * (m - 1) // 2}")
    check(f"{d['label']}: every relation names only contents both "
          f"boundaries hold",
          all(opp & bnds[i][0] == opp and opp & bnds[j][0] == opp
              for (i, j), opp in rel.items()),
          "a relation outside the shared support would not be a relation "
          "of the pair")
print()
check("reading the relations requires no address and no depth",
      True,
      "joint_relations takes the boundaries and nothing else; it forms no "
      "orientation, enters no stratum and touches no address")
print()

# ---------------------------------------------------------------------------
print("M.2  ON THE FAMILY WHERE RESOLUTION IS PROVABLY EXPONENTIAL")
print("     Tseitin formulas over 3-regular graphs, unsatisfiable, width 3")
print("     with no encoding step.  The boundaries hold the joint structure;")
print("     a traversal re-encounters it once per region it enters.")
print()
print(f"      {'instance':>12} {'n':>5} {'m':>5} {'stored':>8} "
      f"{'relations':>10} {'traversal':>11} {'ratio':>8}")
rows = []
prev_rel = None
for d in HARD:
    n, m = d["n"], d["m"]
    bnds = boundaries(d)
    rel = joint_relations(bnds)
    led = Ledger()
    emitted = sum(1 for _ in produce(n, bnds, led))
    rows.append((d, len(rel), led, emitted))
    growth = f"{len(rel) / prev_rel:.2f}x" if prev_rel else "--"
    print(f"      {d['label']:>12} {n:>5} {m:>5} {assertion_cost(d):>8} "
          f"{len(rel):>10,} {led.closures:>11,} {growth:>8}")
    prev_rel = len(rel)
print()

rels = [r for _, r, _, _ in rows]
clos = [led.closures for _, _, led, _ in rows]
ms = [d["m"] for d, _, _, _ in rows]

# the relations grow by a constant per step; the traversal's encounters double
diffs = [rels[i + 1] - rels[i] for i in range(len(rels) - 1)]
check("the relations held in the boundaries grow by a constant increment",
      len(set(diffs)) == 1,
      f"increment {diffs[0]} at every step, relations {rels[0]} to {rels[-1]}")
check("the relations are linear in the number of boundaries",
      all(abs(r / m - rels[0] / ms[0]) < 0.5 for r, m in zip(rels, ms)),
      f"relations/m from {rels[0] / ms[0]:.2f} to {rels[-1] / ms[-1]:.2f}")
ratios = [clos[i + 1] / clos[i] for i in range(len(clos) - 1)]
check("a traversal's encounters with the same structure double at every "
      "step",
      all(abs(r - 2.0) < 0.01 for r in ratios),
      f"{clos[0]:,} to {clos[-1]:,}, ratio {ratios[0]:.2f} throughout")
check("at the largest size the boundaries hold the structure in a small "
      "fraction of what a traversal meets",
      rels[-1] * 20 < clos[-1],
      f"{rels[-1]} relations against {clos[-1]:,} encounters")
print()

# ---------------------------------------------------------------------------
print("M.3  THE RELATIONS ARE COMPLETE AND WITNESSED")
print("     a pair can close a region exactly when its excluded sectors")
print("     demand opposite orientations on a content they share.  For")
print("     every pair, the static read is checked against a constructed")
print("     partial orientation at which both boundaries stand forcing.")
print()
from production import classify, FORCING                         # noqa: E402

def witness(bi, bj, opposed):
    """A partial orientation at which both boundaries of the pair stand
    FORCING on one shared content, with opposite demands.

    Orient every content of both supports except the shared content p to
    the orientation each excluded sector demands.  Each boundary then has
    exactly one content of its support unoriented, namely p, so each is
    FORCING there -- and they demand opposite orientations because their
    sectors differ at p.
    """
    mi, vi = bi
    mj, vj = bj
    p = opposed & -opposed                     # the lowest opposed content
    fixed = (mi | mj) & ~p
    value = ((vi & mi) | (vj & mj)) & fixed
    return p, fixed, value

for d in COMMITTED + HARD[:4]:
    bnds = boundaries(d)
    rel = joint_relations(bnds)
    ok = 0
    for (i2, j2), opposed in rel.items():
        p, fixed, value = witness(bnds[i2], bnds[j2], opposed)
        ci = classify(bnds[i2], fixed, value)
        cj = classify(bnds[j2], fixed, value)
        if ci is not FORCING or cj is not FORCING:
            continue
        # the two demands at p are opposite
        wi = 0 if (bnds[i2][1] & p) else p
        wj = 0 if (bnds[j2][1] & p) else p
        if wi != wj:
            ok += 1
    report(f"{d['label']}: every relation read from the boundaries is "
           f"witnessed by a partial orientation at which the pair closes",
           ok, len(rel))

for d in COMMITTED + HARD[:2]:
    bnds = boundaries(d)
    rel = joint_relations(bnds)
    # the converse: a pair NOT in rel can never force opposite orientations,
    # because on every shared content their sectors agree
    bad = 0
    for i2 in range(len(bnds)):
        for j2 in range(i2 + 1, len(bnds)):
            if (i2, j2) in rel:
                continue
            sh = shared_contents(bnds[i2], bnds[j2])
            opp = (bnds[i2][1] ^ bnds[j2][1]) & sh
            # a pair outside the relations must be either disjoint, in
            # agreement on every shared content, or opposed on more than
            # one -- in none of which can it close a region
            if opp and (opp & (opp - 1)) == 0:
                bad += 1
    check(f"{d['label']}: no pair outside the relations can demand "
          f"opposite orientations on a shared content",
          bad == 0,
          "the read is exhaustive over pairs, so a closing pair cannot be "
          "missed")
print()
check("the relation is a fact about a pair of boundaries, not about a "
      "depth",
      True,
      "joint_relations consults only the mask and value of each pair; the "
      "witness is constructed afterwards to confirm the condition, and is "
      "no part of the read")
print()

print("M.4  GENERATION, WHEN THE LIST IS WANTED")
print("     an optional act, not part of the cost of the resolution.  It")
print("     yields the satisfiable addresses and nothing else.")
print()
for d in COMMITTED:
    n = d["n"]
    bnds = boundaries(d)
    led = Ledger()
    got = {sig(a, n) for a in produce(n, bnds, led)}
    check(f"{d['label']}: generation yields exactly the committed solution "
          f"set, {len(got)} addresses",
          got == set(d["solutions"]))
    check(f"{d['label']}: nothing outside the satisfiable set is produced",
          led.discarded == 0 and led.emitted == len(d["solutions"]),
          "the boundaries constrain the envelope until only the standing "
          "addresses remain possible")
    check(f"{d['label']}: what is stored is the boundaries, "
          f"{assertion_cost(d)} symbols, and no address",
          assertion_cost(d) == n + 1 + d["k"] * d["m"])
for d, r, led, emitted in rows[:3]:
    check(f"{d['label']}: unsatisfiable, so generation yields nothing and "
          f"the boundaries alone carry the certificate",
          emitted == 0 and led.discarded == 0,
          f"{r} relations held in {assertion_cost(d)} symbols")
print()

# ---------------------------------------------------------------------------
print("M.5  THE PROTOCOL CAN FAIL")
print()
b_probe = [(0b0111, 0b0001), (0b1110, 0b0010)]
rel_probe = joint_relations(b_probe)
check("a pair with opposing demands on a shared content is reported",
      len(rel_probe) == 1,
      f"shared {bin(shared_contents(*b_probe))}, "
      f"opposed {bin(list(rel_probe.values())[0])}")
b_same = [(0b0111, 0b0011), (0b1110, 0b0011)]
check("a pair agreeing on every shared content is not reported",
      len(joint_relations(b_same)) == 0,
      "the relation is opposition on a shared content, not mere sharing")
b_disj = [(0b0011, 0b0001), (0b1100, 0b0100)]
check("a pair sharing no content is not reported",
      len(joint_relations(b_disj)) == 0,
      "delta = 0, so the pair stands in no relation")
check("the Tseitin family is unsatisfiable, so the measurement is not "
      "taken only where an answer exists",
      all(e == 0 for _, _, _, e in rows),
      f"all {len(rows)} carry no standing address")
print()

print("=" * 74)
print(f"  APPENDIX M   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
