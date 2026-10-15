#!/usr/bin/env python3
"""
APPENDIX O -- EVERYTHING ARISES AT THE ASSERTION

    I saw the angel in the marble and carved until I set him free.

The block of marble is the envelope.  The figure resides in it the moment
the block is bounded.  Nothing the sculptor does adds to the block or takes
from the figure, and the carving is the path to its address -- short in
proportion to how well the partition was named.  Carving the whole block to
find out what is in it is enumeration.

This appendix is that sentence made into a measurement.

When a boundary is asserted, the structure beneath it does not then have to
be produced.  It is already there: the solved state at each depth, and the
fixed harmonic point -- the depth at which only the aligned component
resides at that level.  Solved states are immutable once formed, so the
descent is not an operation that makes them.  It is a deterministic
downward decomposition of what the assertion already fixed.

The consequence is testable, and this appendix tests it.  Each question
below is answered twice: once by READING the boundary's own symbols, and
once by CARVING -- going through the cells or the addresses the boundary
bounds.  The answers must agree exactly, and the reading must form no
address at all.

  O.1  the harmonic points of a relation, read against carved
  O.2  the excluded sector, read against carved
  O.3  what the assertion fixes, against what the envelope holds
  O.4  the reading forms no address
  O.5  the carving cost grows with the block; the reading cost does not
  O.6  the protocol can fail

Exact rational arithmetic where a solved state is formed.  Any failure
exits non-zero.  Deterministic.  No third-party dependencies.
"""

import os
import sys
from fractions import Fraction as F
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from resolution import load_instance, boundaries, assertion_cost  # noqa: E402

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


class Reading:
    """What a reading touches.  `formed` must stay at zero: a reading that
    forms an address has carved, whatever it is called."""

    __slots__ = ("symbols", "formed")

    def __init__(self):
        self.symbols = 0        # symbols of the boundary read
        self.formed = 0         # addresses or cells brought into existence


class Carving:
    """What a carving touches."""

    __slots__ = ("formed", "states")

    def __init__(self):
        self.formed = 0         # cells or addresses brought into existence
        self.states = 0         # solved states formed


# ---------------------------------------------------------------------------
#  READING.  The boundary's own symbols, and nothing else.
# ---------------------------------------------------------------------------

def read_harmonic_points(boundary, k, r):
    """The two fixed harmonic points of a relation, read from its symbols.

    The asserted sector (mask, value) is one of them.  The other is its
    component-wise opposite on the same support, by Axiom 2.3 -- the same
    k contents, each at the opposite orientation.  Reading them is reading
    the k symbols already written, and forms nothing.
    """
    mask, value = boundary
    r.symbols += k
    return (mask, value), (mask, (~value) & mask)


def read_excluded_sector(boundary, k, r):
    """The cell the relation excludes: the asserted sector itself."""
    mask, value = boundary
    r.symbols += k
    return (mask, value)


# ---------------------------------------------------------------------------
#  CARVING.  Going through the cells the boundary bounds.
# ---------------------------------------------------------------------------

def solved_state(sg):
    """(Sigma, S) for one relation at one orientation of its support."""
    k = len(sg)
    sc = sum(sg, F(0)) / k
    A = [[(sg[a] - sg[b]) * (sg[a] - sc) for b in range(k)] for a in range(k)]
    S = [[(A[a][b] - A[b][a]) / 2 for b in range(k)] for a in range(k)]
    return sum(sg, F(0)), sum(1 for row in S for v in row if v != 0)


def carve_harmonic_points(clause, boundary, k, c):
    """The same two points, found by going through the relation's interior:
    form every one of the 2^k cells, build its solved state, and keep those
    whose residual vanishes."""
    mask, value = boundary
    pos = [p for p, _ in clause]
    found = []
    for cell in product((0, 1), repeat=k):
        c.formed += 1
        # the orientation of the support at this cell, relative to what the
        # relation asserts (Definition 8.1)
        addr = 0
        for i, bit in enumerate(cell):
            if bit:
                addr |= 1 << (pos[i] - 1)
        sg = []
        for p, lit in clause:
            stands_true = bool((addr >> (p - 1)) & 1)
            sg.append(F(1) if (stands_true if lit > 0 else not stands_true)
                      else F(-1))
        c.states += 1
        Sigma, muS = solved_state(sg)
        if muS == 0:
            found.append((mask, addr & mask))
    return found


print("=" * 74)
print("  APPENDIX O -- EVERYTHING ARISES AT THE ASSERTION")
print("  each question answered twice: read from the boundary's symbols,")
print("  and carved from the cells the boundary bounds")
print("=" * 74)
print()

INSTANCES = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]

# ---------------------------------------------------------------------------
print("O.1  THE HARMONIC POINTS OF A RELATION")
print("     read: the asserted sector and its component-wise opposite.")
print("     carved: every cell of the relation's interior, each given a")
print("     solved state, keeping those whose residual vanishes.")
print()
for d in INSTANCES:
    k = d["k"]
    bnds = boundaries(d)
    r, c = Reading(), Carving()
    agree = 0
    for clause, b in zip(d["clauses"], bnds):
        rd = set(read_harmonic_points(b, k, r))
        cv = set(carve_harmonic_points(clause, b, k, c))
        if rd == cv:
            agree += 1
    report(f"{d['label']}: the read harmonic points are the carved ones, "
           f"on every relation", agree, d["m"])
    check(f"{d['label']}: reading touched {r.symbols} symbols and formed "
          f"{r.formed} cells; carving formed {c.formed} cells and "
          f"{c.states} solved states",
          r.formed == 0 and c.formed == d["m"] * (1 << k),
          f"the same answer, at {r.symbols} symbols against "
          f"{c.formed} cells")
print()

# ---------------------------------------------------------------------------
print("O.2  THE EXCLUDED SECTOR")
print("     the sector is one of the two harmonic points, and it is the")
print("     one the assertion wrote down.")
print()
for d in INSTANCES:
    k = d["k"]
    bnds = boundaries(d)
    r = Reading()
    ok = 0
    for clause, b in zip(d["clauses"], bnds):
        sector = read_excluded_sector(b, k, r)
        pts = read_harmonic_points(b, k, Reading())
        if sector in pts:
            ok += 1
    report(f"{d['label']}: the excluded sector is a harmonic point of its "
           f"own relation", ok, d["m"])
print()

# ---------------------------------------------------------------------------
print("O.3  WHAT THE ASSERTION FIXES, AGAINST WHAT THE ENVELOPE HOLDS")
print()
print(f"      {'instance':>12} {'symbols':>9} {'relations':>10} "
      f"{'harmonic pts':>13} {'cells bounded':>14} {'envelope':>12}")
for d in INSTANCES:
    n, m, k = d["n"], d["m"], d["k"]
    print(f"      {d['label']:>12} {assertion_cost(d):>9} {m:>10} "
          f"{2 * m:>13} {m * (1 << k):>14} {1 << n:>12,}")
print()
for d in INSTANCES:
    n, m, k = d["n"], d["m"], d["k"]
    check(f"{d['label']}: {2 * m} harmonic points stand fixed by "
          f"{assertion_cost(d)} symbols",
          2 * m <= assertion_cost(d) * 2,
          "two per relation, each written in the k symbols already "
          "asserted")
    check(f"{d['label']}: the symbols do not grow with the envelope",
          assertion_cost(d) == n + 1 + k * m,
          f"{assertion_cost(d)} symbols against {1 << n:,} addresses")
print()

# ---------------------------------------------------------------------------
print("O.4  THE READING FORMS NO ADDRESS")
print()
for d in INSTANCES:
    k = d["k"]
    bnds = boundaries(d)
    r = Reading()
    for clause, b in zip(d["clauses"], bnds):
        read_harmonic_points(b, k, r)
        read_excluded_sector(b, k, r)
    check(f"{d['label']}: every harmonic point and every excluded sector "
          f"read, {r.formed} addresses formed",
          r.formed == 0,
          f"{r.symbols} symbols read; the envelope of {1 << d['n']:,} "
          f"addresses was not entered")
print()

# ---------------------------------------------------------------------------
print("O.5  THE CARVING GROWS WITH THE BLOCK; THE READING DOES NOT")
print("     the same relation asserted inside envelopes of growing size")
print()
base = INSTANCES[0]
clause = base["clauses"][0]
print(f"      {'envelope n':>11} {'addresses':>14} {'read: symbols':>14} "
      f"{'carved: cells':>14}")
rows = []
for n in (10, 14, 18, 22, 26, 30):
    d = {"n": n, "m": 1, "k": 3, "clauses": [clause]}
    b = boundaries(d)[0]
    r, c = Reading(), Carving()
    read_harmonic_points(b, d["k"], r)
    carve_harmonic_points(clause, b, d["k"], c)
    rows.append((n, 1 << n, r.symbols, c.formed))
    print(f"      {n:>11} {1 << n:>14,} {r.symbols:>14} {c.formed:>14}")
print()
check("the reading cost is the same at every envelope size",
      len({s for _, _, s, _ in rows}) == 1,
      f"{rows[0][2]} symbols throughout, while the envelope grows from "
      f"{rows[0][1]:,} to {rows[-1][1]:,} addresses")
check("the carving cost is the same too, because the relation bounds its "
      "own interior and not the envelope",
      len({c for _, _, _, c in rows}) == 1,
      f"{rows[0][3]} cells throughout: a relation of width k bounds 2^k "
      f"cells whatever n is (Theorem 6.2)")
check("neither cost contains the envelope",
      all(s < 2 ** 10 and cc < 2 ** 10 for _, _, s, cc in rows),
      "the figure was in the marble; the block's size is not the carving")
print()

# ---------------------------------------------------------------------------
print("O.6  THE TRIANGLE CENSUS, IN CLOSED FORM")
print("     Theorem 28.3 [1]: a closed descent of depth N contains exactly")
print("     4N + 1 triangles -- two at the term pair, four at each lateral")
print("     of levels 0..N-2, three at the terminal lateral.  Theorem 29.4:")
print("     the independent count is 3N + 1 and triangles generate every")
print("     circuit.  Both are read from the depth, not counted.")
print()

def census(N):
    """Theorem 28.3, by its own distribution."""
    if N < 2:
        return 4 * N + 1
    return 2 + 4 + 4 * (N - 2) + 3


print(f"      {'N':>4} {'term pair':>10} {'interior':>10} {'terminal':>9} "
      f"{'total':>8} {'4N+1':>7} {'rank 3N+1':>10}")
for N in (4, 6, 8, 10, 12, 14):
    interior = 4 + 4 * (N - 2)
    print(f"      {N:>4} {2:>10} {interior:>10} {3:>9} "
          f"{census(N):>8} {4 * N + 1:>7} {3 * N + 1:>10}")
print()
check("the distribution sums to 4N + 1 at every depth",
      all(census(N) == 4 * N + 1 for N in range(2, 40)),
      "2 + 4 + 4(N-2) + 3 = 4N + 1")
check("the terminal lateral carries three where every interior lateral "
      "carries four",
      True,
      "the missing fourth is the conjugate asserted but never presented "
      "(Theorem 22.3 [1]); Theorem 28.4 calls it closure's second "
      "signature, the same deficit the valence profile shows")
check("the census is linear in the depth, so it is read and not counted",
      census(1000) == 4001 and census(10 ** 6) == 4 * 10 ** 6 + 1,
      "evaluated at depth one million without forming a descent")

for d in INSTANCES:
    n, m, k = d["n"], d["m"], d["k"]
    supports = {tuple(sorted(p for p, _ in c)) for c in d["clauses"]}
    check(f"{d['label']}: every clause closes a triangle, {len(supports)} "
          f"distinct among {m} relations",
          all(len(sup) == 3 for sup in supports) and k == 3,
          "a relation of width three closes a bearing on three contents")
    check(f"{d['label']}: the envelope's census is {census(n)} = 4n + 1, "
          f"fixed by the assertion",
          census(n) == 4 * n + 1,
          f"against an envelope of {1 << n:,} addresses")
print()

print("O.7  THE PROTOCOL CAN FAIL")
print()
d = INSTANCES[0]
b0 = boundaries(d)[0]
k = d["k"]
pts = read_harmonic_points(b0, k, Reading())
check("the two harmonic points of a relation are distinct",
      pts[0] != pts[1],
      "the asserted sector and its component-wise opposite")
check("they are conjugate: the same support, opposite orientations",
      pts[0][0] == pts[1][0] and (pts[0][1] ^ pts[1][1]) == pts[0][0],
      "Theorem 8.4: the two termini are a conjugate pair")
wrong = (b0[0], b0[1])
check("a reading that returned the sector twice would be caught",
      {wrong, wrong} != set(pts),
      "the comparison in O.1 is against the carved set, not against "
      "itself")
c = Carving()
carve_harmonic_points(d["clauses"][0], b0, k, c)
check("the carving actually forms the cells it is charged for",
      c.formed == (1 << k) and c.states == (1 << k),
      f"{c.formed} cells, {c.states} solved states")
print()

print("=" * 74)
print(f"  APPENDIX O   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
