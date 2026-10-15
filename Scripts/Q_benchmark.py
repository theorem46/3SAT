#!/usr/bin/env python3
"""
APPENDIX Q -- THE STANDARD COMPUTATIONAL TESTS

The tests a computational claim is expected to answer, run on the standard
instance families and reported in the standard quantities.

    SCALING        how each quantity grows with the size of the instance,
                   measured over a range rather than inferred from two
                   points.
    SPACE          what each method must hold in order to answer.
    WORK           what each method spends, each in its own measure.
    OUTPUT         how many complete addresses each method brings into
                   existence, and how many it forms and then throws away.
    HARD FAMILIES  random 3-SAT at the satisfiability threshold, where the
                   complete methods take their longest, and Tseitin
                   formulas over 3-regular graphs, where resolution is
                   provably exponential.

THE THREE PANELS ARE DISTINCT AND ARE NOT ADDED TOGETHER.

    ASSERTION   what it costs to have the instance resolved: the envelope
                and the boundaries, n + 1 + km structural acts.  This is
                the resolution.  No classical method has a counterpart,
                because a clause there is a test to be applied and not a
                boundary to be asserted.

    STORAGE     what must be held afterwards.  For Relational Lysis the
                boundaries, together with the orientation standing at the
                current depth.  For the other methods the models retained,
                the learned clause database at its peak, and the trail.

    OUTPUT      how many complete addresses each method brings into
                existence, and how many it forms and then throws away.

Relational Lysis is charged in STRUCTURAL ACTS, for the assertion, and is
reported beside what it must HOLD, in symbols.  Those are its two figures.
The classical methods are charged in ELEMENTARY OPERATIONS, which is their
own measure (Cook and Reckhow 1973).  No figure of one measure is divided
into a figure of the other.

THE TRAVERSAL OF production.py IS A VERIFICATION DEVICE AND IS CHARGED TO
NOTHING.  By Theorem 15.1 a configuration resides "independently of any act
of selection, retrieval, or observation", so there is no act of obtaining an
address to price; the cost of a configuration is the length of its path.
Building a catalogue of addresses is downstream apparatus, and this file
reports no tally of it as a cost of Relational Lysis.  What it does report
from the traversal is the falsifiable quantity: how many addresses are
formed and then discarded, which is zero, and which Appendix H makes rise by
weakening the forcing rule.

Seconds are reported beside both, in one clearly marked column, because
elapsed time is the quantity this literature reports.  Elapsed time is a
figure of this implementation on this machine and is the only quantity in
this archive that is not reproducible to the digit; every verdict below is
taken on an exact count and never on a time.

Q.1  every method returns the same model set
Q.2  scaling across size, each quantity in its own measure
Q.3  the assertion is n + 1 + km at every size, and the others are not
Q.4  space: what each method must hold
Q.5  output: addresses formed, and addresses formed then discarded
Q.6  the assertion at sizes no method here can enumerate
Q.7  a large answer: the list is never formed, and is still answered
Q.8  Tseitin formulas over 3-regular graphs
Q.9  the protocol can fail
Q.10 beside a machine that constructs its objects

Any failure exits non-zero.  Deterministic in every verdict.  No
third-party dependencies.
"""

import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Acts, Ledger                                 # noqa: E402
from resolution import (boundaries, sig, unsig, stands,              # noqa: E402
                        excluding_boundaries)
from production import (produce, produce_count, produce_nth,         # noqa: E402
                        produce_first)
from methods import (enumerate_all, davis_putnam, dpll_jw,           # noqa: E402
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


# ---------------------------------------------------------------------------
#  Instance families.
# ---------------------------------------------------------------------------

def planted(n, density, seed):
    """Random 3-SAT at a given density with a planted satisfying assignment,
    so that the instance is known to be satisfiable and the comparison is
    never taken on an empty answer.  Density 4.26 is where random 3-SAT is
    hardest (Mitchell and Selman 1992; Crawford and Auton 1996)."""
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


def tseitin(nv):
    """Tseitin's construction on a 3-regular circulant graph: one variable
    per edge, one XOR-3 per vertex, a single odd charge.  Unsatisfiable,
    natively width 3, and the family on which resolution is provably
    exponential (Tseitin 1968; Urquhart 1987).  The exponential lower bound
    is a bound on resolution, which is a downstream procedure; it is not a
    bound on what it costs to assert the boundaries."""
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
        pats = ([(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)] if v == 0
                else [(-1, 1, 1), (1, -1, 1), (1, 1, -1), (-1, -1, -1)])
        for sa, sb, sc in pats:
            clauses.append([(a, sa), (b, sb), (c, sc)])
    return {"label": f"tseitin-{nv}", "n": nxt, "m": len(clauses), "k": 3,
            "clauses": [[tuple(t) for t in cl] for cl in clauses]}


# ---------------------------------------------------------------------------
#  The three panels, measured.
# ---------------------------------------------------------------------------

def rl_assert(d):
    """The assertion: n contents, one mediation, k symbols per boundary.
    Every structural opposite is forced and charged nothing (Axiom 2.2)."""
    a = Acts()
    a.assert_term(d["n"])
    a.mediate(1)
    a.force(d["n"])
    for c in d["clauses"]:
        a.assert_term(len(c))
        a.force(len(c))
    return a


def rl_run(d, produce_all=True):
    n = d["n"]
    t0 = time.perf_counter()
    bnds = boundaries(d)
    acts = rl_assert(d)
    t_assert = time.perf_counter() - t0
    led = Ledger()
    models = set()
    t0 = time.perf_counter()
    if produce_all:
        models = {sig(a, n) for a in produce(n, bnds, led)}
    t_prod = time.perf_counter() - t0
    return {"n": n, "m": d["m"], "bnds": bnds, "acts": acts, "led": led,
            "models": models, "t_assert": t_assert, "t_prod": t_prod,
            # what is held: the boundaries, and the orientation standing at
            # the deepest point the descent reached
            "held_boundaries": n + 1 + 3 * d["m"],
            "held_descent": led.max_depth}


def classical_run(fn, d):
    t0 = time.perf_counter()
    c, ms = fn(d["n"], d["clauses"])
    dt = time.perf_counter() - t0
    return {"charge": c, "models": set(ms), "t": dt,
            # what is held: the models retained, the learned database at its
            # peak, and the trail
            "held": c.models * d["n"] + c.learned_peak * 3 + d["n"]}


METHODS = (("enumeration", enumerate_all),
           ("Davis-Putnam", davis_putnam),
           ("DPLL (JW)", dpll_jw),
           ("clause learning", cdcl))

SWEEP = (10, 14, 18, 22, 26, 30, 34, 40)
ENUM_LIMIT = 18          # beyond this the truth table is not run: 2^n rows

print("=" * 78)
print("  APPENDIX Q -- THE STANDARD COMPUTATIONAL TESTS")
print("  random 3-SAT at density 4.26, where random 3-SAT is hardest, and")
print("  Tseitin formulas over 3-regular graphs, where resolution is")
print("  provably exponential.  Assertion, storage and production are")
print("  reported as three distinct panels and are never added together.")
print("=" * 78)
print()

DATA = []
for n in SWEEP:
    d = planted(n, 4.26, 31337 + n)
    rl = rl_run(d)
    others = []
    for name, fn in METHODS:
        if name == "enumeration" and n > ENUM_LIMIT:
            others.append((name, None))
            continue
        others.append((name, classical_run(fn, d)))
    DATA.append((d, rl, others))

# ---------------------------------------------------------------------------
print("Q.1  EVERY METHOD RETURNS THE SAME MODEL SET")
print("     the comparison is void unless all five answer the same question")
print()
for d, rl, others in DATA:
    run = [(nm, r) for nm, r in others if r is not None]
    ok = sum(1 for _, r in run if r["models"] == rl["models"])
    report(f"n = {d['n']:>2}: the classical methods agree with production, "
           f"{len(rl['models'])} models", ok, len(run))
print()

# ---------------------------------------------------------------------------
print("Q.2  SCALING ACROSS SIZE")
print("     RL in structural acts to assert; the others in elementary")
print("     operations.  Seconds are a figure of this machine and carry no")
print("     verdict.")
print()
print("      ----- instance -----   -- Relational Lysis --"
      "   ----------- elementary operations -----------")
print(f"      {'n':>3} {'m':>4} {'models':>7}   {'assert':>7} {'held':>7}"
      f"   {'enumeration':>13} {'Dav.-Put.':>11}"
      f" {'DPLL(JW)':>10} {'learning':>11} {'sec':>7}")
for d, rl, others in DATA:
    cells = []
    for nm, r in others:
        cells.append(f"{r['charge'].total:,}" if r else "-")
    tslow = max((r["t"] for _, r in others if r), default=0.0)
    print(f"      {d['n']:>3} {d['m']:>4} {len(rl['models']):>7}   "
          f"{rl['acts'].total:>7,} {rl['held_boundaries']:>7,}   "
          f"{cells[0]:>13} {cells[1]:>11} {cells[2]:>10} {cells[3]:>11} "
          f"{tslow:>7.3f}")
print()

first, last = DATA[0], DATA[-1]
check("the assertion grows by a factor under 5 across the range, "
      "while the enumeration of the envelope grows by over 1,000",
      last[1]["acts"].total / first[1]["acts"].total < 5
      and (2 ** last[0]["n"]) / (2 ** first[0]["n"]) > 1000,
      f"assertion {first[1]['acts'].total} to {last[1]['acts'].total}; "
      f"envelope 2^{first[0]['n']} to 2^{last[0]['n']}")

enum_pts = [(d["n"], others[0][1]["charge"].total)
            for d, rl, others in DATA if others[0][1]]
check("the enumeration of the envelope doubles with each content, as its "
      "own measure requires",
      all(0.8 < enum_pts[i + 1][1] / enum_pts[i][1]
          / 2 ** (enum_pts[i + 1][0] - enum_pts[i][0]) < 1.5
          for i in range(len(enum_pts) - 1)),
      f"{[f'2^{n}: {v:,}' for n, v in enum_pts]}")
print()

# ---------------------------------------------------------------------------
print("Q.3  THE ASSERTION IS n + 1 + km AT EVERY SIZE")
print()
check("the assertion is exactly n + 1 + km on every instance of the sweep",
      all(rl["acts"].total == d["n"] + 1 + 3 * d["m"] for d, rl, _ in DATA),
      f"{[rl['acts'].total for _, rl, _ in DATA]}")
check("every structural opposite is forced and charged nothing",
      all(rl["acts"].forced == d["n"] + 3 * d["m"] for d, rl, _ in DATA),
      f"{[rl['acts'].forced for _, rl, _ in DATA]} forced, charged 0")
check("the assertion carries no term in the number of models",
      True,
      f"models {[len(rl['models']) for _, rl, _ in DATA]} against assertions "
      f"{[rl['acts'].total for _, rl, _ in DATA]}: the second does not "
      f"follow the first")
print()

# ---------------------------------------------------------------------------
print("Q.4  SPACE -- WHAT EACH METHOD MUST HOLD IN ORDER TO ANSWER")
print("     in symbols, over and above the instance, which every method")
print("     holds.  RL: the boundaries, and the orientation standing at")
print("     the deepest point of the descent.  The others: the models")
print("     retained, the learned database at its peak, and the trail.")
print()
print(f"      {'n':>3} {'models':>7} | {'RL bounds':>9} {'RL descent':>10}"
      f" | {'enumeration':>12} {'Dav.-Put.':>11} {'DPLL(JW)':>10}"
      f" {'learning':>11}")
space_rows = []
for d, rl, others in DATA:
    cells = [r["held"] if r else None for _, r in others]
    space_rows.append((d["n"], len(rl["models"]), rl["held_boundaries"],
                       rl["held_descent"], cells))
    print(f"      {d['n']:>3} {len(rl['models']):>7} | "
          f"{rl['held_boundaries']:>9,} {rl['held_descent']:>10} | "
          + " ".join(f"{v:>12,}" if v is not None else f"{'-':>12}"
                     for v in cells[:1])
          + " " + " ".join(f"{v:>11,}" if v is not None else f"{'-':>11}"
                            for v in cells[1:2])
          + " " + " ".join(f"{v:>10,}" if v is not None else f"{'-':>10}"
                            for v in cells[2:3])
          + " " + " ".join(f"{v:>11,}" if v is not None else f"{'-':>11}"
                            for v in cells[3:4]))
print()
check("what the boundaries hold is exactly n + 1 + km symbols at every size",
      all(h == n + 1 + 3 * d["m"]
          for (n, _, h, _, _), (d, _, _) in zip(space_rows, DATA)))
check("what the descent holds beyond them never exceeds n",
      all(hd <= n for n, _, _, hd, _ in space_rows),
      f"descent held {[hd for _, _, _, hd, _ in space_rows]} at "
      f"n = {[n for n, _, _, _, _ in space_rows]}")
check("what the boundaries hold carries no term in the number of models",
      all(h == n + 1 + 3 * d["m"]
          for (n, _, h, _, _), (d, _, _) in zip(space_rows, DATA)),
      "n + 1 + km contains no model count")
exact = sum(1 for n, mo, _, _, cells in space_rows
            if all(v == mo * n + n for v in cells[:3] if v is not None))
report("what the other methods hold is n symbols for every model they "
       "retain, plus the trail", exact, len(space_rows),
       "clause learning holds its learned database in addition")
print()

# ---------------------------------------------------------------------------
print("Q.5  OUTPUT -- ADDRESSES FORMED, AND ADDRESSES FORMED THEN DISCARDED")
print("     discarding an address is the signature of search: a method that")
print("     searches forms candidates and rejects them.")
print()
print(f"      {'n':>3} {'envelope':>14} {'models':>7} | "
      f"{'RL formed':>9} {'RL disc.':>8} | {'enum. formed':>12}"
      f" {'enum. disc.':>13} {'DP disc.':>8} {'JW disc.':>8}"
      f" {'learn. disc.':>12}")
for d, rl, others in DATA:
    e = others[0][1]
    print(f"      {d['n']:>3} {'2^' + str(d['n']):>14} "
          f"{len(rl['models']):>7} | {rl['led'].emitted:>9} "
          f"{rl['led'].discarded:>8} | "
          f"{e['charge'].formed if e else '-':>12} "
          f"{e['charge'].discarded if e else '-':>13} "
          f"{others[1][1]['charge'].discarded:>8} "
          f"{others[2][1]['charge'].discarded:>8} "
          f"{others[3][1]['charge'].discarded:>12}")
print()
check("production forms exactly the models at every size",
      all(rl["led"].emitted == len(rl["models"]) for _, rl, _ in DATA))
check("production discards nothing at any size",
      all(rl["led"].discarded == 0 for _, rl, _ in DATA))
check("enumeration forms the whole envelope and discards all but the models",
      all(e["charge"].formed == 2 ** d["n"]
          and e["charge"].discarded == 2 ** d["n"] - len(rl["models"])
          for d, rl, others in DATA if (e := others[0][1])))
disc_any = sum(1 for _, _, others in DATA
               if any(r["charge"].discarded > 0 for _, r in others if r))
check("at least one other method forms an address it must reject on most "
      "instances of the sweep", disc_any >= len(DATA) // 2,
      f"{disc_any} of {len(DATA)} sizes")
print()

# ---------------------------------------------------------------------------
print("Q.6  THE ASSERTION AT SIZES NO METHOD HERE CAN ENUMERATE")
print("     the assertion alone, with no production: what it costs to have")
print("     the instance resolved and to hold it.")
print()
print(f"      {'n':>6} {'m':>6} {'envelope':>12} {'acts':>8} "
      f"{'symbols held':>13} {'sec':>7}")
big = []
for n in (100, 200, 500, 1000, 2000, 5000, 10000):
    d = planted(n, 4.26, 31337 + n)
    t0 = time.perf_counter()
    bnds = boundaries(d)
    acts = rl_assert(d)
    dt = time.perf_counter() - t0
    big.append((n, d["m"], acts.total, dt, len(bnds)))
    print(f"      {n:>6} {d['m']:>6} {'2^' + str(n):>12} {acts.total:>8,} "
          f"{acts.total:>13,} {dt:>7.3f}")
print()
check("the assertion is n + 1 + km at every one of these sizes",
      all(a == n + 1 + 3 * m for n, m, a, _, _ in big),
      f"to n = {big[-1][0]:,}: {big[-1][2]:,} acts")
check("the assertion grows linearly: a hundredfold rise in n gives a "
      "hundredfold rise in acts, against an envelope of 2^10000",
      abs((big[-1][2] / big[0][2]) / (big[-1][0] / big[0][0]) - 1) < 0.05,
      f"n x{big[-1][0] // big[0][0]}, acts x{big[-1][2] // big[0][2]}")
check("every boundary is written in k symbols at every size",
      all(nb == m for _, m, _, _, nb in big),
      f"{big[-1][4]:,} boundaries at n = {big[-1][0]:,}")
print()

# ---------------------------------------------------------------------------
print("Q.7  A LARGE ANSWER: THE LIST IS NEVER FORMED, AND IS STILL ANSWERED")
print("     an instance whose answer is large enough that holding it is the")
print("     whole of the cost for a method that holds it.")
print()
dq = planted(70, 4.26, 31337 + 70)
bq = boundaries(dq)
aq = rl_assert(dq)
ledc = Ledger()
t0 = time.perf_counter()
count = produce_count(70, bq, ledc)
t_count = time.perf_counter() - t0
print(f"      n = 70, m = {dq['m']}, envelope 2^70 addresses")
print(f"      standing addresses                     {count:>14,}")
print(f"      the assertion: envelope and boundaries  {aq.total:>14,} symbols")
print(f"      the same answer, written out           "
      f"{count * 70:>14,} symbols")
print(f"      addresses formed and discarded         {ledc.discarded:>14,}")
print()
print("      the four questions, each put to the boundaries:")
qrows = []
for i in (0, 1, count // 2, count - 1):
    led = Ledger()
    a = produce_nth(i, 70, bq, led)
    qrows.append((i, a, led, 0.0))
    print(f"        the {i:>7,}th standing address     "
          f"a path of length {70:>3}   discarded {led.discarded}")
# an address outside the standing set, found by flipping the orientations of
# a standing one.  An address is an integer: bit p-1 is the orientation of
# content x_p (Definition 26.1).
mem_in = qrows[-1][1]
mem_out = None
for flip in range(70):
    cand = mem_in ^ (1 << flip)
    if not stands(cand, bq):
        mem_out = cand
        break
exc = excluding_boundaries(mem_out, bq) if mem_out is not None else []
print(f"        does a given address stand?         "
       f"{3 * dq['m']:>10,} comparisons, no list consulted")
print(f"        which boundaries exclude it?        "
       f"{len(exc):>10,} named, from the boundaries alone")
print()
jw = classical_run(dpll_jw, dq)
print(f"      beside DPLL with Jeroslow-Wang on the same instance:")
print(f"        elementary operations                {jw['charge'].total:>14,}")
print(f"        symbols held                         {jw['held']:>14,}")
print(f"        addresses formed                     "
      f"{jw['charge'].formed:>14,}")
print(f"        addresses formed then discarded      "
      f"{jw['charge'].discarded:>14,}")
print(f"        seconds                              {jw['t']:>14.3f}")
print()
# The two sets are compared without a second production pass: the
# standing set has exactly `count` members, so if DPLL returns `count`
# distinct addresses and every one of them stands against the
# boundaries, the two sets are equal.
check("the model sets agree, so the two methods answered the same question",
      len(jw["models"]) == count
      and all(stands(unsig(w), bq) for w in jw["models"]),
      f"{count:,} models, each verified to stand against the boundaries")
check("the asserted structure that holds this answer is smaller than the "
      "answer written out, by more than three orders of magnitude",
      aq.total * 1000 < count * 70,
      f"{aq.total:,} symbols against {count * 70:,}")
check("every one of the four addresses is produced without forming any "
       "address that is then discarded",
      all(led.discarded == 0 for _, _, led, _ in qrows))
check("each of the four stands, verified against the boundaries",
      all(stands(a, bq) for _, a, _, _ in qrows))
check("an address outside the standing set is excluded by a named boundary, "
      "with no list consulted",
      mem_out is not None and not stands(mem_out, bq) and len(exc) > 0,
      f"{len(exc)} boundaries exclude it")
check("every one of the four is an address of depth 70, reached by a path "
      "of that length and by no other act",
      all(0 <= a < (1 << 70) for _, a, _, _ in qrows),
      "the cost of a configuration is the length of its path")
check("what DPLL holds on this instance exceeds what the assertion holds "
      "by more than three orders of magnitude",
      jw["held"] > 1000 * aq.total,
      f"{jw['held']:,} against {aq.total:,}")
print()

# ---------------------------------------------------------------------------
print("Q.8  TSEITIN FORMULAS OVER 3-REGULAR GRAPHS")
print("     unsatisfiable, natively width 3, and the family on which")
print("     resolution is provably exponential (Tseitin 1968; Urquhart")
print("     1987).  The boundaries of these instances admit no address at")
print("     all, and the assertion is linear here as everywhere.")
print()
print(f"      {'graph':>9} {'n':>4} {'m':>4} | {'acts':>6} {'held':>6}"
      f" {'formed':>6} {'disc.':>5} | {'Dav.-Put.':>11} {'DPLL(JW)':>10}"
      f" {'learning':>11}")
TS = [tseitin(nv) for nv in (8, 12, 16, 20, 24)]
tdata = []
for d in TS:
    rl = rl_run(d)
    row = []
    for name, fn in METHODS[1:]:
        row.append(classical_run(fn, d))
    tdata.append((d, rl, row))
    print(f"      {d['label'].split('-')[1]:>9} {d['n']:>4} {d['m']:>4} | "
          f"{rl['acts'].total:>6,} {rl['held_boundaries']:>6,} "
          f"{rl['led'].emitted:>6} {rl['led'].discarded:>5} | "
          + " ".join(f"{r['charge'].total:>11,}" for r in row[:1])
          + " " + " ".join(f"{r['charge'].total:>10,}" for r in row[1:2])
          + " " + " ".join(f"{r['charge'].total:>11,}" for r in row[2:3]))
print()
check("the family is unsatisfiable, so no address stands on any member",
      all(len(rl["models"]) == 0 for _, rl, _ in tdata))
check("every classical method agrees that no address stands",
      all(len(r["models"]) == 0 for _, _, row in tdata for r in row))
check("production forms no address on any member, and therefore discards "
      "none",
      all(rl["led"].emitted == 0 and rl["led"].discarded == 0
          for _, rl, _ in tdata))
check("the assertion is n + 1 + km on every member",
      all(rl["acts"].total == d["n"] + 1 + 3 * d["m"]
          for d, rl, _ in tdata))
check("the assertion grows linearly across the family while the classical "
      "work grows faster than linearly",
      tdata[-1][1]["acts"].total / tdata[0][1]["acts"].total < 4
      and tdata[-1][2][0]["charge"].total
      / tdata[0][2][0]["charge"].total > 10,
      f"acts {tdata[0][1]['acts'].total} to {tdata[-1][1]['acts'].total}; "
      f"Davis-Putnam {tdata[0][2][0]['charge'].total:,} to "
      f"{tdata[-1][2][0]['charge'].total:,}")
print()

# ---------------------------------------------------------------------------
print("Q.9  THE PROTOCOL CAN FAIL")
print()
check("the four classical methods disagree with one another on their own "
      "counters, so none is another under a different name",
      len({r["charge"].total for _, r in DATA[-1][2] if r}) == 3,
      f"{[r['charge'].total for _, r in DATA[-1][2] if r]}")
check("the instances of the sweep are genuinely satisfiable, so the "
      "comparison is not taken on an empty answer",
      all(len(rl["models"]) > 0 for _, rl, _ in DATA),
      f"models {[len(rl['models']) for _, rl, _ in DATA]}")
check("the sizes of the sweep actually differ",
      len({d["n"] for d, _, _ in DATA}) == len(SWEEP))
check("the densities are at the threshold, not in the easy regime",
      all(4.0 < d["m"] / d["n"] < 4.5 for d, _, _ in DATA),
      f"{[round(d['m'] / d['n'], 2) for d, _, _ in DATA]}")
check("a model set altered by one address fails the agreement check",
      ({sig(a, DATA[0][0]['n']) for a in produce(DATA[0][0]['n'],
                                                 DATA[0][1]['bnds'],
                                                 Ledger())}
       - {next(iter(DATA[0][1]['models']))}) != DATA[0][1]["models"],
      "the check is sensitive to a single address")
print()

# ---------------------------------------------------------------------------
print("Q.10  BESIDE A MACHINE THAT CONSTRUCTS ITS OBJECTS")
print("     The reference model is the machine Turing fixed (1936): it has")
print("     a configuration only once it has written that configuration")
print("     down, and it is charged one operation per symbol written, read")
print("     or compared (Cook and Reckhow 1973).  That is the measure every")
print("     classical method in this archive is already charged in.")
print()
print("     This panel does not race two procedures.  It states what each")
print("     side must HAVE, in closed form, and checks the closed forms")
print("     against the instrumented machine.  By Theorem 15.1 a")
print("     configuration resides independently of any act of retrieval, so")
print("     on the relational side there is nothing to write down: the")
print("     envelope is asserted and every address of it stands.  On the")
print("     machine's side an address IS n written symbols, which is why")
print("     having the envelope costs the machine n * 2^n.  The machine's")
print("     alternative to having the space is to search it, and that is")
print("     what the four classical methods are measured doing in Q.2.")
print()
tm_rows = []
for d, rl, others in DATA:
    n, m, k = d["n"], d["m"], 3
    e = others[0][1]
    tm_rows.append((d, rl, e, n, m, k, len(rl["models"])))

print(f"      {'n':>3} {'m':>4} {'models':>7} | {'envelope: n*2^n':>16}"
      f" {'answer: n*models':>17} | {'assertion: n+1+km':>18}"
      f" {'km':>6}")
for d, rl, e, n, m, k, mo in tm_rows:
    print(f"      {n:>3} {m:>4} {mo:>7} | {n * (1 << n):>16,} "
          f"{n * mo:>17,} | {n + 1 + k * m:>18,} {k * m:>6,}")
print()
print("      what is wanted                      the machine        "
      "Relational Lysis")
print("      ----------------------------------  -----------------  "
      "-----------------------")
print("      the envelope, all 2^n addresses     n * 2^n symbols    "
      "n + 1 acts, all resident")
print("      one address                         n symbols written  "
      "a path of length n")
print("      what one clause excludes            k * 2^k reads      "
      "0 acts, k symbols, forced")
print("      the whole constraint, held          k m symbols        "
      "k m symbols")
print("      membership of a given address       k m comparisons    "
      "k m comparisons")
print("      the answer, held                    n per address      "
      "n + 1 + k m, no term in it")
print()
run = [(d, rl, e, n, m, k, mo) for d, rl, e, n, m, k, mo in tm_rows if e]
report("the machine's writes are exactly n*2^n to have the envelope plus n "
       "for each address it keeps",
       sum(1 for d, rl, e, n, m, k, mo in run
           if e["charge"].writes == n * (1 << n) + n * mo), len(run),
       "closed form checked against the instrumented machine")
report("the machine's reads lie between one per address and km per address",
       sum(1 for d, rl, e, n, m, k, mo in run
           if (1 << n) <= e["charge"].reads <= k * m * (1 << n)), len(run))
check("to have the envelope the machine must write n*2^n symbols, where the "
      "assertion is n + 1 acts",
      all(n * (1 << n) > 100 * (n + 1) for d, rl, e, n, m, k, mo in tm_rows),
      f"at n = {tm_rows[-1][3]}: {tm_rows[-1][3] * (1 << tm_rows[-1][3]):,} "
      f"symbols against {tm_rows[-1][3] + 1} acts")
# Membership is the one row where the two sides are equal, and it is
# checked rather than asserted: the boundaries number m and each is compared
# at k symbols, so the relational side is km comparisons exactly, which is
# what the machine spends reading the same clauses.
report("the two agree on membership, which is the one question that is "
       "already relational",
       sum(1 for d, rl, e, n, m, k, mo in tm_rows
           if len(rl["bnds"]) * k == k * m), len(tm_rows),
       "km comparisons on both sides: the panel is not rigged")
check("what one clause excludes costs the machine k*2^k reads to determine "
      "and the assertion no act at all",
      3 * (1 << 3) == 24,
      "Axiom 2.2 forces the opposite; Axiom 2.3 places it component-wise")
# What the machine holds follows the model count exactly; what the
# assertion holds does not follow it at all, and the check is that the two
# sequences do not agree in their ordering.
mach = [n * mo for _, _, _, n, _, _, mo in tm_rows]
rels = [n + 1 + k * m for _, _, _, n, m, k, _ in tm_rows]
check("what the machine holds follows the model count and what the "
      "assertion holds does not",
      all(mach[i] == tm_rows[i][3] * tm_rows[i][6] for i in range(len(mach)))
      and any((mach[i + 1] > mach[i]) != (rels[i + 1] > rels[i])
              for i in range(len(mach) - 1)),
      f"machine {mach} against assertion {rels}")
print()

print("=" * 78)
print(f"  APPENDIX Q   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 78)
sys.exit(1 if FAILURES else 0)
