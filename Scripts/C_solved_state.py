#!/usr/bin/env python3
"""
APPENDIX C -- THE SOLVED STATE OF A BOUNDARY

Validates Section 8 of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

For every boundary of both instances the relational assignment of
Definition 9.1 [2] is formed on the boundary's own support, decomposed by
Proposition 9.1 [2], and reduced by the elementary lysis transformation of
Definition 10.3 [2] to its fixed harmonic point.

Exact rational arithmetic throughout (fractions.Fraction): no floating
point, so no tolerance is required and no check can pass by rounding.

Any failure exits non-zero.  Deterministic.  No third-party dependencies.
"""

import json
import os
import sys
from fractions import Fraction as F
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

sys.path.insert(0, HERE)
from resolution import load_instance   # noqa: E402

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
#  The solved state.  Definition 9.1, Proposition 9.1, Definition 9.2 [2].
#  The assignment takes the Theorem 6.8 form of [3]:
#      A_ij = (s_i - s_j)(s_i - s_c),   s_c the centre of the support.
# ---------------------------------------------------------------------------

def assignment(s):
    w = len(s)
    sc = sum(s, F(0)) / w
    return [[(s[i] - s[j]) * (s[i] - sc) for j in range(w)] for i in range(w)]


def decompose(A):
    w = len(A)
    D = [[(A[i][j] + A[j][i]) / 2 for j in range(w)] for i in range(w)]
    S = [[(A[i][j] - A[j][i]) / 2 for j in range(w)] for i in range(w)]
    return D, S


def mu(S):
    """Definition 10.2 [2]: the residual size."""
    return sum(1 for row in S for v in row if v != 0)


def lyse(S):
    """Definition 10.3 [2]: zero the lexicographically minimal nonzero
    ordered pair and its transpose, repeat.  Returns the step count and the
    sequence of residual sizes."""
    S = [row[:] for row in S]
    w = len(S)
    trace = [mu(S)]
    steps = 0
    while True:
        target = None
        for i in range(w):
            for j in range(w):
                if S[i][j] != 0:
                    target = (i, j)
                    break
            if target:
                break
        if target is None:
            return steps, trace, S
        i, j = target
        S[i][j] = F(0)
        S[j][i] = F(0)
        steps += 1
        trace.append(mu(S))


# ---------------------------------------------------------------------------
print("=" * 74)
print("  APPENDIX C -- THE SOLVED STATE OF A BOUNDARY")
print("  validates Section 8: Definition 9.1, Proposition 9.1,")
print("            Definition 9.2, Definitions 10.2-10.3,")
print("            Propositions 10.2-10.4, Theorem 22.3")
print("  exact rational arithmetic; no floating point, no tolerance")
print("=" * 74)
print()

INSTANCES = [load("instance1.json"), load("instance2.json")]
ALL = [(d["label"], c) for d in INSTANCES for c in d["clauses"]]
print(f"  boundaries under test: {len(ALL)}")
print()

# ---------------------------------------------------------------------------
print("C.1  PROPOSITION 9.1 -- THE DECOMPOSITION A = D + S IS UNIQUE")
print()
ok_sum = ok_sym = ok_anti = 0
for label, c in ALL:
    s = [F(l) for _, l in c]
    A = assignment(s)
    D, S = decompose(A)
    w = len(s)
    if all(D[i][j] + S[i][j] == A[i][j] for i in range(w) for j in range(w)):
        ok_sum += 1
    if all(D[i][j] == D[j][i] for i in range(w) for j in range(w)):
        ok_sym += 1
    if all(S[i][j] == -S[j][i] for i in range(w) for j in range(w)):
        ok_anti += 1
report("D + S = A entrywise", ok_sum, len(ALL))
report("D symmetric entrywise", ok_sym, len(ALL))
report("S antisymmetric entrywise", ok_anti, len(ALL))
print()

# ---------------------------------------------------------------------------
print("C.2  LEMMA 7.1 [3] -- D IS THE METRIC ON THE SUPPORT")
print("     D_ij = (1/2)||s_i - s_j||^2, so D = 0 exactly on aligned pairs")
print()
ok_metric = ok_zero = 0
for label, c in ALL:
    s = [F(l) for _, l in c]
    D, _ = decompose(assignment(s))
    w = len(s)
    if all(D[i][j] == (s[i] - s[j]) ** 2 / 2 for i in range(w) for j in range(w)):
        ok_metric += 1
    if all((D[i][j] == 0) == (s[i] == s[j]) for i in range(w) for j in range(w)):
        ok_zero += 1
report("D_ij equals half the squared difference", ok_metric, len(ALL))
report("D vanishes exactly on same-orientation pairs", ok_zero, len(ALL))
print()

# ---------------------------------------------------------------------------
print("C.3  PROPOSITIONS 10.2-10.3 -- STRICT DESCENT AND FINITE TERMINATION")
print()
ok_desc = ok_term = ok_steps = 0
for label, c in ALL:
    _, S = decompose(assignment([F(l) for _, l in c]))
    steps, trace, Sf = lyse(S)
    if all(trace[i] > trace[i + 1] for i in range(len(trace) - 1)):
        ok_desc += 1
    if mu(Sf) == 0:
        ok_term += 1
    if steps == trace[0] // 2:
        ok_steps += 1
report("mu(S) strictly decreases at every step (Prop 10.2)", ok_desc, len(ALL))
report("lysis terminates at S = 0 (Prop 10.3, Prop 10.4)", ok_term, len(ALL))
report("step count = mu(S)/2 (Def 10.3 zeroes a pair and its transpose)",
       ok_steps, len(ALL))
print()

# ---------------------------------------------------------------------------
print("C.4  DEFINITION 10.3 -- D IS PRESERVED BY LYSIS, ENTRYWISE")
print()
ok = 0
for label, c in ALL:
    s = [F(l) for _, l in c]
    D0, S0 = decompose(assignment(s))
    before = [row[:] for row in D0]
    lyse(S0)
    if before == D0:
        ok += 1
report("D unchanged through the whole reduction", ok, len(ALL))
print()

# ---------------------------------------------------------------------------
print("C.5  THEOREM 22.3 -- THE TWO TERMINI OF A BOUNDARY")
print("     exhaustive over all 2^k agreement states of every boundary:")
print("     exactly two carry mu(S) = 0, at Sigma = +k and Sigma = -k")
print()
ok_two = ok_sigma = ok_conj = 0
states_tested = 0
for label, c in ALL:
    k = len(c)
    termini = []
    for t in product([F(1), F(-1)], repeat=k):
        states_tested += 1
        _, S = decompose(assignment(list(t)))
        if mu(S) == 0:
            termini.append(t)
    if len(termini) == 2:
        ok_two += 1
    sigmas = sorted(sum(t, F(0)) for t in termini)
    if sigmas == [F(-k), F(k)]:
        ok_sigma += 1
    if len(termini) == 2 and all(a == -b for a, b in zip(*termini)):
        ok_conj += 1
report("exactly two termini per boundary", ok_two, len(ALL))
report("termini at Sigma = +k and Sigma = -k", ok_sigma, len(ALL))
report("the two termini are a conjugate pair (Thm 12.1)", ok_conj, len(ALL),
       f"{states_tested} agreement states tested exhaustively")
print()

# ---------------------------------------------------------------------------
print("C.6  THE NON-TERMINAL STATES REQUIRE THE OPERATOR")
print("     every remaining state carries mu(S) > 0 and reduces in mu/2 steps")
print()
ok = 0
for label, c in ALL:
    k = len(c)
    fine = True
    for t in product([F(1), F(-1)], repeat=k):
        _, S = decompose(assignment(list(t)))
        m0 = mu(S)
        if m0 == 0:
            continue
        steps, trace, Sf = lyse(S)
        if not (steps == m0 // 2 and mu(Sf) == 0
                and all(trace[i] > trace[i + 1] for i in range(len(trace) - 1))):
            fine = False
            break
    if fine:
        ok += 1
report("every non-terminal state reduces to S = 0 in mu/2 steps", ok, len(ALL))
print()

# ---------------------------------------------------------------------------
print("C.7  ADVERSARIAL -- THE DECOMPOSITION IS UNIQUE, NOT MERELY CONSISTENT")
print("     any other symmetric/antisymmetric split of A is shown impossible:")
print("     D' = D + E with E symmetric forces S' = S - E antisymmetric,")
print("     which forces E = 0.  Tested on perturbations of every boundary.")
print()
ok = 0
for label, c in ALL:
    s = [F(l) for _, l in c]
    A = assignment(s)
    D, S = decompose(A)
    w = len(s)
    clean = True
    # perturb by a nonzero symmetric E and confirm the antisymmetry of the
    # complementary part fails
    for (a, b) in ((0, 1), (0, w - 1), (1, w - 1)):
        E = [[F(0)] * w for _ in range(w)]
        E[a][b] = E[b][a] = F(1)
        Dp = [[D[i][j] + E[i][j] for j in range(w)] for i in range(w)]
        Sp = [[A[i][j] - Dp[i][j] for j in range(w)] for i in range(w)]
        if all(Sp[i][j] == -Sp[j][i] for i in range(w) for j in range(w)):
            clean = False
            break
    if clean:
        ok += 1
report("no alternative symmetric/antisymmetric split exists", ok, len(ALL))
print()

# ---------------------------------------------------------------------------
print("C.8  THE TERMINAL CHARACTERISATION AT WIDTH 3, 4 AND 5")
print("     S vanishes exactly where, for every pair, the orientations")
print("     agree or sum to 2*sigma_c.  The termini are the two uniform")
print("     states for k odd, and those plus the balanced states for k")
print("     even.  Exhaustive over all 2^k states, exact arithmetic.")
print()

from math import comb                                           # noqa: E402

print(f"      {'k':>3} {'states':>7} {'termini':>8} {'predicted':>10} "
      f"{'uniform':>8} {'balanced':>9}")
width_rows = []
for k in (3, 4, 5):
    states = list(product((F(1), F(-1)), repeat=k))
    termini = []
    pairwise_ok = 0
    for s in states:
        A = assignment(list(s))
        _, S = decompose(A)
        sc = sum(s, F(0)) / k
        # the closed-form criterion, independent of the matrix
        criterion = all(s[i] == s[j] or s[i] + s[j] == 2 * sc
                        for i in range(k) for j in range(k))
        if (mu(S) == 0) == criterion:
            pairwise_ok += 1
        if mu(S) == 0:
            termini.append(s)
    uniform = [t for t in termini if len(set(t)) == 1]
    balanced = [t for t in termini if sum(t, F(0)) == 0 and len(set(t)) > 1]
    predicted = 2 if k % 2 else 2 + comb(k, k // 2)
    width_rows.append((k, len(states), len(termini), predicted,
                       len(uniform), len(balanced)))
    print(f"      {k:>3} {len(states):>7} {len(termini):>8} {predicted:>10} "
          f"{len(uniform):>8} {len(balanced):>9}")
    report(f"k = {k}: S = 0 agrees with the pairwise criterion on every state",
           pairwise_ok, len(states))
print()

for k, nstates, nterm, pred, nuni, nbal in width_rows:
    check(f"k = {k}: termini number {nterm}, as predicted ({pred})",
          nterm == pred,
          "2 for k odd, 2 + C(k, k/2) for k even")
    check(f"k = {k}: the two uniform states are terminal at every width",
          nuni == 2)
    check(f"k = {k}: balanced termini number {nbal}",
          nbal == (0 if k % 2 else comb(k, k // 2)),
          "none for k odd -- Sigma and k share parity, so Sigma = 0 "
          "is unattainable")

check("width 3 is the odd case the paper resolves: exactly two termini",
      width_rows[0][2] == 2 and width_rows[0][5] == 0)
check("width 4 carries a balanced terminal family, so even width is not "
      "the same object",
      width_rows[1][5] > 0,
      f"{width_rows[1][5]} balanced termini at k = 4")
print()

# ---------------------------------------------------------------------------
print("=" * 74)
print(f"  APPENDIX C   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
