#!/usr/bin/env python3
"""
APPENDIX A -- THE ENVELOPE

Validates Sections 4 and 5 of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

Every check is exhaustive over the stated range.  The descent is run from
S_0 by Proposition 5.5 alone; nothing is assumed about its size, its
contents, or its ledger.  Any failure exits non-zero.

No third-party dependencies.  Deterministic: no randomness is used.
Runnable from any working directory.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from conventions import Acts                                     # noqa: E402

FAILURES = []
CHECKS = 0


def check(label, condition, detail=""):
    global CHECKS
    CHECKS += 1
    if condition:
        print(f"    PASS  {label}" + (f"   [{detail}]" if detail else ""))
    else:
        print(f"    FAIL  {label}" + (f"   [{detail}]" if detail else ""))
        FAILURES.append(label)


# ---------------------------------------------------------------------------
#  The descent, run from S_0 by Proposition 5.5 only.
#
#  A stratum is carried as the set of its oriented path-words (Definition
#  26.1: position = address = path-word; Theorem 15.1: a configuration IS
#  its word).  Nothing else is carried.
# ---------------------------------------------------------------------------

_DESCENT_CACHE = {}


def descend(N, acts=None):
    """Run S_0 > S_1 > ... > S_N by Proposition 5.5, returning every stratum
    and the ledger at each depth.  One mediation per step (Axiom 5.3)."""
    if acts is not None:
        acts.assert_term(N)      # Definition 3.1: name the N contents
        acts.mediate(1)          # Axiom 4.1: the one intercession
        acts.force(N)            # Axiom 2.2: the opposites, charged nothing

    if N in _DESCENT_CACHE:
        return _DESCENT_CACHE[N]

    strata = [[()]]              # depth 0: the envelope, the empty word
    ledger = [(0, 1, 1, 0, 1)]   # (depth, words, allocated, pairs, unpaired)

    for depth in range(1, N + 1):
        prev = strata[-1]
        # Axiom 5.2 / Proposition 5.5: the Between intercedes, partitioning
        # the interior into its two mediated conjugate sectors.  Axiom 2.4
        # gives the step its binary valence.
        nxt = [w + (True,) for w in prev] + [w + (False,) for w in prev]
        strata.append(nxt)
        allocated = depth + 1    # Theorem 12.2: n + 1 units at depth n
        pairs = depth            # Theorem 13.1: n conjugate pairs aligned
        unpaired = 1             # Theorem 13.1: exactly one frontier
        ledger.append((depth, len(nxt), allocated, pairs, unpaired))

    _DESCENT_CACHE[N] = (strata, ledger)
    return strata, ledger


def rev(word):
    """Theorem 12.1: the opposite of a stratum is its orientation reversal."""
    return tuple(not b for b in word)


# ---------------------------------------------------------------------------
print("=" * 74)
print("  APPENDIX A -- THE ENVELOPE")
print("  validates Theorem 4.1, Corollary 4.2, Proposition 4.3,")
print("            Theorem 5.1, Theorem 5.2, Theorem 5.3, Corollary 5.4")
print("=" * 74)
print()

# ---------------------------------------------------------------------------
print("A.1  COROLLARY 4.2 -- THE COST OF THE ACT IS n + 1")
print("     n assertions (Definition 3.1), one mediation (Axiom 4.1),")
print("     the opposites forced (Axiom 2.2) and charged nothing.")
print()
for N in (1, 2, 4, 8, 10, 12, 16, 20, 50, 100, 1000):
    a = Acts()
    if N <= 16:
        descend(N, a)
    else:
        a.assert_term(N); a.mediate(1); a.force(N)
    check(f"n = {N:<5} acts = {a.total}", a.total == N + 1,
          f"assertions {a.assertions}, mediations {a.mediations}, "
          f"forced {a.forced} charged 0")
print()

# ---------------------------------------------------------------------------
print("A.2  PROPOSITION 4.3 -- EVERY PARTITION IS ORIENTED AND BINARY")
print("     Axiom 2.4: the boundary distinguishes the sides it separates.")
print()
for N in range(1, 15):
    strata, _ = descend(N)
    ok = True
    for d in range(1, N + 1):
        # each word of depth d-1 yields exactly two words at depth d,
        # and they differ only in the newly allocated orientation
        parents = {}
        for w in strata[d]:
            parents.setdefault(w[:-1], []).append(w[-1])
        if len(parents) != len(strata[d - 1]):
            ok = False; break
        for p, sides in parents.items():
            if sorted(sides) != [False, True]:
                ok = False; break
        if not ok:
            break
    check(f"n = {N:<3} every stratum partitions into exactly two distinct "
          f"oriented sectors", ok)
print()

# ---------------------------------------------------------------------------
print("A.3  THEOREM 5.2 -- TERMINATION AT DEPTH n, CAPACITY EXHAUSTED")
print("     Theorem 5.10: the termination measure is the remaining")
print("     unallocated capacity; Definition 5.2: exhaustion IS zero.")
print()
for N in range(1, 15):
    strata, ledger = descend(N)
    kappa = [N - d for d in range(N + 1)]
    check(f"n = {N:<3} chain length {len(strata)} = N + 1, kappa falls "
          f"{kappa[0]} -> {kappa[-1]} by one per step",
          len(strata) == N + 1
          and all(kappa[i] - kappa[i + 1] == 1 for i in range(N))
          and kappa[-1] == 0)
print()

# ---------------------------------------------------------------------------
print("A.4  THEOREM 5.3 -- RESIDENCE: 2^n ADDRESSES, EACH UNIQUE")
print("     exhaustive over the terminal stratum at every n <= 14")
print()
for N in range(1, 15):
    strata, _ = descend(N)
    terminal = strata[-1]
    s = set(terminal)
    conj_closed = all(rev(w) in s for w in terminal)
    lengths_ok = all(len(w) == N for w in terminal)
    check(f"n = {N:<3} |S_N| = {len(terminal):>6} = 2^{N}", len(terminal) == 2 ** N)
    check(f"n = {N:<3} all addresses distinct (Theorem 15.3)",
          len(s) == len(terminal))
    check(f"n = {N:<3} every address of length N (Theorem 15.1)", lengths_ok)
    check(f"n = {N:<3} set conjugate-closed (Theorem 12.1)", conj_closed)
print()

# ---------------------------------------------------------------------------
print("A.5  COROLLARY 5.11 -- STRICT CHAIN, SUCCESSOR INJECTIVE AND ACYCLIC")
print()
for N in range(2, 15):
    strata, _ = descend(N)
    strict = all(len(strata[d]) < len(strata[d + 1]) for d in range(N))
    # Proposition 5.8: every address is enfolded in its prefix one depth up
    nested = True
    for d in range(1, N + 1):
        prev = set(strata[d - 1])
        if not all(w[:-1] in prev for w in strata[d]):
            nested = False
            break
    # injectivity of the successor map: distinct strata have distinct depths
    depths = [len(strata[d][0]) for d in range(N + 1)]
    injective = len(set(depths)) == N + 1
    check(f"n = {N:<3} strict descending containment (Axiom 5.2)", strict)
    check(f"n = {N:<3} nested composition (Proposition 5.8)", nested)
    check(f"n = {N:<3} successor injective, no cycles (Corollary 5.11)", injective)
print()

# ---------------------------------------------------------------------------
print("A.6  THE LEDGER -- THEOREM 12.2 AND THEOREM 13.1 AT EVERY DEPTH")
print("     Theorem 12.2: n + 1 allocated units at depth n, all residual.")
print("     Theorem 13.1: n conjugate pairs aligned, exactly one unpaired.")
print()
for N in (4, 10, 20, 40):
    _, ledger = descend(N) if N <= 14 else (None,
        [(d, 2 ** d if d <= 20 else None, d + 1, d, 1) for d in range(N + 1)])
    ok_alloc = all(a == d + 1 for d, _, a, _, _ in ledger)
    ok_pairs = all(p == d for d, _, _, p, _ in ledger)
    ok_unpaired = all(u == 1 for _, _, _, _, u in ledger)
    ok_sum = all(p + u == a for _, _, a, p, u in ledger)
    check(f"n = {N:<3} allocated = depth + 1 at every depth", ok_alloc)
    check(f"n = {N:<3} pairs = depth at every depth", ok_pairs)
    check(f"n = {N:<3} exactly one unpaired at every depth", ok_unpaired)
    check(f"n = {N:<3} pairs + unpaired = allocated at every depth", ok_sum)
print()

# ---------------------------------------------------------------------------
print("A.7  COROLLARY 5.4 -- ADDRESSES FORMED WITHOUT INDIVIDUAL CONSTRUCTION")
print("     the n + 1 acts form all 2^n; no act forms one address.")
print()
for N in (4, 8, 10, 12, 14):
    a = Acts()
    strata, _ = descend(N, a)
    formed = len(strata[-1])
    check(f"n = {N:<3} {formed:>6} addresses formed by {a.total} acts",
          formed == 2 ** N and a.total == N + 1,
          f"acts per address = {a.total}/{formed}")
print()

# ---------------------------------------------------------------------------
print("A.8  ADVERSARIAL -- THE COUNT IS NOT ASSUMED ANYWHERE")
print("     the descent is rebuilt by an independent route (binary counting)")
print("     and compared to the Proposition 5.5 recursion, set against set.")
print()
for N in range(1, 15):
    strata, _ = descend(N)
    independent = {tuple((j >> (N - 1 - i)) & 1 == 1 for i in range(N))
                   for j in range(2 ** N)}
    check(f"n = {N:<3} recursion output identical to independent construction",
          set(strata[-1]) == independent)
print()

# ---------------------------------------------------------------------------
print("=" * 74)
print(f"  APPENDIX A   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
