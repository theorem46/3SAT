"""
resolution.py -- the assertion, written once.

Imported by every appendix that resolves an instance, so that none can pass
on a variant of its own.  This file is not an experiment.

WHAT IS STORED IS THE BOUNDARY.  There is no list of addresses in this
module, and none is created, kept, cached or summarised by any function in
it.  The boundaries are asserted here; the addresses are produced from them
in production.py.

A NOTE ON THE SURVEY FUNCTIONS AT THE END OF THIS FILE.

The functions whose names begin `survey_` traverse the envelope, one address
at a time, and test each against the boundaries.  They are NOT the
resolution and they are not what the paper claims.  They exist for one
purpose: to check the boundaries against a complete truth table, so that
the resolution can be verified by exact set equality on every address of the
envelope rather than on a sample.  Verification is permitted to be
exhaustive; that is what makes it verification.

The resolution is production.produce, which consults the boundaries and
emits the standing addresses without traversing anything.  Every cost figure
the paper reports for Relational Lysis comes from the assertion (class Acts)
and from production (class Ledger).  No survey figure is ever reported as a
cost of the method, and the survey functions are charged to no measure.
"""

import hashlib
import json
import os

__all__ = ["load_instance", "_fingerprint", "FINGERPRINTS", "boundaries",
           "assertion_cost", "sig", "unsig", "excluding_boundaries", "stands",
           "survey_count", "survey_nth", "survey_stream"]


# ---------------------------------------------------------------------------
#  Instance integrity
#
#  The expected fingerprints live HERE, in code, not only in the files they
#  protect.  A fingerprint stored only beside the data it certifies is an
#  internal-consistency seal: anyone may substitute the data and recompute
#  the seal.  Pinning the hex here means the archive is bound to these two
#  instances and to no others, so a substituted instance fails to load even
#  if its own fingerprint is consistent.
# ---------------------------------------------------------------------------

FINGERPRINTS = {
    "instance1.json":
        "ffd36235ea4b0455a4dcbd62bb44cce35a23eef93570c8885327f4bc96e73965",
    "instance2.json":
        "4f51871db1190a1d737df34f5869ba184e2b04f0add33a13a36d7201e7ed1785",
    "instance3.json":
        "f173fc01677f6f6cdb373d424f74008625157f09c512c76a849b5987908cbd85",
}


def _fingerprint(d):
    """SHA-256 over a canonical serialisation of the whole instance.

    Every field a protocol or the manuscript relies on is inside the hash:
    the contents, the clauses, the declared counts, the committed solution
    set, the planted assignment, the generator's seed and the label.  An
    alteration anywhere in the instance therefore changes it -- including
    the removal of a clause that happens to be logically redundant, and
    including a change to a field no check reads directly.
    """
    canon = json.dumps(
        {
            "label": d.get("label"),
            "n": d["n"],
            "k": d["k"],
            "m": d["m"],
            "density": d.get("density"),
            "seed": d.get("seed"),
            "planted": d.get("planted"),
            "solutions": sorted(d.get("solutions") or []),
            "clauses": [[list(t) for t in c] for c in d["clauses"]],
        },
        sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canon.encode()).hexdigest()


def load_instance(path):
    """Load an instance and verify its integrity before returning it.

    Any failure raises.  A protocol that cannot load its instance must fail,
    never report "0 of 0 checks pass".
    """
    with open(path) as f:
        d = json.load(f)
    d["clauses"] = [[tuple(t) for t in c] for c in d["clauses"]]

    if not d["clauses"]:
        raise ValueError(f"{path}: empty clause list; nothing to resolve")
    if d["m"] != len(d["clauses"]):
        raise ValueError(f"{path}: declares m = {d['m']} but carries "
                         f"{len(d['clauses'])} clauses")
    if any(len(c) != d["k"] for c in d["clauses"]):
        raise ValueError(f"{path}: a clause does not have width k = {d['k']}")
    if not d.get("solutions"):
        raise ValueError(f"{path}: empty solution set; nothing to verify against")
    if len(d["solutions"]) != len(set(d["solutions"])):
        raise ValueError(f"{path}: the committed solution set repeats an address")
    if any(len(w) != d["n"] for w in d["solutions"]):
        raise ValueError(f"{path}: a committed address is not {d['n']} symbols")
    if d.get("planted") not in d["solutions"]:
        raise ValueError(f"{path}: the planted assignment is not in the "
                         f"committed solution set")

    got = _fingerprint(d)
    if d.get("fingerprint") != got:
        raise ValueError(f"{path}: fingerprint mismatch\n"
                         f"  committed {d.get('fingerprint')}\n"
                         f"  computed  {got}\n"
                         f"  the instance data has been altered")

    # the archive is bound to these instances, not merely to self-consistency
    expected = FINGERPRINTS.get(os.path.basename(path))
    if expected is not None and got != expected:
        raise ValueError(f"{path}: this is not the instance the archive "
                         f"reports on\n"
                         f"  expected  {expected}  (pinned in resolution.py)\n"
                         f"  loaded    {got}\n"
                         f"  the instance has been substituted")
    return d


# ---------------------------------------------------------------------------
#  The assertion
# ---------------------------------------------------------------------------

def boundaries(instance):
    """Assert one boundary per clause.

    Theorem 7.1: the excluded sector is the component-wise opposite of the
    clause, forced rather than asserted (Axiom 2.2, Axiom 2.3).
    Theorem 7.2: it is written in k symbols.

    Each boundary is returned as (mask, value) over the envelope's contents:
    mask marks the k positions the boundary fixes, value their orientations
    at the excluded sector.
    """
    out = []
    for c in instance["clauses"]:
        mask = 0
        value = 0
        for p, lit in c:
            bit = 1 << (p - 1)
            mask |= bit
            if lit < 0:              # the opposite of this literal
                value |= bit
        out.append((mask, value))
    assert all(bin(mk).count("1") == len(c)
               for (mk, _), c in zip(out, instance["clauses"]))
    return out


def assertion_cost(instance):
    """Corollary 7.3: n + 1 + km acts."""
    return instance["n"] + 1 + instance["k"] * instance["m"]


# ---------------------------------------------------------------------------
#  Addresses.  An address is an integer; bit p-1 carries the orientation of
#  content x_p (Definition 26.1: position = address = path-word).
# ---------------------------------------------------------------------------

def sig(a, n):
    """An address written as its oriented path-word, x_1 first."""
    return "".join("T" if (a >> i) & 1 else "F" for i in range(n))


def unsig(w):
    """The address of an oriented path-word."""
    return sum(1 << i for i, ch in enumerate(w) if ch == "T")


# ---------------------------------------------------------------------------
#  Questions put to the boundaries
# ---------------------------------------------------------------------------

def excluding_boundaries(a, bnds):
    """Every boundary whose excluded sector contains this address.
    km comparisons; no list of addresses exists."""
    return [i for i, (mask, value) in enumerate(bnds) if (a & mask) == value]


def stands(a, bnds):
    """Whether this address stands.  Short-circuits on the first boundary
    that excludes it."""
    for mask, value in bnds:
        if (a & mask) == value:
            return False
    return True


# ---------------------------------------------------------------------------
#  THE SURVEY.  Verification only.  See the note at the head of this file.
#
#  These traverse the envelope.  They are the complete truth table against
#  which the resolution is checked, and they are charged to no measure and
#  reported as no method's cost.
# ---------------------------------------------------------------------------

def survey_count(n, bnds):
    """VERIFICATION DEVICE.  Traverses the envelope and counts the addresses
    that stand.  This is the truth table, not the resolution."""
    total = 0
    for a in range(1 << n):
        if stands(a, bnds):
            total += 1
    return total


def survey_nth(i, n, bnds):
    """VERIFICATION DEVICE.  Traverses the envelope to its i-th standing
    address.  This is the truth table, not the resolution."""
    seen = 0
    for a in range(1 << n):
        if stands(a, bnds):
            if seen == i:
                return a
            seen += 1
    return None


def survey_stream(n, bnds):
    """VERIFICATION DEVICE.  Traverses the envelope, yielding the addresses
    that stand.  This is the truth table, not the resolution."""
    for a in range(1 << n):
        if stands(a, bnds):
            yield a
