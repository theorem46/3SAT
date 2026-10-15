#!/usr/bin/env python3
"""
PRODUCTION FROM THE BOUNDARY

The stored object is the boundary.  The addresses are produced from it.

WHAT THIS MODULE IS, AND WHAT ITS TALLY IS NOT.

This module is a verification device.  It establishes, from the boundaries
alone, which addresses the boundaries admit, so that the asserted structure
can be checked against a committed solution set and against an independent
survey of the envelope.  Its tally (conventions.Ledger) is charged to
nothing and is reported as no method's cost.

The reason is axiomatic.  By Theorem 15.1 every finite configuration resides
within the descent of the first relation "independently of any act of
selection, retrieval, or observation"; the addresses are not brought into
being by this file.  As Section 1 of the primitive architecture states it,
"retrieval is arrival at an address rather than reassembly from parts" and
"the cost of a configuration is the length of its path rather than the size
of a stored table".  Building and holding a catalogue of addresses is
"downstream apparatus, not foundation", so a tally of the walk that builds
one is a figure for that apparatus and never for Relational Lysis.

What is charged to Relational Lysis is the assertion, in structural acts,
and what is reported beside it is what must be held, in symbols.

A boundary u_i is k symbols: the orientations of its k contents at the
excluded sector (Theorem 7.1, Theorem 7.2).  Those k symbols name every
address of the excluded sector -- 2^(n-k) of them -- and the boundary is
therefore the record of that sector, not a sample of it.

Production descends through the boundaries.  At each step every boundary
is in exactly one of three conditions with respect to the partial
orientation standing so far:

  DISCHARGED  some oriented content of its support disagrees with the
              excluded sector.  The sector cannot be reached below this
              point, and the boundary says nothing further.

  FORCING     every oriented content of its support agrees with the
              excluded sector and exactly one content remains unoriented.
              The boundary then forces that content to the orientation
              opposite the sector's (Axiom 2.2): no other orientation is
              admissible, because taking the sector's orientation would
              place the descent inside a sector the boundary excludes.

  OPEN        two or more contents of its support remain unoriented.  The
              boundary is not yet decisive.

Forcing is applied to exhaustion before any orientation is chosen.  That
ordering is what removes search: a boundary's excluded sector becomes
reachable only when its last content is oriented, and forcing orients
that content one step earlier.  The descent therefore never enters an
excluded sector, and so never forms an address it must discard.

Where no boundary forces, the lowest unoriented content stands in both
orientations -- the conjugate pair -- and the descent continues into each.
Where two boundaries force opposite orientations on the same content,
their excluded sectors jointly exhaust the region and the descent closes
there; the exclusion is read off the two boundaries, not tested against
an address.

The addresses emitted are exactly the standing addresses.  Nothing is
stored but the boundaries and the orientation of the current descent.

LOCALITY, AND WHY IT IS NOT AN OPTIMISATION.

Axiom 5.1 states that a relational state \"possesses no existence beyond
the strict limits defined by its bounding interface\".  The boundary u_i is
bounded by its own k contents, so it stands in no relation to any content
outside that support.  Its condition with respect to a partial orientation
is therefore a fact about its own k contents and nothing else, and orienting
a content can change the condition of exactly those boundaries whose support
contains it.

A resolution that re-reads a boundary after orienting a content outside its
support is reading a relation the axiom says is not there.  The index built
below -- content to the boundaries containing it -- is what the axiom
requires, not a device for making a figure smaller, and it is what bounds
the reads of a descent:

    residence reads  <=  m  +  sum over orientations fixed of deg(that
                              content)
                     <=  m  +  (forced + chosen) * max_p deg(x_p)

m for the one survey at genesis, then the degree of each content as it is
oriented.  No term in 2^n appears, and the bound is a consequence of the
axiom rather than a measurement of this program.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

from conventions import Ledger                                 # noqa: E402

__all__ = ["produce", "produce_count", "produce_first", "produce_nth",
           "classify", "Ledger", "DISCHARGED", "FORCING", "OPEN", "MATCHED"]

DISCHARGED = "discharged"   # the sector cannot be reached below this point
FORCING = "forcing"         # one content unoriented; the boundary dictates it
OPEN = "open"               # two or more unoriented; not yet decisive
MATCHED = "matched"         # every content oriented at the excluded sector


def classify(boundary, fixed, value):
    """The condition of one boundary with respect to a partial orientation.

    This is the whole of the mechanism, isolated so that it can be tested on
    its own (Appendix I.1) and so that no other function may decide a
    boundary's condition by a different rule.
    """
    bmask, bval = boundary
    decided = bmask & fixed
    if (value & decided) != (bval & decided):
        return DISCHARGED
    free = bmask & ~fixed
    if free == 0:
        return MATCHED
    if free & (free - 1) == 0:
        return FORCING
    return OPEN


def support_index(n, bnds):
    """Content to the boundaries whose support contains it.

    Axiom 5.1: a boundary relates only to its own contents, so this index
    is the complete account of which boundaries any one orientation can
    affect.  Built once from the asserted boundaries, in km steps.
    """
    idx = [[] for _ in range(n + 1)]
    for i, (bmask, _) in enumerate(bnds):
        p = 1
        mk = bmask
        while mk:
            if mk & 1:
                idx[p].append(i)
            mk >>= 1
            p += 1
    return [tuple(v) for v in idx]


def _reclassify(bnds, touched, live, forcing, fixed, value, led):
    """Re-read only the boundaries whose support contains a content just
    oriented, and update the descent's view of them.

    `live` is the set of boundaries not yet discharged; `forcing` maps a
    content's bit to the orientation a boundary dictates for it.  Returns
    False if the region is closed -- a boundary fully matched, or two
    boundaries forcing opposite orientations on one content.
    """
    for i in touched:
        if i not in live:
            continue                       # discharged, and stays so
        bmask, bval = bnds[i]
        led.consult()                      # one residence read
        condition = classify((bmask, bval), fixed, value)
        if condition is DISCHARGED:
            live.discard(i)
            continue
        if condition is MATCHED:
            return False                   # the sector is fully matched
        if condition is FORCING:
            free = bmask & ~fixed
            want = 0 if (bval & free) else free
            prior = forcing.get(free)
            if prior is not None and prior != want:
                return False               # opposite forcings
            forcing[free] = want
    return True


def _survey(bnds, live, fixed, value, led):
    """Read the boundaries still live against the partial orientation.

    A boundary discharged at a point is discharged everywhere below it,
    since orientations are only added as the descent deepens and never
    revised (Proposition 14.1).  The survey therefore returns the
    surviving boundaries, and a discharged boundary is never read again.

    Returns (verdict, datum, surviving):
      ("closed", None, _)          two boundaries force opposite
                                   orientations, or a sector is fully
                                   matched
      ("forced", (bit, want), s)   the lowest content a boundary dictates
      ("open", None, s)            no boundary is decisive
    """
    forced_here = {}
    surviving = []
    for idx in live:
        bmask, bval = bnds[idx]
        led.consult()
        condition = classify((bmask, bval), fixed, value)
        if condition is DISCHARGED:
            continue                       # and stays discharged below
        if condition is MATCHED:
            return "closed", None, surviving
        surviving.append(idx)
        if condition is FORCING:
            free = bmask & ~fixed
            # the sector's orientation at that content is inadmissible, so
            # the content is forced to the opposite orientation
            want = 0 if (bval & free) else free
            prior = forced_here.get(free)
            if prior is not None and prior != want:
                return "closed", None, surviving   # opposite forcings
            forced_here[free] = want
    if forced_here:
        bit = min(forced_here)
        return "forced", (bit, forced_here[bit]), surviving
    return "open", None, surviving


def produce(n, bnds, led=None):
    """Produce the standing addresses from the boundaries.

    A generator.  Holds the boundaries, the orientation of the current
    descent, and the descent's own stack of pending branches.  No list of
    addresses exists at any point, and the envelope is never traversed.
    """
    if led is None:
        led = Ledger()
    full = (1 << n) - 1
    index = support_index(n, bnds)

    # One survey at genesis: every boundary read once against the empty
    # orientation.  Thereafter a boundary is re-read only when a content of
    # its own support is oriented (Axiom 5.1).
    live0 = set()
    forcing0 = {}
    opened = True
    for i, (bmask, bval) in enumerate(bnds):
        led.consult()
        condition = classify((bmask, bval), 0, 0)
        if condition is DISCHARGED:
            continue
        if condition is MATCHED:
            opened = False                 # a clause excludes everything
            break
        live0.add(i)
        if condition is FORCING:
            free = bmask & ~0
            want = 0 if (bval & free) else free
            prior = forcing0.get(free)
            if prior is not None and prior != want:
                opened = False
                break
            forcing0[free] = want
    if not opened:
        led.close()
        return

    # each frame is a partial orientation together with the descent's view
    # of the boundaries at that point
    stack = [(0, 0, live0, forcing0)]
    while stack:
        led.depth(len(stack))
        fixed, value, live, forcing = stack.pop()
        live = set(live)
        forcing = dict(forcing)
        # apply forcing to exhaustion, re-reading only what each
        # orientation can affect
        closed = False
        while forcing:
            bit, want = min(forcing.items())
            del forcing[bit]
            if fixed & bit:
                continue                   # already oriented, by an earlier
                                           # forcing in this same round
            fixed |= bit
            if want:
                value |= bit
            led.force()
            p = bit.bit_length()
            if not _reclassify(bnds, index[p], live, forcing,
                               fixed, value, led):
                closed = True
                break
        if closed:
            led.close()
            if fixed == full:
                # Every content was oriented before the exclusion was seen,
                # so a complete address was formed and is now thrown away.
                # That is a discard, and discarding is the signature of
                # search.  It cannot occur while forcing is applied to
                # exhaustion: a boundary's excluded sector becomes reachable
                # only when the last content of its support is oriented, and
                # forcing orients that content, to the admissible
                # orientation, one step earlier.  The figure is therefore
                # zero by the mechanism rather than by stipulation -- and a
                # run in which forcing is weakened records a positive count
                # here (Appendix H, fault `no-eager-forcing`).
                led.discard()
            continue
        if fixed == full:
            # every content is oriented and no boundary excludes this
            # address.  Forcing is applied to exhaustion above, so a fully
            # oriented descent that reaches here was never a candidate to
            # be tested: it is the address the boundaries produced.
            led.emit()
            yield value
            continue
        # No boundary is decisive: the lowest unoriented content stands in
        # both orientations -- the conjugate pair -- and the descent
        # continues into each.  This is the one act the descent performs
        # that a boundary did not dictate, and it is what the production
        # ledger charges.
        free = full & ~fixed
        bit = free & -free
        p = bit.bit_length()
        led.branch()
        led.choose()
        for orient in (bit, 0):            # the two sides of the pair
            cfixed = fixed | bit
            cvalue = value | orient
            clive = set(live)
            cforcing = {}
            # only the boundaries holding this content can have changed
            if _reclassify(bnds, index[p], clive, cforcing,
                           cfixed, cvalue, led):
                stack.append((cfixed, cvalue, clive, cforcing))
            else:
                led.close()
                if cfixed == full:
                    led.discard()


def produce_count(n, bnds, led=None):
    """How many addresses stand.  Produced, not counted over the envelope."""
    total = 0
    for _ in produce(n, bnds, led):
        total += 1
    return total


def produce_first(n, bnds, led=None):
    """One standing address.  Returns None if the boundaries close the
    envelope entirely."""
    for a in produce(n, bnds, led):
        return a
    return None


def produce_nth(i, n, bnds, led=None):
    """The i-th standing address in the descent's own order."""
    for j, a in enumerate(produce(n, bnds, led)):
        if j == i:
            return a
    return None
