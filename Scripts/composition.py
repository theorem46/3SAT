"""
composition.py -- the composed boundary, by the descent of Section 12.

EVERY OBJECT IN THIS FILE IS A BOUNDARY OR A STRATUM OF THE DESCENT.
NOTHING HERE FORMS AN ADDRESS EXCEPT `read_region`, WHICH IS THE READING OF
AN ANSWER AND NOT PART OF THE COMPOSITION.

WHAT IS COMPOSED, AND BY WHAT MATH.

An inner boundary is not a different object from the first boundary.  The
envelope is the bounding relation of S0 (Axiom 5.1 PA, Remark); it fixes a
finite admissible partition capacity at genesis, and interior mediation
allocates that capacity one level per partition step and does not create it
(Axiom 5.3 PA).  Every generated state forces a strictly finer interior
stratum S_{n+1} := S_n (x) ~S_n, operating strictly within the envelope
(Proposition 5.5 PA), and the Between partitions the interior into mediated
conjugate sectors at strictly finer resolution, the coarser containing the
finer (Axiom 5.2 PA).  The stratification is a strict finite chain, its
successor map injective and admitting no cycles (Corollary 5.11 PA).  So the
descent is inward, monotone in capacity, and deterministic.

Each asserted boundary carries its own solved state on its own support, by
the same math: the relational assignment of Definition 9.1 YM in the form of
Theorem 6.8 TB, decomposed uniquely as A = D + S with D symmetric (aligned)
and S antisymmetric (residual) by Proposition 9.1 YM, reduced by the
elementary lysis transformation of Definition 10.3 YM -- a well-defined
deterministic function (Proposition 10.1 YM), strictly descending in mu(S)
(Proposition 10.2 YM), terminating (Proposition 10.3 YM) at S = 0
(Proposition 10.4 YM), with D untouched; the operator of Theorem 11.5 YM is
then the Laplacian of that surviving aligned component.

For k odd the boundary has exactly TWO termini, the uniform states at
Sigma_u = +k and Sigma_u = -k, and by Axiom 2.3 PA each is the component-wise
opposite of the other: a CONJUGATE PAIR.  The terminus at Sigma_u = -k is the
boundary's excluded sector.  This is Theorem 12.3 of the paper and is
verified in exact rational arithmetic in Appendix C.

THE ONE OPERATIVE FACT.

By Theorem 22.3 PA the conjugate of a terminal frontier "stands asserted but
never presented", and by Theorem 22.1 PA presentation is generated only by
allocation.  A boundary's residual terminus is therefore never presented by
the descent.  Knowing the asserted sector is knowing both termini (Axiom 2.2
PA: the assertion of any term forces the assertion of its structural
opposite; Axiom 2.3 PA: opposition is involutive), and the conjugate stands
interiorly, requiring no exterior term (Proposition 5.4 PA).  Nothing is
constructed, and nothing is charged: the opposite is forced.

Hence the descent never enters a residual terminus, and so never leaves one.
THERE IS NO CLOSURE IN THE SENSE OF A BRANCH ABANDONED.

WHAT IS NOT DONE HERE, AND WHY.

No region is ever decomposed into a disjoint union of parts.  The Remark to
Theorem 11.1 PA is explicit that the primitive decomposition "does not assert
any additive splitting of a single content into aligned-plus-residual parts:
the domain possesses no addition of contents, and no such operation is
invoked."  The only partition performed is Axiom 5.2's: one mediation, into
two mediated conjugate sectors, allocating exactly one level of capacity
(Axiom 5.3, Proposition 5.5 PA).

THREE RELATIONS OF A BOUNDARY TO A STRATUM, all read from the asserted
symbols through the contents of the boundary's own support (Axiom 5.1 PA:
a boundary possesses no existence beyond its own bounding interface):

  AT ITS RESIDUAL TERMINUS   the stratum fixes every content of the support
      and fixes each as the residual terminus demands.  By Theorem 22.3 PA
      this is never presented.

  BARRED FROM IT             the stratum fixes some content of the support
      opposite to that demand.  The boundary then stands at its conjugate
      terminus throughout the stratum, asserted and never presented; no
      address of the stratum can reach the residual terminus.

  NOT YET DETERMINED         neither: the support is not yet wholly fixed and
      nothing yet opposes the demand.  The boundary still requires partition
      within the stratum.

A LIGHTHOUSE is a stratum from which every asserted boundary is barred.  No
asserted relation requires any further partition within it, which by
Definition 5.2 PA is the closure condition -- "the fact of no further
admissible partition" -- and by Axiom 5.3 PA "no novel mediation is
generable, and none is required."  Its radius is the capacity the asserted
relations leave unallocated.  Every address of a lighthouse stands; there is
nothing to reject and no test to perform.

THE ORDER OF MEDIATION IS PART OF THE ASSERTION.

Axiom 2.4 PA makes the Between oriented and Axiom 2.3 PA makes opposition
preserve the order of mediation, so the order in which the contents stand is
asserted rather than chosen by a reader.  Under an order, a boundary is
DETERMINED at the depth at which the last content of its support is oriented
(Axiom 5.1 PA), and says nothing above that depth; boundaries stratify into
BANDS by that depth.

How to assert the order, and which relations to assert, is the open question
this archive poses.  It is not answered here.
"""

__all__ = ["support", "free_count", "residual_terminus", "at_residual",
           "barred", "order_given", "order_closing", "bands", "compose",
           "read_region", "region_str"]


def support(mask):
    """The contents a stratum or a boundary's support constrains."""
    return [p for p in range(mask.bit_length()) if (mask >> p) & 1]


def free_count(region, n):
    """The contents a stratum leaves free: its radius, the capacity the
    asserted relations leave unallocated (Axiom 5.3 PA)."""
    return n - bin(region[0]).count("1")


# ---------------------------------------------------------------------------
#  The boundary's residual terminus
# ---------------------------------------------------------------------------

def residual_terminus(clause, n):
    """The boundary's terminus at Sigma_u = -k, as a partial orientation.

    `clause` is a list of (content, polarity) with 1-based contents and
    polarity +1 or -1.  Theorem 12.3 of the paper: for k odd the termini are
    the two uniform states; the one at Sigma_u = -k is the state at which
    every literal of the boundary is falsified.  Its conjugate, at
    Sigma_u = +k, is forced by Axiom 2.2 PA and involutive by Axiom 2.3 PA;
    it is not written here because it does not need to be.
    """
    fixed = value = 0
    for var, pol in clause:
        p = var - 1
        fixed |= 1 << p
        if pol < 0:                 # literal ~x_p is falsified by x_p = T
            value |= 1 << p
    return (fixed, value)


def at_residual(region, terminus):
    """True when the stratum lies at the boundary's residual terminus: the
    support is wholly fixed and fixed as the terminus demands.  Never
    presented (Theorem 22.3 PA)."""
    rf, rv = region
    sf, sv = terminus
    if sf & ~rf:                    # the support is not yet wholly oriented
        return False
    return (rv & sf) == sv


def barred(region, terminus):
    """True when the stratum fixes a content of the support opposite to the
    residual terminus's demand.  The boundary then stands at its conjugate
    terminus throughout (Axiom 2.3 PA), asserted and never presented
    (Theorem 22.3 PA)."""
    rf, rv = region
    sf, sv = terminus
    both = rf & sf
    return (rv & both) != (sv & both)


# ---------------------------------------------------------------------------
#  The order of mediation, and the bands it fixes
# ---------------------------------------------------------------------------

def order_given(n, termini):
    """The order the contents arrive in."""
    return list(range(n))


def order_closing(n, termini):
    """The order the asserted relations indicate.  Deterministic, and a
    function of the written sectors alone: no address is consulted.

    At each step the content that determines the most boundaries -- a
    boundary counting as determined when the last content of its support not
    yet ordered is taken; ties by the INCIDENCE of the content, the number of
    asserted supports containing it, which by Axiom 5.1 PA is a determinate
    feature of the assertion; then by the lowest index.
    """
    remaining = set(range(n))
    incidence = {p: sum(1 for mk, _ in termini if (mk >> p) & 1)
                 for p in range(n)}
    taken = []
    while remaining:
        best = None
        for p in sorted(remaining):
            closes = 0
            for mk, _ in termini:
                if not (mk >> p) & 1:
                    continue
                if all(q not in remaining for q in support(mk) if q != p):
                    closes += 1
            key = (closes, incidence[p], -p)
            if best is None or key > best[0]:
                best = (key, p)
        taken.append(best[1])
        remaining.discard(best[1])
    return taken


def bands(n, termini, order):
    """Each boundary's band: the depth at which the last content of its
    support is oriented, after which it is determined and above which it
    says nothing (Axiom 5.1 PA).

    Returns (genesis, out).  A boundary whose support is empty bears through
    no content at all, so by Axiom 5.1 PA it bears on the envelope itself and
    is determined at genesis, before any mediation; such boundaries are
    returned in `genesis`.  The assertion's joint content can carry one: it
    is the statement that the envelope is itself at a residual terminus, and
    hence that the composed boundary admits nothing.
    """
    pos = {p: i for i, p in enumerate(order)}
    genesis = []
    out = [[] for _ in range(n)]
    for t in termini:
        sup = support(t[0])
        if not sup:
            genesis.append(t)
        else:
            out[max(pos[p] for p in sup)].append(t)
    return genesis, out


# ---------------------------------------------------------------------------
#  The descent.  Inward only; one mediation per depth, into Axiom 5.2's two
#  mediated conjugate sectors; a residual terminus is never presented.
# ---------------------------------------------------------------------------

def compose(n, termini, order, census=None):
    """The composed boundary: the lighthouses of the asserted boundaries
    under the given order of mediation.

    Returns (family, held).  `family` is a frozenset of strata and `held` the
    greatest number of strata standing at once -- one per depth of the chain
    the descent is on, so at most n + 1 (Corollary 5.11 PA).  `census`, if a
    list is given, receives one (depth, radius) per lighthouse.

    NOTHING ELSE IS REPORTED.  The descent realizes what the assertion fixed
    at genesis (Axiom 5.3 PA: "The levels of the structure are fixed by the
    relation; iteration realizes them"), so the steps it takes on the way are
    not a feature of the assertion and are not counted.  A step that bounds
    no address has no residence (Theorem 15.1 PA) and is not a stratum of the
    structure; it is an artefact of walking the envelope rather than reading
    the boundary, and this module does not tally it.

    The result is a function of `termini` and `order` and of nothing else.
    """
    genesis, bd = bands(n, termini, order)
    held = [0]

    # A boundary determined at genesis bears on the envelope itself
    # (Axiom 5.1 PA).  If the envelope stands at a residual terminus it is
    # never presented (Theorem 22.3 PA), and the composed boundary admits
    # nothing.  Nothing is entered, so nothing is left.
    if any(at_residual((0, 0), t) for t in genesis):
        return frozenset(), 0

    def go(d, region, path):
        held[0] = max(held[0], path)

        # Definition 5.2 PA: closure is the fact of no further admissible
        # partition.  Where every asserted boundary is barred, no asserted
        # relation requires a partition within this stratum, and by
        # Axiom 5.3 PA no novel mediation is generable and none is required.
        if all(barred(region, t) for t in termini):
            if census is not None:
                census.append((d, free_count(region, n)))
            return frozenset([region])

        if d == n:
            # Unreachable: at full depth every support is wholly oriented,
            # and a stratum at a residual terminus is never presented, so
            # every boundary is barred and the branch above has returned.
            raise AssertionError("a full-depth stratum was not all-barred")

        bit = 1 << order[d]
        f, v = region
        fam = set()
        # Axiom 5.2 PA: the Between partitions the interior into the two
        # mediated conjugate sectors.  Both are the partition; neither is
        # chosen.  One mediation, one level of capacity (Axiom 5.3 PA).
        for orient in (bit, 0):
            sector = (f | bit, v | orient)
            # Theorem 22.3 PA: a residual terminus stands asserted but is
            # never presented, and by Theorem 22.1 PA presentation is
            # generated only by allocation.  An unpresented sector is not
            # entered, so it is never left.
            if any(at_residual(sector, t) for t in bd[d]):
                continue
            fam |= go(d + 1, sector, path + 1)
        return frozenset(fam)

    return go(0, (0, 0), 1), held[0]


# ---------------------------------------------------------------------------
#  Reading a lighthouse.  THE ONLY PLACE AN ADDRESS APPEARS.
#
#  This performs no test.  Every address of a lighthouse stands, so the
#  reading emits the answer and rejects nothing.  It is charged to nothing:
#  by Theorem 15.1 PA a configuration resides independently of any act of
#  selection, retrieval or observation, and the cost of a configuration is
#  the length of its path.
# ---------------------------------------------------------------------------

def read_region(region, n):
    """Every address of a stratum, by orienting the contents it leaves free."""
    fixed, value = region
    free = [p for p in range(n) if not (fixed >> p) & 1]
    for mask in range(1 << len(free)):
        a = value
        for i, q in enumerate(free):
            if (mask >> i) & 1:
                a |= 1 << q
        yield a


def region_str(region, n):
    """A stratum written out: T, F, or * for a content it leaves free."""
    fixed, value = region
    return "".join(("T" if (value >> p) & 1 else "F")
                   if (fixed >> p) & 1 else "*" for p in range(n))
