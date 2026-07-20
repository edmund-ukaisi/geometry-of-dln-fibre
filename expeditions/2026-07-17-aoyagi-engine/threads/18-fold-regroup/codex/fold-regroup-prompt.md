# Independent derivation request: a fold of monomial blow-up charts and its Jacobian

You are an exact-algebra second opinion. Derive from scratch; I withhold my own conclusions.

## The objects (all exact / symbolic; no floating point)

We work with points in R^N whose coordinates are indexed by "flat cells" (think matrix entries). Write
z_c(x) for the value of coordinate/cell c at point x. A source point w has fresh independent
coordinates z_c(w).

A **blow-up chart** is specified by a finite set C of cells (the "center") and a distinguished pivot
cell pi in C. As a self-map of R^N it acts by (max-modulus normalization):

    z_pi |-> z_pi                         (the pivot coordinate is free)
    z_c  |-> z_pi * z_c    for c in C, c != pi     (every OTHER center coordinate is scaled by the pivot)
    z_c  |-> z_c           for c not in C          (spectator coordinates unchanged)

A **path** is a sequence of nodes node_1, ..., node_m (node_1 = "root", node_m = "deepest"). Each node
j has a center C_j and pivot pi_j. The **composite** map is applied to a source point w with the
DEEPEST node first and the ROOT last:

    Phi(w) = chart_1( chart_2( ... chart_m(w) ... ) )         (root outermost).

## The recursion that generates the nodes (a resolution ledger)

The nodes come from a resolution recursion with a state carrying: a set of "live divisors", each a
cell together with an integer exponent divExp, plus a running residual block. There are three node
kinds (each is one node with an explicit center + pivot):

- **case-2 (birth):** blow up a fresh rows x cols residual block. Center = the block's rows*cols cells.
  It BIRTHS a new divisor whose cell is the chosen pivot, with divExp := rows*cols. dim(center)=rows*cols.
- **case-1(2) (split):** center = { u } ∪ { a fresh runLen x resCols block }, where u is the cell of an
  ALREADY-LIVE divisor ("mergeIdx"). The pivot is one of the fresh block cells. It BIRTHS a new divisor
  at that pivot with divExp := divExp(mergeIdx) + runLen*resCols. mergeIdx stays live, unchanged exponent.
  dim(center) = 1 + runLen*resCols.
- **case-1(1) (merge):** center = { u } ∪ { a fresh runLen x resCols block }, u = an already-live
  divisor's cell (mergeIdx). The pivot is u itself. NO new divisor: instead divExp(mergeIdx) +=
  runLen*resCols. dim(center) = 1 + runLen*resCols.

An already-live divisor referenced as "u" (mergeIdx) is referenced by its canonical BIRTH cell (a fixed
diagonal cell recorded when it was born), which need not equal the pivot cell that geometrically birthed
it if the birth was a case-2/case-1(2) at an off-center pivot.

Root nodes are shallow (few divisors cleared); deeper nodes have cleared more. A divisor is born at
some node and may later (at DEEPER nodes) be merged into (case-1(1)) or split (case-1(2)).

## The per-node atom (given, from a determinant computation you may take as known)

For a single chart with center C and pivot pi, the Jacobian determinant over the center coordinates is
z_pi^{|C|-1} (spectators contribute 1). So by the chain rule the composite's Jacobian determinant is a
product over nodes of  z_{pi_j}(y_j)^{|C_j|-1}, where y_j is the image of w under all DEEPER charts
(nodes j+1..m). This is at an INTERMEDIATE point y_j, not at source w.

## The QUESTIONS (derive independently, exactly)

Q1. For each node j, express z_{pi_j}(y_j) — the pivot coordinate read at the intermediate point — as
    a monomial in the SOURCE coordinates z_.(w). In particular: which deeper nodes, if any, cause
    z_{pi_j}(y_j) to differ from z_{pi_j}(w)? Give the exact product.

Q2. Define, for the leaf, the "ledger monomial" prod over live divisors k of z_{coord_k}(w)^{divExp_k - 1},
    with coord_k the divisor's cell and divExp_k the accumulated exponent. Is the composite Jacobian
    determinant EQUAL to this ledger monomial? Prove it or exhibit the smallest counterexample.
    Work a concrete small instance end to end: (a) case-2 births A (say a 2x2 block, so divExp(A)=4),
    then a deeper case-1(2) splits a new divisor e off A. Compute the composite Jacobian in source
    coordinates and compare to z_A^{4-1} * z_e^{divExp(e)-1}.

Q3. In the instance of Q2, WHERE does the divExp(mergeIdx) contribution to the new split-divisor's
    exponent come from — the split node's own atom, or some other node's atom? Be specific.

Q4. Consider case-2 birthing a 2x2 block at an OFF-diagonal pivot cell, followed by a deeper case-1(1)
    that merges into that divisor referencing its DIAGONAL birth cell (not the off-diagonal pivot).
    Does the composite Jacobian still equal the ledger monomial (which names the off-diagonal pivot as
    the divisor's cell)? If not, what is the exact discrepancy, and what condition on births would
    restore the equality?

Give exact monomials throughout. State any assumption you make about the recursion.
