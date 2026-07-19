# Independent check: a threaded ledger invariant for a fold of normalized blow-up charts

Derive from scratch; I withhold my own conclusions.

## Objects (exact / symbolic)

Coordinates z_c(x) index "flat cells" c of a point x. Two building maps on cells:
- swap(a,b): exchanges the values at cells a and b (a linear involution, det = -1).
- blowup(C, p): for a finite center set C and pivot p in C: z_p |-> z_p; z_c |-> z_p*z_c for c in C\{p};
  z_c |-> z_c for c not in C.

A **normalized chart** for an edge is  B = blowup(C, p) o swap(p, d),  where p (the "pivot cell") and d
(the "diagonal target cell") both lie in C. Its Jacobian determinant modulus is |det D B (w)| =
|z_d(w)|^{|C|-1} (the exceptional divisor is relocated to the diagonal d by the swap).

A path is a sequence of edges from a root state; the composite chart is fold(B_1, ..., B_m) with B_1
(root) OUTERMOST: Phi(w) = B_1(B_2(...B_m(w)...)).

## The recursion / ledger (a resolution)

A state s carries a list of "live divisors", each a DIAGONAL cell `diag` and an integer exponent divExp.
Edges (each adds one normalized chart B and advances the state):
- **case-2 (birth):** C = a fresh block (|C| = rows*cols), disjoint from all existing divisor diagonals;
  d = a fresh diagonal cell in C; p = some cell of C. Appends a new divisor (diag = d, divExp = |C|).
- **case-1(1) (merge):** C = { u } ∪ (fresh block), u = an existing divisor's diagonal cell (mergeIdx);
  p = u and d = u (so swap is the identity). divExp(mergeIdx) += (|C| - 1). No new divisor.
- **case-1(2) (split):** C = { u } ∪ (fresh block), u = an existing divisor's diagonal (mergeIdx);
  p = a fresh block cell, d = a fresh block diagonal cell (p, d distinct from u and from all existing
  diagonals). Appends a new divisor (diag = d, divExp = divExp(mergeIdx) + (|C| - 1)). mergeIdx unchanged.
- **rollover:** no chart, no change to the divisor list.

Existing divisor diagonals are pairwise distinct and (freshness) never lie in a later edge's fresh block.

## Define L(s)(x) := prod over live divisors k of |z_{diag_k}(x)|^{divExp_k - 1}.

## QUESTIONS (derive independently, exactly)

Q1. Fix an edge with chart B advancing state s to s'. Compute L(s)(B(w)) — the OLD ledger monomial
    evaluated at the image B(w) — as a monomial in source coordinates z_.(w), for each of the four edge
    kinds. (I.e. how does each existing divisor's diagonal coordinate pull back through B?)

Q2. Is it true that for every edge kind,  L(s)(B(w)) * |z_d(w)|^{|C|-1} = L(s')(w)  (with the case-2 /
    case-1 diagonal target d; rollover has no chart, |det|=1)? Prove it or give the smallest counterexample.
    Pay special attention to case-1(2): does the factor |z_d|^{divExp(mergeIdx)-1} appear, and if so from
    which term?

Q3. Conclude (or refute): defining Inv(acc, s) := "|det D acc (w)| = L(s)(w) for all w", with base
    acc = id at the root (empty divisor list, L = 1), does Inv propagate along every edge to
    acc' = acc o B, s'? State exactly what the induction needs.

Q4. Work one concrete depth-3 mixed run end to end (case-2 births A with a 2x2 block; case-1(2) splits B
    off A with a size-2 block; case-1(1) merges into B with a size-1 block). Give L at each state and the
    composite |det D Phi| in source coordinates, and check they agree.

Exact monomials throughout. State any assumption you rely on (freshness, disjointness).
