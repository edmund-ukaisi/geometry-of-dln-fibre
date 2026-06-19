# Thread 03 - block and product reduction

Type: formalisation. Status: in-progress.

## Task

Formalise Aoyagi's elementary matrix reductions: the full-rank block elimination
and product reduction.

## Output contract

- Lean statements for Claim A1 and Claim A2 at exact scope.
- Proofs where elementary; any analytic/local hypotheses named explicitly.
- Statement cards at AUDIT time.

## Controller notes

Read `lean/CLAUDE.md` before Lean work. Keep Aoyagi/DLN application code out of
`DLNFibre.Core`.

## 2026-06-18 A1 narrow tide

Opened xhigh worker tide `Lovelace` for the first Lean implementation. Scope is
only Aoyagi Lemma 2's checked algebraic block-elimination chart identity, and
possibly the rank formula if it falls out without overclaiming. Explicitly out
of scope: RLCT invariance, local-germ/ideal consequences, Theorem 3 product
reduction, and target-normalisation claims.

Read-only xhigh statement reviewer `Euclid` was also opened to audit the exact
statement shape before controller acceptance.

Outcome: landed two algebraic block identities in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`:
`schurComplement_leftBlockElim_fromBlocks` and
`schurComplement_blockElim_fromBlocks`. Theorems are over `[CommRing K]` with
explicit chart hypothesis `IsUnit A1.det`, and contain no rank/RLCT/germ/ideal
claim. Controller verified targeted build, full `DLNFibre` build, and
`scripts/sorries`. Statement card:
`statement-card-a1-block-identities.md`.

Remaining A1 target: rank formula as a separate theorem, likely via a
block-diagonal rank lemma over a field. A2 remains blocked by the checker
findings: source-faithful basis/open-chart hypotheses and analytic-boundary
decision.

## 2026-06-18 A1 rank-formula tide

Opened xhigh worker tide `Lovelace` to prove a separate block-diagonal rank
theorem and then the Schur-complement rank corollary. Scope remains purely
algebraic: no RLCT/germ/ideal/Theorem 3 claim.

Outcome: landed `rank_fromBlocks_zero_zero` and
`rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det` in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`. Controller verified targeted
build, full `DLNFibre` build, and `scripts/sorries`. Xhigh reviewer `Euclid`
accepted after minor docstring/name edits. Rank statement card:
`statement-card-a1-rank-formula.md`.

## 2026-06-18 A2 repair scout

Opened xhigh read-only scout `Erdos` to repair the pen-and-paper reproduction of
Aoyagi Theorem 3/product reduction before any A2 Lean target. The requested
output is a source-faithful algebraic statement, induction invariant, boundary
case analysis, and separation of analytic/RLCT assumptions.

Outcome: report saved at `reproduction-repair-a2.md`. Verdict: full Theorem 3
is still blocked, but the chart-local algebraic induction-step theorem is
reproduction-ready for Lean. The target-product normalization and post-Theorem-3
RLCT equality remain analytic-boundary issues.

## 2026-06-18 A2 chart-local induction-step tide

Opened xhigh formalisation work on only the reproduction-ready chart-local
algebraic induction step from the A2 repair report. Scope is the block identity
for a prefix diagonal block `fromBlocks C1 0 0 D` multiplied by the next
transformed layer `fromBlocks A1 A2 A3 A4`, under explicit determinant-unit
chart hypotheses for `C1` and `A1`.

Outcome: landed
`DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks` in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`, imported by the single-writer
aggregator. The theorem proves only the chart-local algebraic block identity:
left lower-left multiplier `-(D * A3 * (C1 * A1)⁻¹)`, right upper-right
multiplier `-(A1⁻¹ * A2)`, and residual block
`D * (A4 - A3 * A1⁻¹ * A2)`. It includes an identity-corner example showing
the determinant-unit chart hypotheses are inhabited, including zero-size
corners.

Controller verified targeted build, full `DLNFibre` build, `scripts/sorries`,
and `#print axioms` for the theorem. Xhigh hardener `Jason` and xhigh fidelity
reviewer `Huygens` passed the artifact at this narrow scope. Statement card:
`statement-card-a2-chart-local-induction-step.md`.

Still blocked: full Aoyagi Theorem 3 from source rank/neighborhood hypotheses,
through-layer basis/open-chart existence, target-product normalization via
Aoyagi Lemma 1, local analytic/ideal-germ invariance, regular-coordinate RLCT
additivity, and every final RLCT consequence.

## 2026-06-18 A2 matrix-entry ideal tide

After the analytic-interface repair, opened the next elementary transport
target: matrix-entry ideal algebra for the post-Theorem-3 block generators.
Scope is algebraic ideals over a commutative ring only. Explicitly out of
scope: analytic germs, local coordinate invariance, normal-crossing
certificates, RLCT equality, and pole-order consequences.

Outcome: landed `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`, imported by the
single-writer aggregator. Main theorems:

- `matrixEntryIdeal_mul_left_eq_of_isUnit_det`;
- `matrixEntryIdeal_mul_right_eq_of_isUnit_det`;
- `matrixEntryIdeal_mul_le_sup`;
- `fourMatrixEntryIdeal_sub_mul_eq`.

The last theorem proves the elementary cleanup

```text
<entries X, entries F2, entries F3, entries (D - F3 F2)>
  = <entries X, entries F2, entries F3, entries D>.
```

The file includes identity-multiplier examples witnessing the determinant-unit
hypotheses. Controller verified targeted build, full `DLNFibre` build,
`scripts/sorries`, and `#print axioms` for the main theorems. Xhigh fidelity
reviewer `Dalton` and xhigh hardener `Linnaeus` passed the artifact at the
elementary algebraic scope. Statement card: `statement-card-a2-entry-ideal.md`.

Still blocked: the same algebraic ideal does not by itself imply the same RLCT.
The final route must construct or transport a normal-crossing certificate before
using the single extraction citation.

## 2026-06-18 A2 through-layer basis reproduction

Opened xhigh pen-and-paper scout `Gibbs` to reproduce the missing
through-layer basis/open-chart lemma, then xhigh checker `Hooke` to audit it.
Report saved at `through-layer-basis-reproduction.md`.

Verdict: product rank `r` is enough to choose bases existentially so the true
layer maps have block form `[I B; 0 D]` and the Aoyagi induction charts contain
the base point. Product rank is not enough for a preselected fixed chart; the
report records counterexamples. This is an auxiliary elementary
linear-algebra repair, not a source-stated Aoyagi lemma and not an analytic
claim.

Lean-ready now: the field-linear through-subspace existence lemma, and the
local unitriangular chart-stability block calculation. Full Theorem 3 remains
blocked until this basis lemma is formalised and connected to the already
landed chart-local induction identity.

Outcome for the local calculation: landed
`DLNFibre.DLN.Aoyagi.upperUnitriangular_mul_fromBlocks_one_zero` in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`. It proves

```text
[I -F; 0 I] [I B; 0 D] = [I B - F D; 0 D].
```

Controller verified targeted build, full `DLNFibre` build, `scripts/sorries`,
and `#print axioms`. Statement card:
`statement-card-a2-unitriangular-chart.md`.

## 2026-06-19 A2 through-subspace Lean layer

Landed the elementary through-subspace theorem in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`.

Main Lean artifacts:

- `chainMap`, `chainMap_succ`, `chainMap_trans`: source-to-target composites
  for an upward finite chain `A i : V i.castSucc -> V i.succ`.
- `exists_chain_throughSubspaces`: chooses `U0` complementary to the total
  kernel and defines through-subspaces `U j` as prefix images; proves edge
  transport, suffix-kernel disjointness, constant finrank equal to the total
  range finrank, and `U last = range total`.
- `throughSubspaceEdgeEquiv` and `throughSubspaceEdgeEquiv_apply`: each edge
  restricts to a linear equivalence between adjacent through-subspaces, induced
  by the original edge map.

Orientation note: this Lean chain runs from `V 0` to `V (Fin.last N)`. It is
Aoyagi's chain after reversing the paper-order maps
`A^(s) : V_(s+1) -> V_s`.

Xhigh reviewers `Nietzsche` and `Pascal` accepted the statement scope. Caveats:
this is not a fixed-coordinate chart theorem, does not choose complements to
the through-subspaces, and does not itself produce basis matrices. The next
target is the complement/direct-sum and chain-level matrix packaging needed to
connect this subspace layer to the already-proved chart-local product reduction
identity.

Statement card: `statement-card-a2-through-subspaces.md`.

## 2026-06-19 A2 through-matrix block Lean layer

Landed the per-edge transported-basis matrix block theorem in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`, imported by the single-writer
aggregator.

Main Lean artifacts:

- `exists_toMatrix_sumQuot_eq_fromBlocks_one_zero`: for a linear map `f : E -> F`
  whose restriction to `U` is a specified equivalence `U ≃ U'`, transported
  `Module.Basis.sumQuot` bases put the matrix of `f` in block form
  `fromBlocks 1 B 0 D`.
- `exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`:
  specialization to an edge `A p : V p.castSucc -> V p.succ` using
  `throughSubspaceEdgeEquiv`.
- `basisOfIsCompl`: builds an ambient basis from bases of complementary
  subspaces using `Submodule.prodEquivOfIsCompl`.
- `exists_toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero`: generic direct-sum
  adapted-basis block theorem.
- `exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`:
  through-edge specialization in supplied complement/direct-sum bases.

This checkpoint proves basis-coordinate bookkeeping only: transported
through-subspace bases give the identity top-left block, and subspace
membership gives the zero lower-left block. Quotient bases, complements, and
complement bases are explicit inputs. It is not a fixed-coordinate chart
theorem, does not package simultaneous chain bases, and does not prove Aoyagi
Theorem 3 or any analytic/RLCT consequence.

Statement card: `statement-card-a2-through-matrix-block.md`.

## 2026-06-19 A2 endpoint total-product block

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with the endpoint
normalization theorem for the whole chain.

Main Lean artifacts:

- `toMatrix_basisOfIsCompl_eq_fromBlocks_one_zero_zero_of_map_complement_eq_zero`:
  generic direct-sum theorem saying that if the source complement maps to zero,
  the matrix is `fromBlocks 1 0 0 0` in transported direct-sum bases.
- `toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero`:
  specialization to the total composite `chainMap V A 0 (Fin.last N) ...`,
  with source decomposition `U₀ ⊕ ker P` and target decomposition
  `throughSubspace last ⊕ Wlast`.

This proves only endpoint matrix normalization. It does not package one
simultaneous family of bases at every intermediate layer, does not translate
orientation back to Aoyagi paper order, and does not yet connect the endpoint
and per-edge block forms to the chart-local product-reduction identity.

Statement card: `statement-card-a2-total-product-block.md`.

## 2026-06-19 A2 prefix-compatible edge bases

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with the prefix
transport package:

- `disjoint_ker_chainMap_prefix_of_disjoint_ker_total`: a subspace disjoint
  from the total kernel is disjoint from every prefix kernel.
- `throughSubspacePrefixEquiv` and `throughSubspacePrefixEquiv_apply`:
  transport from the initial through-subspace `U₀` to `throughSubspace ... j`
  by the prefix chain map.
- `throughSubspacePrefixEquiv_succ_apply`: adjacent prefix transports are
  related by the edge map.
- `exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`:
  a through-layer edge has matrix form `fromBlocks 1 B 0 D` when the top bases
  at both endpoints are obtained by transporting one common initial basis of
  `U₀`.

This proves compatibility of the top/through bases across layers. It still
takes local complements and complement bases as inputs for the source and target
of a single edge. It does not yet bundle complement data across all layers, run
the chart-local product-reduction induction, or state any analytic/RLCT
consequence.

## 2026-06-19 A2 unitriangular chart-form corollary

Extended `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` with
`exists_fromBlocks_one_zero_of_upperUnitriangular_mul`. The theorem packages the
already-proved identity

```text
[I -F; 0 I] [I B; 0 D] = [I B - F D; 0 D]
```

as an existential chart-form preservation statement: if a matrix has some
identity-corner, zero-lower-left block form, then the upper-unitriangular left
multiplier leaves it in some such form.

This is still pure block algebra over a commutative ring. It does not run the
product-reduction induction, choose the complement data supplied to the
through-layer matrix theorems, or state analytic/RLCT consequences.

## 2026-06-19 A2 supplied chart-data bundle

Extended the matrix/chart layer with indexed and bundled forms:

- `upperUnitriangular_mul_fromBlocks_one_zero_indexed` and
  `exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed` generalize the
  unitriangular chart-form lemmas from `Fin` dimensions to arbitrary finite
  basis index types.
- `ThroughSubspaceChartData` bundles, for every layer, a complement to the
  through-subspace and a basis of that complement, together with one initial
  through-basis.
- `exists_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
  restates the prefix-compatible edge block theorem using the bundled data.
- `exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
  combines the bundled edge matrix form with the indexed unitriangular
  chart-preservation lemma.

This is still a supplied-data theorem. It does not itself construct finite
indexed complement data, does not run the product-reduction induction, and does
not state analytic/RLCT consequences.

## 2026-06-19 A2 finite chart-data existence

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with the
finite-dimensional existence layer:

- `throughSubspaceComplement` and `throughSubspace_isCompl_complement` choose
  and verify a complement to each transported through-subspace.
- `throughSubspaceComplementIndex` indexes each chosen complement by
  `Fin (Module.finrank K ...)`.
- `throughSubspaceChartDataOfFiniteDimensional` constructs concrete
  finite-indexed chart data for any chosen initial through-subspace `U₀`, using
  `Module.finBasis` for the initial subspace and complements.
- `exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`
  additionally chooses `U₀` complementary to the total kernel and preserves the
  earlier `finrank U₀ = finrank range P` equality.

This proves the elementary finite-dimensional supplied-data construction needed
by the through-basis repair. It does not prove Aoyagi's fixed-coordinate chart
claim, the paper-order rank/open-neighborhood bridge, the product-reduction
induction, or any analytic/RLCT consequence.

## 2026-06-19 A2 concrete finite-basis block corollaries

Added concrete finite-dimensional wrappers around the supplied-data block
theorems:

- `exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`
  instantiates the per-edge `[I B; 0 D]` theorem with the chosen complements
  and `Module.finBasis` bases from `throughSubspaceChartDataOfFiniteDimensional`.
- `exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`
  instantiates the unitriangular chart-preservation theorem with the same
  concrete finite indices.
- `toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
  instantiates the endpoint `[I 0; 0 0]` theorem using `Module.finBasis` for
  `U₀`, `ker P`, and the chosen target complement.

These are still adapted-coordinate statements. They do not identify Aoyagi's
paper-order top-left coordinate blocks, prove rank-open neighborhoods, run the
induction, or state analytic/RLCT consequences.

## 2026-06-19 A2 paper-order bridge notes

Added `paper-order-bridge-notes.md` recording the source-to-Lean direction
reversal:

```text
V_j = W_(L+1-j),    Lean edge j = paper layer s = L-j.
```

The note identifies the next elementary bridge obligations: a reindexing lemma,
a finite chart-data-to-paper-block wrapper, a determinant-open chart statement,
the paper-order induction assembly, and optional rank corollaries. It also
records nonclaims: this does not prove Theorem 3, does not make the Lemma 1
normalization elementary, and does not justify the post-Theorem-3 RLCT shift.

## 2026-06-19 A2 paper-order chain composite

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean` with
`paperChainMap`, a descending composite for Aoyagi-order maps
`B p : W p.succ -> W p.castSucc`.

The proved API is:

- `paperChainMap_self`: the empty paper-order composite is the identity.
- `paperChainMap_succ`: extending the upper endpoint composes the new paper
  edge on the right.
- `paperChainMap_edge`: a one-edge paper-order composite is the edge itself.
- `paperChainMap_trans`: the composite splits at an intermediate vertex as
  prefix composed with suffix.
- `paperChainMap_zero_last_eq_prefix_comp_suffix`: the full product splits as
  paper prefix followed by paper suffix.

This is only product-order bookkeeping. It does not transfer adapted block
forms to paper notation, run the product-reduction induction, or state
analytic/RLCT consequences.

## 2026-06-19 A2 reversed-chain bridge

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean` with the formal
source-to-paper orientation bridge:

- `rev_succ_eq_rev_castSucc`, `rev_castSucc_eq_rev_succ`, and
  `rev_succ_le_rev_castSucc`: the `Fin.rev` endpoint bookkeeping for a reversed
  edge.
- `reverseVertex`: the paper-order vertex family viewed in source-to-target
  order.
- `reverseEdge`: the one-edge paper-order composite viewed as a
  source-to-target edge.
- `chainMap_reverse_eq_paper`: the composite `chainMap` on reversed vertices is
  exactly the corresponding `paperChainMap`.

This removes the orientation mismatch between the Lean through-subspace chain
and Aoyagi's printed product order. It still does not transfer the finite
adapted-basis block corollaries into paper notation, prove determinant-open
chart wrappers, run the product-reduction induction, or state analytic/RLCT
consequences.

## 2026-06-19 A2 paper-order finite matrix blocks

Extended `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean` with finite
paper-order matrix wrappers:

- `disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`: converts a
  disjointness hypothesis for the paper-order total product into the reversed
  source-to-target total-kernel hypothesis, using `chainMap_reverse_eq_paper`.
- `isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`: the matching
  complement-hypothesis bridge.
- `exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`:
  instantiates the concrete finite edge block theorem on `reverseVertex W` and
  `reverseEdge W B`.
- `exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`:
  gives the corresponding unitriangular chart-form preservation wrapper.
- `toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`:
  gives the endpoint `[I 0; 0 0]` form for the total paper product.

This transfers the finite adapted-basis edge and endpoint statements into the
paper-order orientation. It still does not provide determinant/open chart
wrappers, the product-reduction induction, or analytic/RLCT consequences.

## 2026-06-19 A2 indexed block algebra

Extended the pure block algebra layer with indexed variants:

- `schurComplement_leftBlockElim_fromBlocks_indexed`;
- `schurComplement_blockElim_fromBlocks_indexed`;
- `productReduction_chartLocalInductionStep_fromBlocks_indexed`.

These are the same identities as the existing `Fin`-indexed A1/A2 block
theorems, but stated for arbitrary finite block index types. This is
infrastructure for chart-data assembly only; it does not prove the
product-reduction induction or any analytic consequence.

## 2026-06-19 A2 determinant chart predicates

Added a non-topological determinant-chart predicate layer:

- `topLeftCorner`;
- `identityCornerForm`;
- `identityCornerDetChart`;
- `topLeftCorner_eq_one_of_identityCornerForm`;
- `identityCornerDetChart_of_identityCornerForm`;
- `identityCornerForm_upperUnitriangular_mul`.

Then named the adapted paper edge matrix as `paperAdaptedReverseEdgeMatrix` and
the corresponding upper-unitriangular multiplier as `paperUnitriangularLeft`.
Theorems now state that the adapted paper edge matrix has identity-corner form,
selected top-left corner `1`, and determinant-chart membership; the
unitriangularly transformed matrix also has identity-corner form and
determinant-chart membership.

This is algebraic `IsUnit` at the adapted base matrix. It is not a topological
open-neighborhood theorem, not a fixed-coordinate chart theorem, and not a
rank or RLCT statement.

## 2026-06-19 A2 one-edge right elimination

Added the explicit indexed algebraic theorem
`productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`:

- a block-diagonal prefix `fromBlocks C1 0 0 Dprev`;
- followed by the witnessed identity-corner edge `fromBlocks 1 B 0 Dnext`;
- followed by a right unitriangular source-side multiplier
  `fromBlocks 1 (-B) 0 1`;
- equals a new block-diagonal prefix `fromBlocks C1 0 0 (Dprev * Dnext)`.

Also added the equality corollary
`productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`
and the convenience wrapper
`productReduction_blockDiagonal_mul_identityCornerForm_rightElim`, which
packages the witness through `identityCornerForm`.

No determinant-unit hypothesis is needed in this identity because the next edge
has top-left corner exactly `1`; no inverse or Schur complement is used.

Added the paper-order corollary
`productReduction_paperAdaptedReverseEdgeMatrix_rightElim`. For
`paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p`, rows are indexed by
`Fin (finrank U₀) ⊕ κ p.succ` and columns by
`Fin (finrank U₀) ⊕ κ p.castSucc`, where
`κ j = throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j`.
Thus `Dprev` has columns `κ p.succ`, `Dnext` has rows `κ p.succ` and columns
`κ p.castSucc`, and the right multiplier's lower identity is on `κ p.castSucc`.

This is still one-edge algebra. Full product assembly remains blocked on a
shared adapted basis family whose endpoint source complement is the total
kernel; the current concrete finite edge wrappers use automatically chosen
complements at every vertex, while the endpoint total-product theorem uses
`ker P` as the source complement.

## 2026-06-19 A2 endpoint-compatible chart data

Added a named shared adapted basis family:

- `throughSubspaceAdaptedBasis`.

Using that basis family:

- `exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero`
  restates the edge `[I B; 0 D]` theorem with the named basis at adjacent
  vertices.
- `toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`
  states the endpoint `[I 0; 0 0]` theorem for any supplied chart data whose
  source complement maps to zero under the total product.

Then added endpoint-compatible finite chart data:

- `throughSubspaceEndpointComplement`: source complement is the total kernel,
  other complements are chosen arbitrarily;
- `throughSubspaceEndpointComplementIndex`;
- `throughSubspaceEndpointChartDataOfFiniteDimensional`;
- `exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional`;
- `toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero`;
- `endpointChartData_edge_and_totalProduct_blocks`.

Finally added paper-order wrappers:

- `exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional`;
- `paperEndpointChartData_edge_and_totalProduct_blocks`.

This removes the previous endpoint-basis mismatch: one edge matrix and the
total product matrix can now be stated in the same endpoint-compatible adapted
basis family, including in paper order. It still does not prove that the
ordered product of all edge matrices equals the endpoint total matrix in this
basis family, and it does not run the product-reduction induction.

## 2026-06-19 A2 adapted matrix composition

Added generic supplied-data matrix names:

- `throughSubspaceAdaptedChainMapMatrix`;
- `throughSubspaceAdaptedEdgeMatrix`.

Added the one-step composition theorem
`throughSubspaceAdaptedChainMapMatrix_succ`. For `i ≤ p.castSucc`, the matrix
of `chainMap i p.succ` in the supplied adapted bases is

`throughSubspaceAdaptedEdgeMatrix p *
throughSubspaceAdaptedChainMapMatrix i p.castSucc`.

This is the matrix form of `chainMap_succ`, using Mathlib
`LinearMap.toMatrix_comp`. The order is edge-on-the-left and prefix-on-the-right
for the source-to-target Lean chain. This is not yet an all-layer product
theorem and does not use the endpoint-compatible data specifically.

## 2026-06-19 A2 adapted edge-product theorem

Added a dependent recursive product of adapted edge matrices:

- `throughSubspaceAdaptedEdgeProductMatrix`;
- `throughSubspaceAdaptedEdgeProductMatrix_self`;
- `throughSubspaceAdaptedEdgeProductMatrix_succ`.

The recurrence is the same edge-on-left order as the chain-map matrix:

`edge p * edgeProduct i p.castSucc`.

Added `throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix`, proving for
any interval `i ≤ j` that the adapted matrix of `chainMap i j` equals this
dependent edge product. Added prefix/endpoint corollaries:

- `throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix`;
- `toMatrix_chainMap_zero_last_eq_adaptedEdgeProductMatrix`.

This closes the composition-only gap between one-edge adapted matrices and the
endpoint total-product matrix in a supplied adapted basis family. It still does
not run Aoyagi's product-reduction induction or assert any analytic/RLCT
consequence. The next algebraic assembly layer needs right-oriented suffix
composition and canonical block projections for the one-edge elimination step.

## 2026-06-19 A2 right-elimination assembly API

Added deterministic block projections in `ProductReduction.lean`:

- `upperRightBlock`;
- `lowerRightBlock`.

Added deterministic right-elimination wrappers:

- `productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`;
- `productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`.

These turn an `identityCornerForm M` hypothesis into the concrete elimination
identity using `upperRightBlock M` as the right multiplier and
`lowerRightBlock M` as the residual edge block. The unitriangular version first
left-multiplies by `[I -F; 0 I]`, using the already proved chart-form
stability theorem.

Added the suffix-oriented adapted matrix composition theorem
`throughSubspaceAdaptedChainMapMatrix_succ_right` in `ThroughLayerMatrix.lean`:
for `p.succ ≤ j`, the matrix of `chainMap p.castSucc j` is

`throughSubspaceAdaptedChainMapMatrix p.succ j *
throughSubspaceAdaptedEdgeMatrix p`.

This is the direction needed by right-elimination induction. It is still only
composition/block algebra; it does not yet prove the abstract suffix-chain
reduction theorem.

## 2026-06-19 A2 suffix-chain right elimination

Added cancellation and suffix-step algebra in `ProductReduction.lean`:

- `upperUnitriangular_neg_mul_upperUnitriangular`;
- `upperUnitriangular_neg_mul_upperUnitriangular_neg_neg`;
- `productReduction_identityCorner_suffixStep_rightElim`.

The suffix-step theorem proves the induction step: from a reduced suffix
`Ptail * [I -Bprev; 0 I] = [I 0; 0 Dprev]` and an identity-corner edge `E`,
one gets `Ptail * E * [I -B; 0 I] = [I 0; 0 D]` for suitable `B, D`.

Added the abstract chain theorem
`productReduction_identityCorner_suffixChain_rightElim`. It assumes:

- identity empty segments;
- suffix composition `P p.castSucc j = P p.succ j * E p`;
- identity-corner form for every edge `E p`;
- proof-irrelevance of `P i j h` in the proof `h : i ≤ j`.

The theorem returns existence of a source-side upper-unitriangular right
multiplier putting `P i j` in block-diagonal form `[I 0; 0 D]`.

Added supplied adapted-basis wrappers in `ThroughLayerMatrix.lean`:

- `throughSubspaceAdaptedChainMapMatrix_proof_irrel`;
- `throughSubspaceAdaptedChainMapMatrix_self`;
- `identityCornerForm_throughSubspaceAdaptedEdgeMatrix`;
- `productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`.

This is the first full chain-level product-reduction algebra for supplied
through-subspace adapted bases. It is still not full Aoyagi Theorem 3: no
paper-order endpoint wrapper, rank/open chart bridge, target normalization, or
analytic/RLCT consequence is asserted here.

Xhigh review found no blocking orientation issue. The review confirmed the
unitriangular signs, the backward suffix induction order, and the supplied
adapted-basis wrapper. It flagged the key source-fidelity boundary: this is a
pointwise theorem for an already supplied adapted basis family, with bases
depending on the actual chain. It does not yet provide fixed coordinate charts
over a neighborhood, regular `P1`/`P2`, rank/open-chart hypotheses, endpoint
kernel normalization as a paper-facing statement, or any RLCT/generator
transport.

## 2026-06-19 A2 paper endpoint suffix-chain wrapper

Added
`productReduction_paperChainMap_endpointChartData_suffixChain_rightElim` in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`.

The theorem works in Aoyagi paper order for maps `B p : W p.succ -> W
p.castSucc`. It reverses the paper chain via `(reverseVertex W) (reverseEdge W
B)`, uses endpoint-compatible finite chart data from an explicit complement
`IsCompl U0 (ker totalPaperProduct)`, and states that the adapted matrix of the
full `paperChainMap` admits a source-side upper-unitriangular right elimination:

`paperTotalMatrix * [I -Bmat; 0 I] = [I 0; 0 Dmat]`.

The proof is a thin wrapper around
`productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`
plus `chainMap_reverse_eq_paper`. This closes the paper-order endpoint
packaging gap for the supplied-data algebra. It remains pointwise and
adapted-coordinate only: no fixed coordinate neighborhood, openness/rank chart,
regular coordinate-change, named residual-factor identification, or RLCT
consequence is claimed.

## 2026-06-19 A2 rank/open split

Added rank bridge helpers in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`:

- `rank_toMatrix_eq_finrank_range`;
- `rank_schurComplement_eq_sub_rank_fromBlocks`.

Added the paper adapted-edge residual-rank corollary in
`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`:

- `lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub`.

It proves that the lower-right residual block of an adapted paper-order edge
has rank

`finrank range(reverseEdge W B p) - finrank U0`.

Added `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`, imported by the aggregator.
It proves:

- `isOpen_identityCornerDetChart`;
- `identityCornerDetChart_mem_nhds`;
- `identityCornerForm_mem_nhds_identityCornerDetChart`;
- `paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`;
- `unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`.

This is the first honest topological bridge: determinant nonvanishing defines
an open chart around the adapted base matrices. Exact rank is not claimed to be
open. The current paper adapted bases still depend on the actual chain `B`, so
the remaining source-faithful local theorem needs fixed basepoint chart data
and variable-layer matrices expressed in those fixed bases.

## 2026-06-19 A2 endpoint basepoint certificate

Added `lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean` and imported it in
the aggregator. The module names the endpoint-compatible paper-order objects:

- `paperTotalMap`;
- `paperEndpointChartData`;
- `paperEndpointAdaptedEdgeMatrix`;
- `paperEndpointUnitriangularLeft`;
- `paperEndpointAdaptedTotalMatrix`.

It proves the endpoint-specific residual rank bridge
`lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub` and the
paper wrapper `lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub`.
Unlike the earlier ordinary-complement residual-rank theorem, this version uses
the endpoint chart data whose source complement is the total product kernel.

It also proves endpoint-compatible determinant-chart and block/elimination
wrappers:

- `identityCornerForm_paperEndpointAdaptedEdgeMatrix`;
- `identityCornerDetChart_paperEndpointAdaptedEdgeMatrix`;
- `paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart`;
- `identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix`;
- `unitriangular_paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart`;
- `paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero`;
- `productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim`.

The package theorem `paperEndpointBasepointCertificate_of_isCompl` bundles
these facts for a supplied total-kernel complement, and
`exists_paperEndpointBasepointCertificate` chooses such a complement in finite
dimension. This is the current bedrock A2 basepoint certificate. It remains a
fixed-chain, adapted-coordinate statement: it does not prove a fixed coordinate
family for variable nearby chains, exact rank-stratum openness, regular
coordinate-change transport, normal-crossing extraction, or any RLCT claim.

## 2026-06-19 A2 fixed-basepoint variable chart

Added generic block-corner and Schur-residual API to `ProductReduction.lean`:

- `lowerLeftBlock`;
- `fromBlocks_corners`;
- `schurResidualBlock`;
- `rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`.

The last theorem says that if a block matrix is in the selected determinant
chart, then its Schur residual has rank `rank M - r`. This is the correct
variable-edge rank statement; for a variable chain in fixed basepoint bases,
the raw lower-right block is not the residual unless the variable edge remains
in identity-corner form.

Added `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`. It fixes endpoint
bases from a base paper-order chain `B` and represents a variable chain `C` in
those same bases:

- `paperEndpointFixedBaseBasis`;
- `paperEndpointFixedBaseChainMapMatrix`;
- `paperEndpointFixedBaseEdgeMatrix`;
- `paperEndpointFixedBaseTotalMatrix`;
- `paperEndpointFixedBaseChainMapMatrix_succ_right`;
- `paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix`;
- basepoint equalities for `C = B`;
- `rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`;
- two-edge wrappers
  `paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0`.

The rank theorem keeps both hypotheses explicit:
`identityCornerDetChart (paperEndpointFixedBaseEdgeMatrix W B C U0 hU0 p)` and
`rank = rho`. No openness of exact rank strata, no automatic chart membership
for nearby chains, and no re-adaptation of bases to `C` is claimed.

Added the first variable-chart suffix step. In `ProductReduction.lean`,
`productReduction_chartLocal_suffixStep_fromBlocks_indexed` abstracts the
one-step induction move: from a reduced suffix

`Lprev * Ptail * Rprev = [Ctop 0; 0 Dprev]`

and a next edge factored as `E = Rprev * M`, if `Ctop` and the selected
top-left block of `M` have unit determinant, explicit left and right
block-triangular multipliers reduce `Ptail * E` to

`[Ctop * topLeft(M) 0; 0 Dprev * schurResidualBlock(M)]`.

In `FixedBasepointChart.lean`,
`paperEndpointFixedBase_chartLocal_suffixStep` instantiates this for fixed-base
variable-chain segment matrices. The wrapper
`rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range` identifies fixed-base
matrix rank with the variable edge's source linear-map range rank, and
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub`
states the Schur-residual rank as
`finrank range(reverseEdge W C p) - finrank U0` under the explicit determinant
chart hypothesis.

Added the all-layer explicit-chart induction:

- `productReduction_chartLocal_suffixChain_blockDiagonal_indexed` in
  `ProductReduction.lean`;
- `paperEndpointFixedBaseChainMapMatrix_proof_irrel` and
  `productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`
  in `FixedBasepointChart.lean`.

The abstract chain theorem mirrors the older identity-corner suffix-chain
induction, but its chart hypothesis is on the transformed edge

`[I Bprev; 0 I] * E p`

at every stage. It returns a left multiplier `L`, a right upper-unitriangular
source multiplier, a determinant-unit top block `Ctop`, and a residual block
`D` such that

`L * P i j * [I -B; 0 I] = [Ctop 0; 0 D]`.

The fixed-base wrapper applies this to variable paper-order chains expressed
in endpoint bases fixed from `B`. It still assumes all transformed-edge
determinant-chart hypotheses explicitly; it does not prove these from
neighborhood membership or exact rank.

## 2026-06-19 A2 fixed-base transformed determinant neighborhood

Extended `ChartTopology.lean` with matrix-space pullback lemmas for the
selected determinant chart:

- `leftMul_identityCornerDetChart_mem_nhds`;
- `fromBlocks_leftMul_identityCornerDetChart_mem_nhds`.

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For each fixed edge `p` and fixed accumulated upper block `Bprev`, the set of
matrices `M` such that `[I Bprev; 0 I] * M` lies in the selected determinant
chart is an ambient matrix-space neighborhood of the base fixed-base edge
matrix at `C = B`. The proof uses the endpoint unitriangular basepoint
certificate with parameter `-Bprev`, then pulls back the open determinant chart
along fixed left multiplication.

This closes the matrix-local determinant-neighborhood package needed by the
explicit-chart induction. It still does not prove a chain-neighborhood theorem:
there is no formal topology on the variable paper-order chain space here and
no continuity theorem for
`C ↦ paperEndpointFixedBaseEdgeMatrix W B C U0 hU0 p`. Exact rank remains an
explicit hypothesis, not an ambient-open condition.

## 2026-06-19 A2 single-edge topology pullback

Extended `ChartTopology.lean` with
`continuous_linearMap_toMatrix`: for fixed source and target bases, the map
from a continuous linear map to its coordinate matrix is continuous. The proof
is coordinatewise: evaluate the continuous linear map at a fixed source-basis
vector, then take a fixed coordinate in the target basis.

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For each fixed edge `p` and fixed accumulated upper block `Bprev`, the
transformed determinant-chart predicate pulls back to a neighborhood of the
base edge `reverseEdge W B p` in the `ContinuousLinearMap` topology.

This is the first honest topology pullback beyond ambient matrix space. It is
still one edge only. It does not define a topology on the whole dependent
paper-order chain, does not assemble finite intersections over all edges, does
not handle continuity of the induction-produced `Bprev`, and does not make
exact rank strata open.

## 2026-06-19 A2 fixed-Bprev edge-family topology assembly

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`.
For a prescribed family of accumulated upper blocks `Bprev p`, the set of
continuous reversed-edge families `Cedge` such that every fixed-basis coordinate
matrix satisfies

`identityCornerDetChart ([I Bprev p; 0 I] * M(Cedge p))`

is a neighborhood of the base edge family

`fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p)`

in the finite Pi/product topology. The proof is the finite intersection of the
single-edge neighborhoods, pulled back along the coordinate projections
`continuous_apply p`.

This closes the finite-intersection part of the topology bridge for fixed chart
data. It still does not control a neighborhood simultaneously for all possible
`Bprev`, does not prove continuity or local boundedness of the `Bprev` produced
by the suffix-chain induction, does not handle exact rank strata, and does not
prove Aoyagi Theorem 3.

## 2026-06-19 A2 variable-Bprev topology handoff

Extended `FixedBasepointChart.lean` with
`paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`.
For an arbitrary topological parameter space, if the continuous reversed-edge
family `Cedge x` and the accumulated-upper-block family `Bprev x` are
continuous at `x0`, and if every transformed determinant chart holds at `x0`,
then all those chart predicates hold on a neighborhood of `x0`.

This is the reusable topological handoff for variable chart data. It does not
construct the `Bprev` family produced by the suffix-chain induction.

Pen-and-paper recurrence check for that still-open construction:

- write `U_+(B) = [I B; 0 I]` and `U_-(B) = [I -B; 0 I]`;
- the induction hypothesis has
  `Lprev * Ptail * U_-(Bprev) = [Cprev 0; 0 Dprev]`;
- insert `E = U_-(Bprev) * (U_+(Bprev) * E)` and set
  `M = U_+(Bprev) * E`;
- the next right-elimination block is
  `(topLeftCorner M)⁻¹ * upperRightBlock M`.

The next Lean target is a deterministic recursive suffix-chain reduction using
this update under recursive determinant-chart hypotheses, followed by a
continuity theorem for that recursive data. Exact rank assumptions remain
separate.
