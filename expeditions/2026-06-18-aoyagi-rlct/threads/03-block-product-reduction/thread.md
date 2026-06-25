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

## 2026-06-20 A2 triangular endpoint multiplier wrapper

Returned to A2 to expose the triangular multipliers appearing explicitly in
Aoyagi Theorem 3.  Pen-and-paper reproduction saved at
`reproduction-a2-triangular-block-diagonal.md`; statement card saved at
`statement-card-a2-triangular-block-diagonal.md`.

Lean changes:

- `lowerUnitriangular_mul_fromBlocks_one_zero_indexed` proves
  `[I 0; F I] [I 0; G I] = [I 0; F + G I]`.
- `ChartLocalSuffixState.step_L_eq_lowerUnitriangular` and
  `ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular` prove the
  deterministic suffix state's accumulated left multiplier has shape
  `[I 0; F3 I]`.
- `ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal`
  and `productReduction_chartLocal_suffixChain_triangularBlockDiagonal_indexed`
  restate the abstract block-diagonal invariant with regular triangular
  multipliers.
- `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal`
  extracts fixed-endpoint Aoyagi-style multipliers from the existing
  source-facing certificate, with right multiplier `F2 = -S.B`.

This is still elementary finite block algebra and certificate repackaging.  It
does not prove chart coverage, exact-rank openness, Aoyagi Lemma 1, analytic
ideal transport, regular-coordinate RLCT additivity, normal crossings, or an
RLCT consequence.

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

## 2026-06-19 A2 deterministic suffix-state step

Extended `ProductReduction.lean` with a deterministic one-step state layer:

- `ChartLocalSuffixState`;
- `ChartLocalSuffixState.BlockDiagonal`;
- `ChartLocalSuffixState.transformedEdge`;
- `ChartLocalSuffixState.step`;
- `ChartLocalSuffixState.step_blockDiagonal`.

The state records the left multiplier `L`, right-elimination block `B`, top
block `Ctop`, and residual block `D`. The transformed edge is

`M = [I B; 0 I] * E p`,

and the deterministic step sets

`Bnext = (topLeftCorner M)⁻¹ * upperRightBlock M`.

The theorem `step_blockDiagonal` proves that this one-step update preserves the
block-diagonal invariant, assuming the previous suffix state satisfies the
invariant and the transformed edge lies in the determinant chart. This is the
algebraic one-step recurrence hidden inside the older existential suffix-chain
proof.

Still open: define the full recursive state from endpoint `j` down to `i`,
prove its block-diagonal invariant by iterating this step, and then prove
continuity of that recursive state on a chart neighborhood. Exact rank
assumptions remain separate.

## 2026-06-19 A2 deterministic recursive suffix state

Extended the deterministic suffix-state layer from one step to the full
recursive chart-local chain:

- `ChartLocalSuffixState.terminal`;
- `ChartLocalSuffixState.suffixState`;
- `ChartLocalSuffixState.suffixState_self`;
- `ChartLocalSuffixState.terminal_blockDiagonal`;
- `ChartLocalSuffixState.suffixState_castSucc`;
- `ChartLocalSuffixState.suffixState_blockDiagonal`.

The definition uses `Nat.decreasingInduction` on the lower endpoint `m ≤ j.val`
and keeps the dependent `Fin` casts local to `ProductReduction.lean`.
`suffixState E j i hij` is the deterministic state obtained by starting from
the terminal state at `j` and repeatedly applying
`ChartLocalSuffixState.step` down to `i`. The theorem
`suffixState_blockDiagonal` proves the full recursive block-diagonal invariant
under determinant-chart hypotheses for the actual transformed edges

`ChartLocalSuffixState.transformedEdge E p (suffixState E j p.succ hpj)`.

The older public existential theorem
`productReduction_chartLocal_suffixChain_blockDiagonal_indexed` is now a
wrapper extracting `L`, `B`, `Ctop`, and `D` from `suffixState`, rather than a
separate duplicate induction.

Still open: continuity of the recursively produced `suffixState` fields,
source-faithful neighborhoods where the recursive transformed-edge charts hold,
certificate transport, and the full source Theorem 3 statement. Exact rank
assumptions remain separate.

## 2026-06-19 A2 recursive-Bprev topology handoff

Extended the topology layer from supplied `Bprev` families to the actual
deterministic accumulated upper blocks produced by `suffixState`.

In `ChartTopology.lean`:

- `continuousAt_matrix_inv_of_isUnit_det`;
- `continuousAt_chartLocalSuffixState_step_B`;
- `continuousAt_chartLocalSuffixState_suffixState_B`.

The one-step continuity theorem proves that the updated block

`Bnext = (topLeftCorner M)⁻¹ * upperRightBlock M`

varies continuously with the edge and previous accumulated upper block, assuming
the transformed edge is in the determinant chart at the base point. The
recursive theorem iterates this along `suffixState`, proving continuity of the
`B` field at every lower endpoint under the recursive basepoint chart
hypotheses.

In `FixedBasepointChart.lean`,
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
feeds the recursively produced `Bprev` family into the existing
variable-`Bprev` handoff. The result is a fixed-base neighborhood on which all
recursive transformed-edge determinant charts persist, assuming those charts
hold at the base parameter.

Still open: exact-rank neighborhoods, certificate transport, the full
source-facing Theorem 3 statement, and continuity of `L`, `Ctop`, and `D` if a
later certificate needs those fields. Exact rank assumptions remain separate.

## 2026-06-19 A2 endpoint block-diagonal neighborhood

Extended `FixedBasepointChart.lean` from chart persistence to the endpoint
block form controlled by the same recursive suffix state.

New fixed-base reversed-edge coordinate API:

- `paperEndpointFixedBaseChainMapMatrixOfReverseEdges`;
- `paperEndpointFixedBaseEdgeMatrixOfReverseEdges`;
- `paperEndpointFixedBaseTotalMatrixOfReverseEdges`;
- composition and identity lemmas for these matrices.

The pointwise theorem
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal`
specializes `ChartLocalSuffixState.suffixState_blockDiagonal` to the endpoint
`0 ≤ Fin.last N`. It uses only the determinant charts for the actual recursive
states `suffixState E (Fin.last N) p.succ _`, not the stronger all-`Bprev`
hypothesis in the older public fixed-base wrapper.

The topology-level predicate
`paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal` names the
deterministic endpoint block form for a continuous reversed-edge family. The
neighborhood theorems
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds`
and
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds`
combine recursive chart persistence with the pointwise block theorem. At a base
family equal to `reverseEdge W B`, the recursive basepoint chart hypotheses are
proved by the unitriangular endpoint identity-corner theorem with `F = -Bprev`.

Still open: exact-rank neighborhoods, certificate transport, a source-facing
Theorem 3 statement, and any continuity of `L`, `Ctop`, or `D` if future
certificate data needs them.

## 2026-06-19 A2 adapted residual rank API

Added a minimal API for the residual blocks visited by the deterministic suffix
state. In `ProductReduction.lean`:

- `ChartLocalSuffixState.residualBlock`;
- `ChartLocalSuffixState.suffixState_D_self`;
- `ChartLocalSuffixState.suffixState_D_castSucc`.

The recurrence is intentionally adapted:

`S_next.D = S_tail.D * schurResidualBlock ([I S_tail.B; 0 I] * E p)`.

This names the lower-right block product in the block-diagonalized endpoint
matrix without claiming it is a raw product of the original edge residuals.

In `FixedBasepointChart.lean`, added the reversed-edge rank bridge
`rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range` and
pointwise transformed residual-rank wrappers, including
`rank_transformedEdge_fixedBaseReverseEdges_eq_range_sub`.
These results assume determinant-chart membership and exact edge rank at the
point. They do not assert exact-rank openness or any neighborhood of exact-rank
conditions.

Then added the first source-facing rank/certificate boundary theorem:

- `paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts`;
- `paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications`;
- `paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds`.

This theorem gives one neighborhood on which recursive determinant charts and
endpoint block form hold, and on which every residual rank conclusion is
available as an implication from an exact pointwise edge-rank hypothesis. It
does not place exact-rank hypotheses inside the neighborhood conclusion.

## 2026-06-19 A2 product-reduction boundary certificate

Landed `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`, imported by the
single-writer aggregator.

Main Lean artifacts:

- `PaperEndpointFixedBaseProductReductionCertificate`: a Prop-valued package
  for the fixed-base recursive determinant charts, endpoint block form, and
  residual-rank implications.
- `paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts`:
  a pointwise constructor from recursive determinant charts, reusing the
  deterministic endpoint block theorem and transformed residual-rank bridge.
- `paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds`: the
  neighborhood theorem for a continuous reversed-edge family based at
  `reverseEdge W B`.
- `PaperEndpointFixedBaseProductReductionLocalCertificate` and
  `paperEndpointFixedBaseProductReductionLocalCertificate_of_isCompl`: the
  fixed-base local package carrying both the basepoint certificate and the
  product-reduction certificate neighborhood.
- `PaperEndpointProductReductionLocalCertificate` and
  `exists_paperEndpointProductReductionLocalCertificate`: the existential local
  package choosing a total-kernel complement.

This checkpoint packages the current source-facing elementary/topological
boundary. It does not prove exact-rank openness, analytic ideal-germ transport,
regular-suspension/RLCT additivity, normal-crossing extraction, or the full
printed triangular product-reduction theorem from Aoyagi's source hypotheses.
The post-Theorem-3 RLCT transport remains a separate deferred problem. Xhigh
scouts `Herschel` and `Ohm` independently recommended this boundary shape,
with the same non-claims. Controller verified targeted build, full `DLNFibre`
build, `scripts/sorries`, `git diff --check`, and axiom spot checks for the
public theorems. Statement card:
`statement-card-a2-product-reduction-boundary-certificate.md`.

## 2026-06-21 A2 residual-product endpoint wrapper

Returned to the Theorem 3 endpoint form to name the lower-right residual
product explicitly. Aoyagi's induction updates the lower-right block by
multiplying the previous residual product by the Schur residual of the next
transformed layer. The Lean suffix state already had this recurrence for `D`;
this checkpoint gives the recurrence a named product.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`:

- `ChartLocalSuffixState.residualProduct`;
- `ChartLocalSuffixState.residualProduct_self`;
- `ChartLocalSuffixState.residualProduct_castSucc`;
- `ChartLocalSuffixState.suffixState_D_eq_residualProduct`;
- `ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct`;
- `productReduction_chartLocal_suffixChain_triangularBlockDiagonal_residualProduct_indexed`.

New endpoint wrapper in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct`.

The product is explicitly the deterministic product of transformed Schur
residuals visited by `suffixState`, not a raw product of original lower-right
edge blocks. The abstract suffix-chain wrapper still keeps the older
all-`Bprev` determinant-chart hypothesis; that is stronger than needed for the
proof but explicit in the statement.

Still open: weakening the abstract chart hypothesis, chart coverage from
source rank hypotheses, exact-rank openness, Aoyagi Lemma 1, analytic
ideal-germ transport, regular-coordinate RLCT bookkeeping, normal-crossing
extraction, and every RLCT consequence.

Artifacts:
`reproduction-a2-residual-product.md`,
`statement-card-a2-residual-product.md`, and
`review-a2-residual-product.md`.

## 2026-06-22 A2 rank-stratum boundary

Returned to the exact-rank side of Aoyagi Theorem 3.  The previous fixed-base
certificate kept residual-rank conclusions as implications from exact layer
ranks.  This checkpoint packages the intended restriction explicitly rather
than treating exact-rank strata as open.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `paperEndpointFixedBaseEdgeRankStratum`;
- `paperEndpointFixedBaseSourceRankStratum`;
- `paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks`;
- `PaperEndpointFixedBaseProductReductionRankStratumCertificate`;
- `PaperEndpointFixedBaseProductReductionCertificate.residualRanks_of_edgeRankStratum`;
- `PaperEndpointFixedBaseProductReductionCertificate.rankStratumCertificate`;
- `PaperEndpointFixedBaseProductReductionCertificate.residualBlock_rank_eq_sourceRankSubProductRank`;
- `paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin`;
- `paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin_source`;
- `PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate`;
- `PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate.mem_nhdsWithin_source`;
- `PaperEndpointProductReductionRankStratumLocalCertificate`;
- `exists_paperEndpointProductReductionRankStratumLocalCertificate`.

The source-shaped stratum records base product rank `r`, exact nearby edge ranks
`rEdge`, and the inequalities `r <= rEdge p`.  On that stratum the basepoint
certificate rewrites `finrank U0` to `r`, giving the residual-rank formula
`rank(residualBlock p) = rEdge p - r`.

This still does not prove exact-rank openness, chart coverage from only source
rank hypotheses, Aoyagi Lemma 1, analytic ideal-germ transport,
regular-coordinate RLCT bookkeeping, normal crossings, or any RLCT consequence.

Artifacts:
`reproduction-a2-rank-stratum-boundary.md` and
`statement-card-a2-rank-stratum-boundary.md`.

## 2026-06-23 A2 source-rank-stratum endpoint wrapper

Combined the two latest fixed-base A2 boundary pieces: the endpoint triangular
block form with deterministic transformed residual product, and the source
rank-stratum residual-rank formula.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `PaperEndpointFixedBaseTriangularResidualProductSourceRanks`;
- `PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`.

The theorem takes a fixed-base basepoint certificate, a fixed-base
product-reduction certificate, and membership in
`paperEndpointFixedBaseSourceRankStratum`.  It returns a bundled endpoint
conclusion: regular triangular endpoint multipliers expose
`ChartLocalSuffixState.residualProduct`, and every visited residual block has
rank `rEdge p - r`.

Scope caveats: "source rank stratum" is repository terminology for Aoyagi's
fixed layer-rank restrictions.  The stratum supplies rank data for the
subtraction formula; the determinant-chart hypotheses required by Lemma 2
remain in the certificate.  This is not exact-rank openness, source-stratum
nonemptiness, full Theorem 3, Lemma 1 normalization, analytic ideal transport,
regular-coordinate RLCT bookkeeping, normal crossings, pole order, or RLCT.

Artifacts:
`reproduction-a2-source-rank-stratum-theorem3-boundary.md`,
`statement-card-a2-source-rank-stratum-theorem3-boundary.md`, and
`review-a2-source-rank-stratum-theorem3-boundary.md`.

## 2026-06-23 A2 local source-rank endpoint package

Lifted the fixed-base/source-rank endpoint wrapper into the local
product-reduction boundary.  The new theorem
`paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`
uses the existing ordinary neighborhood of fixed-base product-reduction
certificates, intersects it with `paperEndpointFixedBaseSourceRankStratum`, and
applies the pointwise source-rank endpoint wrapper.  Thus the conclusion is
relative to the source rank stratum; it does not assert exact-rank openness.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `paperEndpointFixedBaseSourceRankStratum_selfBase_mem`;
- `paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`;
- `PaperEndpointTriangularSourceRanksLocalCertificate`;
- `exists_paperEndpointTriangularSourceRanksLocalCertificate`.

This removes a downstream composition step for A2 consumers: after choosing a
total-kernel complement, the local package directly yields the triangular
endpoint residual-product/source-rank shape relative to the source rank
stratum.  The basepoint membership wrapper proves membership in that stratum
only from supplied product/layer rank equalities and inequalities.  The
endpoint lower-right block remains
`ChartLocalSuffixState.residualProduct` for transformed Schur residuals, not a
raw product of original edge lower-right blocks.

Scope caveats: this is not exact-rank openness, source-stratum nonemptiness,
full Theorem 3, Aoyagi Lemma 1 normalization, analytic ideal transport,
regular-coordinate RLCT additivity, normal crossings, pole order, or RLCT.

Artifacts:
`reproduction-a2-local-source-rank-endpoint-package.md` and
`statement-card-a2-local-source-rank-endpoint-package.md`.
Review:
`review-a2-local-source-rank-endpoint-package.md`.

## 2026-06-23 A2 block product-difference algebra

Formalized the p. 13 pointwise block product-difference calculation downstream
of the triangular endpoint form.  The new theorem
`triangularBlockProductDifference_fromBlocks_indexed` assumes

```text
[I 0; F3 I] * T * [I F2; 0 I] = [Ctop 0; 0 D]
```

and proves

```text
[I 0; F3 I] * (T - [I 0; 0 0]) * [I F2; 0 I]
  = [Ctop - I, -F2; -F3, D - F3 * F2].
```

This is pure block algebra over a commutative ring.  The endpoint wrapper was
intentionally not added: it would only destruct the existing triangular
endpoint certificate, and the source-rank field is irrelevant until a concrete
downstream ideal/certificate theorem needs the exact `T - T0` form.

Scope caveats: this is not source production of the triangular endpoint form,
full Theorem 3, Aoyagi Lemma 1, analytic generator transport, regular
suspension, normal crossings, pole order, or RLCT.

Artifacts:
`reproduction-a2-block-product-difference-algebra.md` and
`statement-card-a2-block-product-difference-algebra.md`.
Independent pen-and-paper check: xhigh `Lorentz`.
Fidelity/scope review: xhigh `Fermat`, accepted in
`review-a2-block-product-difference-algebra.md`.

## 2026-06-23 A2 product-difference entry-ideal boundary

Returned to the p. 13 product-difference block matrix because it now has a
concrete downstream consumer: the scalar matrix-entry ideal handoff at the
fixed-base/source-rank boundary.

New generic Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`:

- `matrixEntryIdeal_neg_eq`;
- `matrixEntryIdeal_fromBlocks_eq_fourMatrixEntryIdeal`;
- `matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal`.

New boundary Lean artifacts in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`:

- `matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal`;
- `PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks`;
- `PaperEndpointFixedBaseTriangularResidualProductSourceRanks.exists_productDifferenceEntryIdeal`;
- `PaperEndpointFixedBaseTriangularResidualProductSourceRanks.toProductDifferenceEntryIdealSourceRanks`;
- `paperEndpointFixedBaseProductDifferenceEntryIdeal_selfBase_mem_nhdsWithin_source`;
- `PaperEndpointProductDifferenceEntryIdealLocalCertificate`;
- `exists_paperEndpointProductDifferenceEntryIdealLocalCertificate`.

The wrapper takes the existing triangular residual-product/source-rank package,
uses determinant-unit left/right entry-ideal transport, rewrites the signed
four-block matrix, and removes the `F3 * F2` correction modulo the entries of
`F2` and `F3`.  The lower-right block remains
`ChartLocalSuffixState.residualProduct`; the conclusion is a scalar
matrix-entry-ideal equality for endpoint matrices, relative to the source rank
stratum.

Scope caveats: this is not analytic germ-ideal transport, exact-rank openness,
source-stratum nonemptiness, full Theorem 3, Aoyagi Lemma 1 normalization,
regular-suspension RLCT additivity, normal-crossing production, pole order, or
RLCT.

Artifacts:
`reproduction-a2-product-difference-entry-ideal-boundary.md` and
`statement-card-a2-product-difference-entry-ideal-boundary.md`.
Review:
`review-a2-product-difference-entry-ideal-boundary.md`.

## 2026-06-23 A2 regular-variable count and finite shift

Returned to the regular block families isolated after Aoyagi Theorem 3:
`C1 - Er`, `F2`, and `F3`.  The pen-and-paper calculation records their scalar
entry count as

```text
r^2 + r(H^(L+1)-r) + (H^(1)-r)r
  = -r^2 + r(H^(1)+H^(L+1)).
```

Under endpoint rank-width bounds, half of this count is the regular term
already named in the Theorem 2 formula layer.

New Lean artifacts:

- `aoyagiTheorem2RegularVariableCount`;
- `aoyagiTheorem2RegularTerm_eq_half_regularVariableCount`;
- `AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiNormalCrossingExponentData.exponentOrder_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_jacobianPriorLossShift_regularVariableCount`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift`.

The first two names live in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`; the
finite-shift bridge lives in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`.

Scope caveats: this is finite count and exponent-array arithmetic only.  It
does not construct a regular-suspension chart, transport analytic ideals,
invoke Aoyagi Lemma 1, prove regular-coordinate RLCT additivity, produce a
normal-crossing certificate, prove pole order, or prove an RLCT theorem.

Artifacts:
`reproduction-a2-regular-variable-count.md` and
`statement-card-a2-regular-variable-count.md`.
Review:
`review-a2-regular-variable-count.md`.

## 2026-06-24 A2 transformed-edge rank-stratum bridge

Returned to the source-rank boundary after the product-difference entry-ideal
package.  The recursive Schur-residual product applies Lemma 2 to transformed
edges of the form

```text
[I Bprev; 0 I] * E_p.
```

Because `[I Bprev; 0 I]` is determinant-unit block-unitriangular, the
transformed edge has the same rank as the original fixed-base source edge.

New Lean artifact in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`:

- `paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum`.

The theorem identifies the transformed-edge rank predicate used by
`ChartLocalSuffixState.transformedEdge` and `suffixState` with the already
named `paperEndpointFixedBaseEdgeRankStratum`.  This removes an ambiguity at
the A2 source-rank boundary: the recursion's transformed-edge exact-rank
condition is not an extra rank hypothesis beyond the fixed-base edge-rank
component of Aoyagi's source-shaped rank stratum.

Scope caveats: no exact-rank openness, source-stratum nonemptiness, chart
production, analytic ideal transport, regular-suspension/RLCT additivity,
normal-crossing production, pole order, or RLCT.

Artifacts:
`reproduction-a2-transformed-edge-rank-stratum-bridge.md` and
`statement-card-a2-transformed-edge-rank-stratum-bridge.md`.
Review:
`review-a2-transformed-edge-rank-stratum-bridge.md`.

## 2026-06-24 A2 regular-variable source-rank shift

Connected the A2 source-rank boundary to the regular-variable finite shift.
The existing regular-variable shift required endpoint rank-width assumptions
`r <= H 1` and `r <= H (N+1)`.  The new slice derives those assumptions from
source-rank-stratum membership and the explicit dimension convention
`H(k+1)=finrank(W k)`.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`:

- `paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds`;
- `AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum`;
- `AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_sourceRankStratum`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_sourceRankStratum`.

Scope caveats: this is endpoint rank-width provenance and finite
certificate arithmetic only.  It does not prove exact-rank openness, regular
suspension chart construction, analytic ideal transport, Aoyagi Lemma 1,
normal-crossing chart production, pole order, RLCT, or a connection from the
supplied reduced certificate to the A2 geometry.

Artifacts:
`reproduction-a2-regular-variable-source-rank-shift.md` and
`statement-card-a2-regular-variable-source-rank-shift.md`.
Review:
`review-a2-regular-variable-source-rank-shift.md`.

## 2026-06-24 A2 regular-variable rank-width shift

The regular-variable finite shift has been weakened from A2 source-rank
stratum data to the source-range rank-width hypothesis already used by
Definition 3:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

The finite shift still needs only the endpoint projections `r <= H 1` and
`r <= H (L+1)`.  The final Definition 3 handoff, however, keeps the full
source-range rank-width hypothesis because selected-width side facts use
rank-width at every selected cutpoint.

New Lean artifacts in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`:

- `sourceRangeRankWidth_regularVariableEndpointBounds`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_rankWidth`;
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_rankWidth`.

The older source-rank finite constructors remain as leaf wrappers but now
delegate through the rank-width constructors.

Scope caveats: finite exponent-array arithmetic and rank-width provenance
only.  This does not prove regular-suspension chart construction, analytic
ideal transport, Aoyagi Lemma 1, active-ratio or chart-count facts,
normal-crossing production, pole order, or RLCT.

Artifacts:
`reproduction-a2-regular-variable-rank-width-shift.md` and
`statement-card-a2-regular-variable-rank-width-shift.md`.
Review:
`review-a2-regular-variable-rank-width-shift.md`.

## 2026-06-24 A2 supplied regular-suspension interface

The p. 13 regular-variable step has been pinned to a conservative boundary:
Aoyagi supplies the block algebra and the count, while a genuine full
regular-suspension normal-crossing chart remains supplied.  The intended Lean
socket carries a reduced chart certificate and a full chart certificate
possibly over different parameter/coefficient types, named abstract
obligations for source/ideal/coverage/Jacobian compatibility, and the finite
exponent equality

```text
Cfull.exponentData =
  Cred.exponentData.jacobianPriorLossShift regularCount.
```

The extraction hypothesis is required for `Cfull`, not for `Cred` with an
after-the-fact `c/2` addition.  Finite consequences then build the existing
`AoyagiTheorem2SuppliedChartFinalBoundary Cfull ...` from reduced
minimum-plus-regular-term and order equalities, without routing through a
boundary for the synthetic shifted certificate.

Artifacts:
`reproduction-a2-regular-suspension-interface.md` and
`statement-card-a2-regular-suspension-interface.md`.
Review:
`review-a2-regular-suspension-interface.md`.

## 2026-06-24 Lean chart-local suffix-state field continuity

Reproduction:
`reproduction-a2-chart-local-suffix-state-field-continuity.md`.
Statement card:
`statement-card-a2-chart-local-suffix-state-field-continuity.md`.
Review:
`review-a2-chart-local-suffix-state-field-continuity.md`.

Lean now extends the chart-local topology API in `ChartTopology.lean`:

```text
continuousAt_chartLocalSuffixState_step_fields
continuousAt_chartLocalSuffixState_suffixState_fields
```

The one-step theorem proves fieldwise continuity of `L`, `B`, `Ctop`, and
`D`, and carries the next `IsUnit Ctop.det` invariant.  The suffix theorem
descends through the deterministic recursion under the same recursive
determinant-chart hypotheses as the existing `B` theorem, returning the
basepoint `Ctop.det` unit and fieldwise continuity for every `i <= j`.

This is only continuity of deterministic matrix fields at the basepoint.  It
does not prove analytic regularity, exact-rank openness, source-rank-stratum
openness, local source-neighborhood construction, regular suspension, ideal
transport, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 fixed-base suffix-state field continuity handoff

Reproduction:
`reproduction-a2-fixed-base-suffix-state-field-continuity.md`.
Statement card:
`statement-card-a2-fixed-base-suffix-state-field-continuity.md`.
Review:
`review-a2-fixed-base-suffix-state-field-continuity.md`.

Lean now applies the generic suffix-state field-continuity theorem to the
endpoint-coordinate matrix family fixed from the base paper chain `B`:

```text
paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt
```

The theorem defines the fixed-base coordinate edge family from a continuous
reversed-edge family `Cedge`, proves this matrix family is continuous by
fixed-basis coordinate continuity, rewrites the recursive determinant-chart
hypotheses, and returns `IsUnit Ctop.det` plus continuity of `L`, `B`,
`Ctop`, and `D` for every suffix state ending at `Fin.last N`.

Boundary: fixed-base continuity handoff only.  This does not prove analytic
regularity, exact-rank/source-rank openness, chart coverage, regular
suspension, ideal transport, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 canonical product-difference coefficient fields

Reproduction:
`reproduction-a2-canonical-product-difference-coefficient-fields.md`.
Statement card:
`statement-card-a2-canonical-product-difference-coefficient-fields.md`.
Review:
`review-a2-canonical-product-difference-coefficient-fields.md`.

Lean now exposes the p. 13 product-difference entry-ideal equality with the
deterministic suffix-state fields instead of existential triangular witnesses:

```text
ChartLocalSuffixState.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal
PaperEndpointFixedBaseProductReductionCertificate.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal_canonicalFields
```

The generic theorem starts from a suffix-state block-diagonal invariant

```text
S.L * P(i,j) * [I -S.B; 0 I] = [S.Ctop 0; 0 S.D]
```

and proves the scalar matrix-entry ideal of
`P(i,j) - [I 0; 0 0]` is the four-block ideal generated by
`S.Ctop - I`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`.  The proof uses
`suffixState_L_eq_lowerUnitriangular` to rewrite `S.L` as
`[I 0; lowerLeftBlock S.L I]`, then delegates to the existing
`matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal`.

The fixed-base theorem applies this pointwise to the endpoint matrix family
from `PaperEndpointFixedBaseProductReductionCertificate`, rewriting the
endpoint total matrix to the chain-map family with
`paperEndpointFixedBaseTotalMatrixOfReverseEdges_eq_chainMapMatrix`.

Boundary: rank-free algebraic entry-ideal handoff only.  This does not prove
source-rank neighborhood construction, exact-rank/source-rank openness,
analytic regularity, analytic germ-ideal transport, chart coverage, normal
crossings, pole order, or RLCT.

## 2026-06-24 A2 canonical product-difference coefficient-field continuity

Reproduction:
`reproduction-a2-canonical-product-difference-field-continuity.md`.
Statement card:
`statement-card-a2-canonical-product-difference-field-continuity.md`.
Review:
`review-a2-canonical-product-difference-field-continuity.md`.

Lean now proves that the deterministic fields used in the canonical
product-difference entry-ideal boundary are continuous fixed-base local
functions, and that they are centered at the self-base chain:

```text
paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt
paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt
paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt
```

The explicit-chart theorem assumes a continuous reversed-edge family together
with the recursive determinant-chart hypotheses at `x0`; the self-base theorem
derives those hypotheses from `Cedge x0 = reverseEdge W B`.  The returned
fields are exactly the canonical p. 13 fields

```text
S.Ctop - 1,  -S.B,  lowerLeftBlock S.L,  S.D.
```

together with `IsUnit ((S x0).Ctop.det)`.  The centered self-base theorem also
proves the four basepoint equalities

```text
(S x0).Ctop - 1 = 0,
-(S x0).B = 0,
lowerLeftBlock (S x0).L = 0,
(S x0).D = 0.
```

Boundary: continuity and basepoint centering only.  This does not prove
analytic regularity, exact-rank/source-rank openness, chart coverage, analytic
ideal or germ transport, a regular-suspension certificate, normal crossings,
pole order, or RLCT.

## 2026-06-24 A2 canonical product-difference local certificate

Reproduction:
`reproduction-a2-canonical-product-difference-local-certificate.md`.
Statement card:
`statement-card-a2-canonical-product-difference-local-certificate.md`.
Review:
`review-a2-canonical-product-difference-local-certificate.md`.

Lean now packages the centered continuous canonical fields with the local
source-rank product-difference boundary:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
PaperEndpointFixedBaseProductReductionCertificate.toCanonicalProductDifferenceSourceRanks
paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl
PaperEndpointCanonicalProductDifferenceLocalCertificate
exists_paperEndpointCanonicalProductDifferenceLocalCertificate
```

The pointwise source-rank predicate uses the deterministic fields

```text
S.Ctop - 1,  -S.B,  lowerLeftBlock S.L,  S.D
```

in the `fourMatrixEntryIdeal` equality and carries the residual-rank formulas
`rank residualBlock_p = rEdge p - r`.  The fixed-base local certificate also
stores the self-base centered-continuity theorem for those same four fields.
The local conclusion is relative to `paperEndpointFixedBaseSourceRankStratum`
via `nhdsWithin`.

Boundary: canonical local packaging only.  This does not assert exact-rank or
source-rank openness, analytic regularity, chart coverage, analytic ideal or
germ transport, a regular-suspension certificate, normal crossings, pole
order, or RLCT.

## 2026-06-24 A2 canonical product-difference local source certificate

Reproduction:
`reproduction-a2-canonical-product-difference-local-source-certificate.md`.
Statement card:
`statement-card-a2-canonical-product-difference-local-source-certificate.md`.
Review:
`review-a2-canonical-product-difference-local-source-certificate.md`.

Target: pair the canonical product-difference local certificate with basepoint
membership in Aoyagi's source-shaped rank stratum, under supplied source rank
data for the base product and base edges.  This removes the vacuity caveat for
the base chain without claiming exact-rank/source-rank openness.

Lean now has:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_source_neighborhood
PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
```

Boundary: nonvacuity/source-rank packaging only.  The local conclusion remains
`nhdsWithin` the source-shaped rank stratum, and the explicit neighborhood
projection keeps source-rank membership as a guard.  This does not prove the
stratum is open, construct regular-suspension charts, transport analytic
ideals, prove normal crossings, identify pole order, or extract RLCT.

## 2026-06-24 A2 canonical product-difference regular-chart source

Reproduction:
`reproduction-a2-canonical-product-difference-regular-chart-source.md`.
Statement card:
`statement-card-a2-canonical-product-difference-regular-chart-source.md`.
Review:
`review-a2-canonical-product-difference-regular-chart-source.md`.

Target: make the supplied regular-suspension boundary consume the A2 local
source certificate directly for its `regular_chart_source` field, without
claiming the analytic regular-suspension construction.

Lean now has:

```text
AoyagiCanonicalProductDifferenceRegularChartSource
AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularChartSource
```

The source predicate is definitionally the existing
`PaperEndpointCanonicalProductDifferenceLocalSourceCertificate W B x0 Cedge r
rEdge`, viewed as a predicate on `Cred`, `Cfull`, and `regularCount`.  The
constructor fills only `regular_chart_source`; ideal transport, coverage,
Jacobian compatibility, and the exponent-data shift equality remain supplied.

Boundary: A2 source-predicate handoff only.  This does not scalarize the
regular variables, prove the regular count, construct `Cfull`, prove analytic
ideal/germ transport, prove chart coverage, prove Jacobian compatibility,
produce normal crossings, identify pole order, or extract RLCT.

Next stronger A2 target from xhigh scout: scalarize the p. 13 regular blocks
`S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`, prove their centered
continuity as finite scalar coordinates, and prove the coordinate count is
`aoyagiTheorem2RegularVariableCount`.

## 2026-06-24 A2 regular-suspension coordinate index

Reproduction:
`reproduction-a2-regular-suspension-coordinate-index.md`.
Statement card:
`statement-card-a2-regular-suspension-coordinate-index.md`.
Review:
`review-a2-regular-suspension-coordinate-index.md`.

Lean now scalarizes the p. 13 regular block families:

```text
AoyagiRegularBlockCoordinateIndex
AoyagiRegularBlockCoordinateIndex.card
AoyagiRegularBlockCoordinateIndex.value
AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount
paperEndpointEndpointComplementIndex_card_eq_layerSubRank
paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount
```

The coordinate index is the finite disjoint union of entries of
`Ctop - 1`, `F2`, and `F3`.  The local-certificate projection applies the
existing centered continuity of `S.Ctop - 1`, `-S.B`, and
`lowerLeftBlock S.L` to every scalar coordinate.  The residual field `S.D` is
excluded.  The endpoint-compatible count theorem now derives the source and
target residual cardinalities from the fixed-base endpoint complement
construction, base product rank, and dimension convention.

Boundary: finite coordinate bookkeeping and componentwise continuity only.
This does not construct analytic regular coordinates, construct `Cfull`, prove
the four-block ideal split, prove ideal transport, prove chart coverage, prove
Jacobian compatibility, produce normal crossings, identify pole order, or
extract RLCT.

## 2026-06-24 A2 regular/residual ideal split

Reproduction:
`reproduction-a2-regular-residual-ideal-split.md`.
Statement card:
`statement-card-a2-regular-residual-ideal-split.md`.
Review:
`review-a2-regular-residual-ideal-split.md`.

Lean now names the regular block-entry ideal and exposes the algebraic split
from the four-block product-difference ideal:

```text
regularBlockEntryIdeal
fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
matrixEntryIdeal_triangularBlockProductDifference_eq_regular_sup_residual
ChartLocalSuffixState.productDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
```

The canonical fixed-base theorem rewrites the product-difference entry ideal as

```text
regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
  matrixEntryIdeal S.D.
```

Boundary: scalar ideal regrouping only.  `S.D` remains residual, not part of
the regular-coordinate index.  This does not prove analytic germ-ideal
transport, regular-suspension chart construction, coverage, Jacobian
compatibility, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 regular-coordinate ideal bridge

Reproduction:
`reproduction-a2-regular-coordinate-ideal-bridge.md`.
Statement card:
`statement-card-a2-regular-coordinate-ideal-bridge.md`.
Review:
`review-a2-regular-coordinate-ideal-bridge.md`.

Lean now connects the scalar coordinate index to the regular block-entry ideal:

```text
AoyagiRegularBlockCoordinateIndex.entryIdeal
AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal
```

The theorem proves that the ideal generated by the scalar values of
`AoyagiRegularBlockCoordinateIndex.value X F2 F3` is exactly
`regularBlockEntryIdeal X F2 F3`.  The fixed-base canonical theorem composes
this with the regular/residual split, rewriting the product-difference entry
ideal as the scalar regular-coordinate ideal joined with `matrixEntryIdeal S.D`.

Boundary: algebraic ideal bookkeeping only.  The scalar-coordinate ideal theorem
is valid without finite index assumptions; the finite Aoyagi use is supplied by
the count theorems.  The residual block `D` is not part of the scalar
regular-coordinate index.  This does not construct analytic regular
coordinates, transport analytic germ ideals, prove chart coverage or Jacobian
compatibility, produce normal crossings, identify pole order, or extract RLCT.

## 2026-06-24 A2 local source regular-coordinate ideal split

Reproduction:
`reproduction-a2-local-source-regular-coordinate-ideal-split.md`.
Statement card:
`statement-card-a2-local-source-regular-coordinate-ideal-split.md`.
Review:
`review-a2-local-source-regular-coordinate-ideal-split.md`.

Lean now upgrades the fixed-base local source certificate to a neighborhood
statement using scalar regular coordinates:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_regularCoordinateIdeal_source_neighborhood
```

For points in the returned neighborhood that also lie in the source-shaped rank
stratum, the product-difference entry ideal is the scalar regular-coordinate
ideal generated by `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`, joined with
the residual ideal `matrixEntryIdeal S.D`.

Boundary: local source-side algebraic bookkeeping only.  The source-stratum
guard remains explicit; this does not prove source-rank openness, analytic
germ-ideal transport, regular-suspension chart construction, coverage,
Jacobian compatibility, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 regular-coordinate ideal source predicate

Reproduction:
`reproduction-a2-regular-coordinate-ideal-source-predicate.md`.
Statement card:
`statement-card-a2-regular-coordinate-ideal-source-predicate.md`.
Review:
`review-a2-regular-coordinate-ideal-source-predicate.md`.

Lean now names the source predicate needed by a later supplied
regular-suspension chart:

```text
PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateIdealSourceNeighborhood
AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate
AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularCoordinateIdealSource
```

The fixed-base predicate records a neighborhood where, on the source-shaped
rank stratum, the canonical product-difference ideal is the scalar
regular-coordinate ideal joined with the residual `S.D` ideal.  The
regular-suspension source predicate existentially chooses the fixed endpoint
base certificate and carries both the local source certificate and the named
regular-coordinate/residual ideal neighborhood.

The boundary constructor fills only `regular_chart_source`.  Ideal transport,
coverage, Jacobian compatibility, and the exponent-shift equality are still
supplied.  This keeps the stronger algebraic source information available
without importing the coordinate file back into `RegularSuspensionInterface`.

Boundary: source-side algebraic source predicate only.  No source-rank
openness, analytic germ-ideal transport, construction of `Cfull`, coverage,
Jacobian compatibility, exponent shift, normal crossings, pole order, or RLCT
is proved.

## 2026-06-24 A2 regular-coordinate ideal source existence

Reproduction:
`reproduction-a2-regular-coordinate-ideal-source-existence.md`.
Statement card:
`statement-card-a2-regular-coordinate-ideal-source-existence.md`.
Review:
`review-a2-regular-coordinate-ideal-source-existence.md`.

Lean now gives the raw-hypothesis constructor for the stronger source
predicate:

```text
exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource
```

It takes a continuous reversed-edge family based at `B`, the supplied base
product rank, supplied base edge ranks, and the supplied rank bounds
`r <= rEdge p`.  It first uses
`exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate` to
choose the endpoint complement and local source certificate, then applies
`aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate`.

Boundary: composition of existing source-side algebra only.  No source-rank
openness, analytic germ-ideal transport, construction of `Cfull`, ideal
transport, coverage, Jacobian compatibility, exponent shift, normal crossings,
pole order, or RLCT is proved.

## 2026-06-24 A2 base product rank bounded by edge ranks

Reproduction:
`reproduction-a2-base-product-rank-le-edge-rank.md`.
Statement card:
`statement-card-a2-base-product-rank-le-edge-rank.md`.
Review:
`review-a2-base-product-rank-le-edge-rank.md`.

Lean now proves the elementary base-chain rank inequality:

```text
paperTotalMap_finrank_range_le_reverseEdge_finrank_range
```

For each edge `p`, the full reversed product factors through
`reverseEdge W B p`, so its range finrank is bounded by the edge range
finrank.  The basepoint source-rank-stratum API now has a no-`hle` constructor:

```text
paperEndpointFixedBaseSourceRankStratum_selfBase_mem_of_rank_eq
```

and the source-certificate path has matching no-`hle` wrappers:

```text
paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq
exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq
```

Boundary: basepoint rank packaging only.  This removes the redundant base
inequality input from the new wrappers, but it does not prove exact-rank or
source-rank openness, analytic germ-ideal transport, `Cfull`, ideal transport,
coverage, Jacobian compatibility, exponent shift, normal crossings, pole
order, or RLCT.

## 2026-06-24 A2 regular-coordinate source data

Reproduction:
`reproduction-a2-regular-coordinate-source-data.md`.
Statement card:
`statement-card-a2-regular-coordinate-source-data.md`.
Review:
`review-a2-regular-coordinate-source-data.md`.

Lean now packages the source-produced p. 13 regular-coordinate data in
`RegularSuspensionCoordinates.lean`:

```text
PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateSourceData
exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq
```

The rank-equality theorem starts from a continuous reversed-edge family based
at `B`, base product rank `r`, base edge ranks `rEdge`, and the dimension
convention `H(k+1)=finrank(W k)`.  It chooses a total-kernel complement and
returns a fixed-base package containing the local source certificate, the
source-stratum guarded regular/residual ideal split, centered continuous
scalar coordinates for `S.Ctop - 1`, `-S.B`, and `lowerLeftBlock S.L`, and the
cardinality equality with `aoyagiTheorem2RegularVariableCount N H r`.

Boundary: source-side regular-coordinate data only.  No exact-rank or
source-rank openness, analytic germ-ideal transport, regular-suspension chart
construction, coverage, Jacobian compatibility, exponent shift, normal
crossings, pole order, or RLCT is proved.

## 2026-06-24 A2 regular-suspension normal-crossing boundary audit

Audit:
`audit-a2-regular-suspension-normal-crossing-boundary.md`.

Controller inspection and xhigh scout `Locke the 3rd` agree that the current
APIs cannot construct a full regular-suspension normal-crossing certificate
`Cfull` from `PaperEndpointFixedBaseRegularCoordinateSourceData`.

The reason is precise.  The source-data package proves centered continuous
scalar regular-coordinate functions and a source-stratum guarded ideal split,
but it does not prove those scalar functions form analytic coordinates.  The
current `AoyagiNormalCrossingChartCertificate` records finite monomial chart
data and supports certificate algebra such as `jacobianPriorLossShift`; it
does not encode analytic chart coverage, coordinate invertibility, generator
transport, or regular-coordinate additivity.

Do not add a theorem

```text
PaperEndpointFixedBaseRegularCoordinateSourceData -> exists Cfull, ...
```

and do not introduce source-anchored analytic obligation predicates whose
fields are empty, `True`, or merely renamed arbitrary predicates.  A Lean
boundary for regular suspension is worthwhile only after a pen-and-paper
reproduction identifies concrete full/reduced generator families, analytic
regular coordinates, coverage, Jacobian/prior shift, units, and extraction for
the actual full certificate.

## 2026-06-24 A2 residual-coordinate source data

Reproduction:
`reproduction-a2-residual-coordinate-source-data.md`.
Statement card:
`statement-card-a2-residual-coordinate-source-data.md`.
Review:
`review-a2-residual-coordinate-source-data.md`.

Lean now also scalarizes the residual p. 13 block in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiResidualBlockCoordinateIndex
AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal
AoyagiResidualBlockCoordinateIndex.value_centered_continuousAt
paperEndpointResidualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.residualBlockCoordinateIndex_card_eq_endpointResidualEntryCount
PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt
```

The existing `PaperEndpointFixedBaseRegularCoordinateSourceData` structure now
also carries centered continuity for scalar entries of `S.D` and the residual
endpoint entry count `(H 1-r)*(H(N+1)-r)`.  This makes the reduced block side
of the regular/residual split explicit while keeping it separate from the
regular-coordinate index and the regular-variable finite shift.

Boundary: source-side residual-coordinate bookkeeping only.  No analytic
residual chart, normal-crossing certificate, germ-ideal transport, coverage,
Jacobian compatibility, exponent shift, regular-coordinate additivity, pole
order, or RLCT is proved.

Xhigh review by `Curie the 3rd` passed after repairing prose that called the
row/left and column/right residual endpoint indices "source" and "target".
The formulas were correct before the wording repair.

## 2026-06-24 A2 product-difference coordinate source data

Reproduction:
`reproduction-a2-product-difference-coordinate-source-data.md`.
Statement card:
`statement-card-a2-product-difference-coordinate-source-data.md`.
Review:
`review-a2-product-difference-coordinate-source-data.md`.

Lean now scalarizes the cleaned p. 13 product-difference ideal-level family in
`RegularSuspensionCoordinates.lean`:

```text
AoyagiProductDifferenceCoordinateIndex
AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal
AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal
AoyagiProductDifferenceCoordinateIndex.value_centered_continuousAt
AoyagiProductDifferenceCoordinateIndex.card_eq_endpointProductEntryCount
paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal
PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_productDifferenceCoordinateIdeal_source_neighborhood
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount
PaperEndpointFixedBaseProductDifferenceScalarCoordinatesCenteredContinuousAt
```

The index is the sum of the regular scalar-coordinate index and residual
scalar-coordinate index, so its scalar ideal is the cleaned four-block ideal
generated by entries of `S.Ctop - 1`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`.
The source-data structure now also carries the source-stratum guarded
product-difference coordinate ideal neighborhood, componentwise centered
continuity for the combined family, and the endpoint product-entry count
`H 1 * H(N+1)`.

Boundary: source-side finite coordinate and ideal bookkeeping only. No
analytic coordinate chart, regular-suspension chart construction, analytic
germ-ideal transport, coverage, transition regularity, Jacobian compatibility,
normal crossings, pole order, or RLCT is proved.

Xhigh review by `Descartes the 3rd` passed after repairing the reproduction's
source anchor to distinguish the literal signed/corrected p. 13 display from
the cleaned four-family entry-ideal generator package.

## 2026-06-24 A2 literal product-difference coordinate ideal bridge

Reproduction:
`reproduction-a2-literal-product-difference-coordinate-ideal-bridge.md`.
Statement card:
`statement-card-a2-literal-product-difference-coordinate-ideal-bridge.md`.
Review:
`review-a2-literal-product-difference-coordinate-ideal-bridge.md`.

Lean now names the direct ideal bridge from the literal signed/corrected p. 13
block to the combined product-difference coordinate ideal:

```text
AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal
```

For arbitrary `X`, `F2`, `F3`, and `D`, it proves

```text
matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3 * F2))
  =
AoyagiProductDifferenceCoordinateIndex.entryIdeal X F2 F3 D.
```

The theorem is finite scalar ideal algebra only.  It uses the previous
signed-block cleanup and
`AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal`;
the correction is `F3*F2`, not `F2*F3`.

## 2026-06-24 A2 product-reduction triangular coordinate chart

Reproduction:
`reproduction-a2-product-reduction-triangular-coordinate-chart.md`.
Statement card:
`statement-card-a2-product-reduction-triangular-coordinate-chart.md`.
Review:
`review-a2-product-reduction-triangular-coordinate-chart.md`.

Lean now packages the one-step p. 13 triangular variable change in
`ProductReduction.lean`:

```text
ProductReductionStepRawCoordinates
ProductReductionStepChartCoordinates
ProductReductionStepRawCoordinates.detChart
ProductReductionStepChartCoordinates.detChart
ProductReductionStepRawCoordinates.toChart
ProductReductionStepChartCoordinates.toRaw
ProductReductionStepRawCoordinates.detChart_toChart
ProductReductionStepChartCoordinates.detChart_toRaw
productReductionStepCoordinate_left_inverse
productReductionStepCoordinate_right_inverse
```

The raw variables are `C1, D, F3, A1, A2, A3, A4`; the chart variables are
`Ctop, D, A1, A3, F2, F3, C`.  The forward formulas are
`Ctop=C1*A1`, `F2=-(A1⁻¹*A2)`,
`F3=F3old-D*A3*(C1*A1)⁻¹`, and `C=A4-A3*A1⁻¹*A2`, with inverse formulas that
retain passive `D`, `A1`, and `A3` and never invert `D`.

Boundary: elementary determinant-chart coordinate algebra only.  It does not
prove analytic coordinate chart status, exact-rank/source-rank openness,
regular-suspension chart construction, block-difference wrapper transport,
analytic germ-ideal transport, coverage, Jacobian compatibility, normal
crossings, pole order, or RLCT extraction.

## 2026-06-24 A2 product-reduction step product-difference wrapper

Reproduction:
`reproduction-a2-product-reduction-step-product-difference-wrapper.md`.
Statement card:
`statement-card-a2-product-reduction-step-product-difference-wrapper.md`.
Review:
`review-a2-product-reduction-step-product-difference-wrapper.md`.

Lean now connects the p. 13 coordinate package to the one-step product and
product-difference block identities:

```text
productReductionStepCoordinate_triangularBlockProduct
productReductionStepCoordinate_productDifference
```

The theorem consumes a prior triangular product hypothesis
`[I 0; F3old I] T = [C1 0; 0 D] [A1 A2; A3 A4]`, sets
`y = x.toChart`, and proves
`[I 0; y.F3 I] T [I y.F2; 0 I] = [y.Ctop 0; 0 y.D*y.C]`.
Subtracting `[I 0; 0 0]` gives the signed p. 13 block
`[y.Ctop-I, -y.F2; -y.F3, y.D*y.C - y.F3*y.F2]`.

Boundary: finite block algebra only.  No inverse of `D` is used.  The
lower-right correction is `F3*F2`.  The suffix-state adapter from
`ChartLocalSuffixState.BlockDiagonal` is recorded separately, and the
coordinate-ideal naming bridge is recorded in the literal product-difference
coordinate ideal bridge card.

## 2026-06-24 A2 suffix-state step coordinate adapter

Reproduction:
`reproduction-a2-suffix-state-step-coordinate-adapter.md`.
Statement card:
`statement-card-a2-suffix-state-step-coordinate-adapter.md`.
Review:
`review-a2-suffix-state-step-coordinate-adapter.md`.

Lean now exposes the one-step deterministic suffix-state adapter:

```text
ChartLocalSuffixState.stepRawCoordinates
ChartLocalSuffixState.stepRawCoordinates_detChart
ChartLocalSuffixState.stepRawCoordinates_toChart_Ctop
ChartLocalSuffixState.stepRawCoordinates_toChart_F2
ChartLocalSuffixState.stepRawCoordinates_toChart_C
ChartLocalSuffixState.stepRawCoordinates_toChart_D_mul_C
ChartLocalSuffixState.stepRawCoordinates_toChart_F3_of_L_eq_lowerUnitriangular
ChartLocalSuffixState.stepRawCoordinates_priorProduct
ChartLocalSuffixState.stepRawCoordinates_triangularBlockProduct
ChartLocalSuffixState.stepRawCoordinates_productDifference
```

The adapter builds raw p. 13 coordinates from `S.Ctop`, `S.D`, a witnessed
lower-left block `F3prev` of `S.L`, and the four corners of
`transformedEdge E p S`.  It proves that `S.BlockDiagonal P hpj` supplies the
prior product hypothesis for `T = P p.castSucc j`, then applies the p. 13
coordinate wrappers to get the triangular product and signed
product-difference block.

Boundary: finite block algebra only.  `BlockDiagonal` alone does not prove
`S.L` is lower unitriangular; the adapter takes that witness as an input.
The determinant chart is on `transformedEdge E p S`, not raw `E p`, and no
inverse of `S.D` is used.

## 2026-06-24 A2 suffix-state step coordinate specialization

Reproduction:
`reproduction-a2-suffix-state-step-coordinate-specialization.md`.
Statement card:
`statement-card-a2-suffix-state-step-coordinate-specialization.md`.
Review:
`review-a2-suffix-state-step-coordinate-specialization.md`.

Lean now specializes the previous arbitrary-suffix-state coordinate adapter to
the actual recursive state:

```text
ChartLocalSuffixState.suffixState_stepRawCoordinates_triangularBlockProduct
ChartLocalSuffixState.suffixState_stepRawCoordinates_productDifference
```

For `S = suffixState E j p.succ hpj`, the wrappers keep the local hypotheses
`S.BlockDiagonal P hpj` and
`identityCornerDetChart (transformedEdge E p S)`, choose the lower-left
witness `F3prev` from `suffixState_L_eq_lowerUnitriangular`, and apply the
generic `stepRawCoordinates_*` theorems.  The product matrix is still
`P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj)`, while the raw
coordinate corners come from `transformedEdge E p S`.

Boundary: finite block algebra only.  This does not derive `S.BlockDiagonal`
from global recursion hypotheses, and it does not prove analytic chart
coverage, ideal transport, regular-suspension construction, normal crossings,
pole order, or RLCT.

## 2026-06-24 A2 regular-suspension coordinate map source data

Reproduction:
`reproduction-a2-regular-suspension-coordinate-map-source-data.md`.
Statement card:
`statement-card-a2-regular-suspension-coordinate-map-source-data.md`.
Review:
`review-a2-regular-suspension-coordinate-map-source-data.md`.

Lean now packages the existing scalar p. 13 source-data fields as Pi-valued
coordinate maps:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap
paperEndpointFixedBaseResidualBlockCoordinateMap
paperEndpointFixedBaseProductDifferenceCoordinateMap
```

and proves that the existing fixed-base source-data package supplies centered
continuity for each map:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt
```

The proofs are componentwise: basepoint vanishing is function extensionality
from the scalar source fields, and continuity uses `continuousAt_pi`.

Boundary: finite/topological packaging only.  This does not construct an
analytic coordinate chart, local inverse, source-rank-open neighborhood,
analytic ideal transport, chart coverage, Jacobian compatibility, normal
crossings, pole order, or RLCT.

## 2026-06-24 A2 cleaned coordinate square-sum

Reproduction:
`reproduction-a2-cleaned-coordinate-square-sum.md`.
Statement card:
`statement-card-a2-cleaned-coordinate-square-sum.md`.
Review:
`review-a2-cleaned-coordinate-square-sum.md`.

Lean now names the finite algebraic square-sum of a scalar coordinate family:

```text
aoyagiCoordinateSquareSum
aoyagiCoordinateSquareSum_sumElim
```

and proves the cleaned p. 13 product-difference coordinate family splits over
the regular/residual disjoint sum:

```text
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_eq_regular_add_residual
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim
paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual
```

This gives the exact square-sum decomposition for the cleaned coordinate
family `C1-Er, F2, F3, prod_s C^(s)`.

Boundary: finite square-sum bookkeeping only.  It does not identify this
cleaned square-sum with the literal signed/corrected p. 13 Frobenius loss,
does not prove analytic generator transport or loss comparability, and does
not construct charts, prove Jacobian compatibility, normal crossings, pole
order, or RLCT.

## 2026-06-24 A2 literal product-difference square-sum

Reproduction:
`reproduction-a2-literal-product-difference-square-sum.md`.
Statement card:
`statement-card-a2-literal-product-difference-square-sum.md`.
Review:
`review-a2-literal-product-difference-square-sum.md`.

Lean now names the scalar coordinate family attached to the literal
signed/corrected p. 13 block:

```text
AoyagiProductDifferenceCoordinateIndex.literalValue
AoyagiProductDifferenceCoordinateIndex.literalValue_regular
AoyagiProductDifferenceCoordinateIndex.literalValue_residual
```

and proves the finite square-sum split

```text
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_regular_add_correctedResidual
```

for

```text
fromBlocks X (-F2) (-F3) (D - F3 * F2).
```

The theorem expands the literal square-sum as regular square-sum plus the
corrected residual square-sum for `D - F3 * F2`; the signs disappear by
`(-a)^2 = a^2`.

Boundary: finite square-sum bookkeeping only.  It does not compare
`D - F3*F2` with `D`, prove local loss comparability, prove analytic generator
transport, construct charts, prove Jacobian compatibility, normal crossings,
pole order, or RLCT.

## 2026-06-24 A2 regular-suspension finite loss comparison

Reproduction:
`reproduction-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.
Statement card:
`statement-card-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.
Review:
`review-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`.

Lean now proves the finite ordered-ring square-sum comparison between the
literal p. 13 scalar family

```text
X, -F2, -F3, D - F3 * F2
```

and the cleaned scalar family

```text
X, F2, F3, D.
```

The key new Lean names include:

```text
aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
AoyagiRegularBlockCoordinateIndex.coordinateSquareSum_eq_ctop_add_f2_add_f3
AoyagiProductDifferenceCoordinateIndex.productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum
AoyagiProductDifferenceCoordinateIndex.four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
```

Under the finite smallness hypothesis

```text
squareSum(F2) + squareSum(F3) <= 1,
```

Lean proves both

```text
literalSquareSum <= 2 * cleanedSquareSum,
cleanedSquareSum <= 2 * literalSquareSum.
```

The proof includes the finite row-column Cauchy-Schwarz estimate
`squareSum(F3*F2) <= squareSum(F3) * squareSum(F2)`.

Boundary: finite ordered-ring square-sum comparison only.  The generic real
ambient-neighborhood shrink from centered continuity is a separate entry
below; analytic regular-coordinate status, Fubini/polar regular-variable
shift, chart coverage, Jacobian compatibility, normal crossings, pole order,
and RLCT remain unproved.

Review passed after wording repairs: the factor-`2` theorem docstrings now
state the combined hypothesis `squareSum(F2)+squareSum(F3) <= 1`, and the
statement card no longer claims sharpness of the constant.

## 2026-06-24 A2 continuity-to-small-loss neighborhood

Reproduction:
`reproduction-a2-continuity-to-small-loss-neighborhood.md`.
Statement card:
`statement-card-a2-continuity-to-small-loss-neighborhood.md`.
Review:
`review-a2-continuity-to-small-loss-neighborhood.md`.

Lean now proves the generic real topology that supplies the finite
comparison's smallness hypothesis from centered continuity:

```text
aoyagiCoordinateSquareSum_continuousAt
aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt
aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt
```

The one-family theorem says that if `f : alpha -> eta -> real` is continuous at
`x0` and `f x0 = 0`, then eventually in `nhds x0`,
`aoyagiCoordinateSquareSum (f x) <= 1`.  The two-family theorem applies this
to a disjoint-sum family and proves eventual
`squareSum(f x) + squareSum(g x) <= 1`.  The coordinatewise variants first
assemble per-coordinate centering and continuity into Pi-valued centered
continuity.

Boundary: ambient real finite topology only.  This is not yet specialised to
the p. 13 source-data maps or weakened to the source-rank stratum, and it does
not prove analytic regular-coordinate status, source-rank openness,
Fubini/polar regular-variable shift, chart coverage, Jacobian compatibility,
normal crossings, pole order, or RLCT.

## 2026-06-24 A2 regular-coordinate F2/F3 smallness projection

Reproduction:
`reproduction-a2-regular-coordinate-f2-f3-smallness-projection.md`.
Statement card:
`statement-card-a2-regular-coordinate-f2-f3-smallness-projection.md`.
Review:
`review-a2-regular-coordinate-f2-f3-smallness-projection.md`.

Lean now projects the generic two-family smallness theorem through the p. 13
regular-coordinate tags:

```text
AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
```

For a finite real tagged family
`coord : alpha -> AoyagiRegularBlockCoordinateIndex iota mu nu -> real`, if
every tagged coordinate is centered and continuous at `x0`, then eventually in
`nhds x0` the square-sums of the `F2` and `F3` tagged subfamilies have total at
most `1`.

Boundary: finite real tag projection only.  This is not yet specialised to the
actual fixed-base source-data map and not weakened to a source-rank stratum.
It does not prove analytic regular-coordinate status, source-rank openness,
Fubini/polar regular-variable shift, chart coverage, Jacobian compatibility,
normal crossings, pole order, or RLCT.

Xhigh review passed.  The reviewer confirmed the narrow theorem shape, the
focused module build, and the need for explicit nested-sum type annotations for
the `F2` and `F3` tags.

## 2026-06-24 A2 fixed-base regular-coordinate F2/F3 smallness

Reproduction:
`reproduction-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.
Statement card:
`statement-card-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.
Review:
`review-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`.

Lean now specialises the p. 13 `F2/F3` smallness theorem to the actual real
fixed-base regular-coordinate map in
`PaperEndpointFixedBaseRegularCoordinateSourceData`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source
```

The ambient theorem uses the source-data package's centered-continuous
Pi-valued regular-coordinate map.  The relative theorem is only a weakening to
`nhdsWithin` the source-rank stratum.

Boundary: real finite topology for the actual fixed-base scalar coordinate
map.  This does not prove source-rank openness, analytic coordinate status,
source coverage, analytic ideal transport, Fubini/polar regular-variable
shift, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 fixed-base literal-cleaned square-sum comparison

Reproduction:
`reproduction-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.
Statement card:
`statement-card-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.
Review:
`review-a2-fixed-base-literal-cleaned-square-sum-comparison.md`.

Lean now defines the actual fixed-base literal signed/corrected p. 13 scalar
coordinate family:

```text
paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
```

and proves that, under real
`PaperEndpointFixedBaseRegularCoordinateSourceData`, its square-sum and the
cleaned `paperEndpointFixedBaseProductDifferenceCoordinateMap` square-sum are
eventually mutually bounded by factor `2`, both in ambient `nhds x0` and in
the source-rank `nhdsWithin` filter.  Directional projection theorems expose
each inequality separately.

Boundary: finite real square-sum comparison only.  This does not prove
analytic ideal transport, chart construction, source coverage, source-rank
openness, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 one-step determinant-chart coordinate equivalence

Reproduction:
`reproduction-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Statement card:
`statement-card-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Review:
`review-a2-one-step-determinant-chart-coordinate-equivalence.md`.

Lean now topologizes the raw and chart one-step product-reduction coordinate
structures by their matrix-field product topologies and proves the p. 13
one-step determinant-chart coordinate change is a homeomorphism:

```text
ProductReductionStepRawCoordinates.continuous_toChart_detChart_subtype
ProductReductionStepRawCoordinates.continuous_detChart_toChart
ProductReductionStepChartCoordinates.continuous_toRaw_detChart_subtype
ProductReductionStepChartCoordinates.continuous_detChart_toRaw
productReductionStepCoordinate_detChart_homeomorph
```

The theorem uses the existing algebraic inverse identities from
`ProductReduction.lean` and the matrix-inversion continuity helper in
`ChartTopology.lean`.  The right-inverse proof passes the chart determinant
pair in the required order: `A1` unit first, then `Ctop` unit.

Boundary: finite determinant-chart topology only.  This does not prove
analytic regularity, an analytic Jacobian determinant calculation,
source-rank openness, source coverage, ideal-germ transport, a
regular-suspension certificate, normal crossings, pole order, or RLCT.

## 2026-06-24 A2 p.13 source regular-suspension boundary

Reproduction:
`reproduction-a2-p13-source-regular-suspension-boundary.md`.
Statement card:
`statement-card-a2-p13-source-regular-suspension-boundary.md`.
Review:
`review-a2-p13-source-regular-suspension-boundary.md`.

The source audit pins the p. 13 split: after Theorem 3 the literal
target-centered block is
`[C1-Er, -F2; -F3, prod_s C^(s)-F3F2]`, while the reduced residual family is
the entries of `D = prod_s C^(s)`.  Aoyagi then states the displayed RLCT
shift by the regular count, but pp. 10-14 do not give the analytic
regular-suspension construction, Jacobian/prior computation, coverage, or
normal-crossing lift.  The p. 14 reduction to `r(s)=r` is also via Theorem 4,
not Theorem 3 alone.

Lean now adds only the reviewed source-side wrapper

```text
exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source_of_rank_eq
```

in `RegularSuspensionCoordinates.lean`.  From real rank/source data it chooses
the existing fixed-base regular-coordinate source data and returns the existing
source-rank-stratum factor-`2` comparison between the literal p. 13 square-sum
and the cleaned square-sum.

Boundary: source-data packaging plus finite real square-sum comparison only.
No analytic regular-coordinate chart, source coverage, ideal-germ transport,
Jacobian/prior shift, full normal-crossing certificate, Theorem 4 reduction,
pole order, or RLCT equality is proved.

## 2026-06-24 A2 supplied regular-suspension extraction projection

Reproduction:
`reproduction-a2-supplied-regular-suspension-extraction-projection.md`.
Statement card:
`statement-card-a2-supplied-regular-suspension-extraction-projection.md`.
Review:
`review-a2-regular-suspension-projections-and-loss-shape.md`.

Lean now hardens the supplied full-certificate boundary in
`RegularSuspensionInterface.lean`:

```text
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_eq_reduced_add_half_regularCount
AoyagiSuppliedRegularSuspensionCertificate.
  poleOrder_eq_reduced_exponentOrder
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_eq_reduced_add_regularTerm
AoyagiSuppliedRegularSuspensionCertificate.
  lambda_and_poleOrder_eq_reduced_add_regularTerm
```

These project `Cfull.ExtractionHypothesis lambda poleOrder` through the
supplied finite equality
`Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift regularCount`.
The result is that the external `lambda` equals the reduced finite minimum
plus `regularCount/2`, the external `poleOrder` equals the reduced finite
order, and under the p.13 count with endpoint bounds the shift is Aoyagi's
displayed `aoyagiTheorem2RegularTerm`.

Boundary: extraction remains on `Cfull`.  This does not construct `Cfull`,
extract from `Cred`, prove Fubini/polar regular-variable shift, prove Aoyagi
Lemma 1 or Theorem 4, produce normal crossings, or prove an RLCT theorem beyond
the supplied full-certificate extraction hypothesis.

## 2026-06-24 A2 source-stratum literal regular/residual square-sum

Reproduction:
`reproduction-a2-source-stratum-literal-regular-residual-square-sum.md`.
Statement card:
`statement-card-a2-source-stratum-literal-regular-residual-square-sum.md`.
Review:
`review-a2-regular-suspension-projections-and-loss-shape.md`.

Lean now proves

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source
```

in `RegularSuspensionCoordinates.lean`.  It composes the existing
source-stratum literal/cleaned factor-`2` comparison with the cleaned
product-difference square-sum split:

```text
cleanedSquareSum = regularBlockSquareSum + residualBlockSquareSum.
```

Thus, eventually on the source-rank stratum, the literal p.13 square-sum is
mutually bounded by factor `2` with
`regularBlockSquareSum + residualBlockSquareSum`.

Boundary: finite source-side square-sum comparison only.  No analytic chart,
Fubini/polar shift, normal-crossing certificate construction, pole order, or
RLCT extraction is proved.

## 2026-06-24 A2 regular square-suspension integrability target

Reproduction target:
`reproduction-a2-regular-square-suspension-integrability-target.md`.

The next genuine analytic target is now pinned as an independent Euclidean
product-coordinate theorem: if a full loss is locally comparable to
`|u|^2 + g(y)` with bounded positive density on `R^k x R^m`, then adding the
regular square variables shifts the local power-integrability threshold by
`k/2`.  The proof route is Fubini plus polar-coordinate estimates for

```text
integral_0^eps r^(k-1) (r^2 + a)^(-t) dr.
```

This theorem is not yet formalised.  It is separate from normal-crossing
extraction and still needs actual Aoyagi p.13 product-chart/density hypotheses
before it can be applied.

## 2026-06-24 A2 one-sided regular-suspension integrability

Reproduction:
`reproduction-a2-one-sided-regular-suspension-integrability.md`.
Statement card:
`statement-card-a2-one-sided-regular-suspension-integrability.md`.
Review:
`review-a2-one-sided-regular-suspension-integrability.md`.

Lean now proves the first narrow ENNReal product-measure brick toward the
regular-square theorem:

```text
lintegral_rpow_neg_add_right_le_prod_fst
lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top
lintegral_rpow_neg_add_right_restrict_lt_top_of_lintegral_rpow_neg_restrict_lt_top
```

The pointwise estimate is

```text
(a x + q y)^(-s) <= (a x)^(-s)
```

for `s >= 0`, proved in `ENNReal` by monotonicity of positive powers and
inverse order reversal.  If the extra measure is finite and the base integral
of `(a x)^(-s)` is finite, Tonelli's product formula gives finiteness of the
integral after adding the extra nonnegative term.  The restricted version uses
`nu t < infinity` to make `nu.restrict t` finite.

Boundary: one-sided finite-factor integrability preservation only.  No
threshold definition, no `+ k/2` shift, no polar-coordinate estimate, no
bounded-density theorem, no p.13 analytic chart or Jacobian theorem, no
normal-crossing construction, no pole-order theorem, and no RLCT theorem is
proved.

## 2026-06-24 A2 radial finite-side integrability

Reproduction:
`reproduction-a2-radial-finite-side-integrability.md`.
Statement card:
`statement-card-a2-radial-finite-side-integrability.md`.
Review:
`review-a2-radial-finite-side-integrability.md`.

Lean now proves the first punctured radial finite-side estimate for the
regular-square theorem in `RegularSuspensionIntegrability.lean`:

```text
integrable_norm_rpow_neg_indicator_Ioo
integrable_norm_sq_add_rpow_neg_indicator_Ioo
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top
```

The radial model uses Mathlib's additive-Haar radial integrability theorem to
reduce

```text
x |-> 1_(0,R)(||x||) * ||x||^(-t)
```

to one-dimensional integrability of `r^(d-1-t)` on `(0,R)`, hence proves
finiteness under `t < d = finrank_R(E)`.  The shifted quadratic estimate
dominates

```text
(||x||^2 + a)^(-s)
```

by `||x||^(-2s)` on the punctured interval, for `a >= 0` and `s >= 0`, and
therefore proves integrability under `2*s < d`.  The final theorem only
transfers the real-valued integrability statement to finiteness of the
`ENNReal.ofReal` lower integral.

Boundary: finite side on `1_(0,R)(||x||)` only.  No ball/null-origin transfer,
endpoint theorem, lower/divergence theorem, uniform asymptotic in `a`,
bounded-density theorem, product-coordinate `+k/2` threshold, Aoyagi p.13
analytic chart/Jacobian theorem, normal-crossing construction, pole order, or
RLCT theorem is proved.

## 2026-06-24 A2 null-origin radial integrability

Reproduction:
`reproduction-a2-null-origin-radial-integrability.md`.
Statement card:
`statement-card-a2-null-origin-radial-integrability.md`.
Review:
`review-a2-null-origin-radial-integrability.md`.

Lean now removes the radial puncture at the origin by a.e. congruence in
`RegularSuspensionIntegrability.lean`:

```text
ae_eq_norm_indicator_Ioo_Iio
integrable_norm_sq_add_rpow_neg_indicator_Iio
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top
norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio
integrable_norm_sq_add_rpow_neg_indicator_ball
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
```

The primitive theorem says that for a nonatomic measure, the radial
indicator-extensions by zero for `(0,R)` and `(-infinity,R)` agree almost
everywhere.  The only possible disagreement is at `x=0`, which is null.
The quadratic integrability and `ENNReal.ofReal` lower-integral results then
transfer from the punctured radial theorem under the same finite-side
hypotheses `R>0`, `a>=0`, `s>=0`, and `2*s < finrank`.  The open-ball wrapper
is a pointwise rewrite of `x in Metric.ball 0 R` as `||x|| < R`.

Boundary: a.e. representative transfer only.  No pointwise regularity at the
origin, closed-ball theorem, boundary-sphere nullity, endpoint theorem,
lower/divergence theorem, uniform asymptotic in `a`, bounded-density theorem,
product-coordinate `+k/2` threshold, Aoyagi p.13 analytic chart/Jacobian
theorem, normal-crossing construction, pole order, or RLCT theorem is proved.

## 2026-06-24 A2 product below-critical integrability

Reproduction:
`reproduction-a2-product-below-critical-integrability.md`.
Statement card:
`statement-card-a2-product-below-critical-integrability.md`.
Review:
`review-a2-product-below-critical-integrability.md`.

Lean now proves the first product-coordinate finite-side theorem in
`RegularSuspensionIntegrability.lean`:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

For a finite base measure `mu`, additive Haar measure `nu` on a nontrivial
finite-dimensional real normed regular space `E`, an a.e. nonnegative base
term `a : alpha -> R`, and `2*s < finrank_R(E)`, the lower integral over
`alpha x E` of

```text
ENNReal.ofReal (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s))
```

is finite.  The proof uses a.e. domination by the `a=0` regular-ball integrand:
away from the regular origin, `(a(x)+||u||^2)^(-s) <= (||u||^2)^(-s)`.
Tonelli then factors the majorant as `mu(univ)` times the already-proved
regular open-ball integral.

Boundary: below-regular-critical finite side only.  No `+dim(E)/2` threshold
shift, no theorem for `s >= dim(E)/2`, no endpoint, lower/divergence, uniform
asymptotic in `a`, bounded-density/prior theorem, Aoyagi p.13 analytic
chart/Jacobian theorem, normal-crossing construction, pole order, or RLCT
theorem is proved.

## 2026-06-25 A2 product bounded-away integrability

Reproduction:
`reproduction-a2-product-bounded-away-integrability.md`.
Statement card:
`statement-card-a2-product-bounded-away-integrability.md`.
Review:
`review-a2-product-bounded-away-integrability.md`.
Threshold-shift Lean-route probe:
`scout-a2-regular-square-threshold-shift-lean-route.md`.

Lean now proves the product-coordinate regular-ball estimate away from the
residual zero set in `RegularSuspensionIntegrability.lean`:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le
```

For a finite base measure `mu`, additive Haar measure `nu` on a nontrivial
finite-dimensional real normed regular space `E`, a positive constant
`epsilon`, an a.e. lower bound `epsilon <= a(x)`, and `s>=0`, the lower
integral over `alpha x E` of

```text
ENNReal.ofReal (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s))
```

is finite.  The proof bounds the integrand by `epsilon^(-s)` on the regular
ball, uses `measure_ball_lt_top`, and factors the constant-ball majorant by
`lintegral_prod_mul`.

Boundary: away-from-zero finite side only.  No singular-base bound where
`a(x)` approaches zero, no `+dim(E)/2` threshold shift, no endpoint,
lower/divergence, uniform asymptotic in `a`, bounded-density/prior theorem,
Aoyagi p.13 analytic chart/Jacobian theorem, normal-crossing construction,
pole order, or RLCT theorem is proved.  The next analytic target is the
Japanese-bracket/Haar-scaling supercritical fiber bound recorded in the scout
route probe.

## 2026-06-25 A2 Japanese-bracket supercritical integrability

Reproduction:
`reproduction-a2-japanese-bracket-supercritical-integrability.md`.
Statement card:
`statement-card-a2-japanese-bracket-supercritical-integrability.md`.
Review:
`review-a2-japanese-bracket-supercritical-integrability.md`.

Lean now proves the global supercritical finite-side model package in
`RegularSuspensionIntegrability.lean`:

```text
integrable_one_add_norm_sq_rpow_neg
lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top
```

If `finrank_R(E)/2 < s`, the Japanese-bracket model
`(1+||x||^2)^(-s)` is integrable and has finite `ENNReal.ofReal` lower
integral.  For each fixed `a>0`, `(a+||x||^2)^(-s)` has finite lower integral
by comparison with `min(a,1)^(-s)*(1+||x||^2)^(-s)`.

Boundary: fixed-parameter supercritical finite side only.  No sharp
`a^(finrank/2-s)` dependence, no base-product theorem where `a(y)` approaches
zero, no `+dim(E)/2` threshold shift, no endpoint, lower/divergence, uniform
asymptotic in `a`, bounded-density/prior theorem, Aoyagi p.13 analytic
chart/Jacobian theorem, normal-crossing construction, pole order, or RLCT
theorem is proved.

## 2026-06-25 A2 sharp positive-parameter fiber scaling

Reproduction:
`reproduction-a2-sharp-positive-parameter-fiber-scaling.md`.
Statement card:
`statement-card-a2-sharp-positive-parameter-fiber-scaling.md`.
Review:
`review-a2-sharp-positive-parameter-fiber-scaling.md`.

Lean now proves the sharp fixed-positive-parameter scaling package in
`RegularSuspensionIntegrability.lean`:

```text
lintegral_comp_inv_smul_eq_mul_addHaar
ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical
```

For additive Haar measure on a finite-dimensional real normed space and
`a>0`, the whole-space lower integral of `(a+||u||^2)^(-s)` is exactly
`a^(finrank/2-s)` times the Japanese-bracket lower integral.  The equality is
only Haar scaling and positive real-power algebra; the supercritical
hypothesis `finrank/2<s` is used in the last theorem only to make the
Japanese-bracket constant finite.  Restricting to `ball(0,R)` gives the
sharp ball bound by monotonicity.

Boundary: fixed positive parameter only.  No variable-base product theorem
where `a(x)` approaches zero, no proof that the residual base has finite
`a(x)^(finrank/2-s)` integral, no full `+dim(E)/2` threshold shift, no
endpoint or divergent side, no uniform asymptotic statement, no
bounded-density/prior theorem, no Aoyagi p.13 analytic chart/Jacobian theorem,
no normal-crossing construction, pole order, or RLCT theorem is proved.

## 2026-06-25 A2 variable-base product fiber integrability

Reproduction:
`reproduction-a2-variable-base-product-fiber-integrability.md`.
Statement card:
`statement-card-a2-variable-base-product-fiber-integrability.md`.
Review:
`review-a2-variable-base-product-fiber-integrability.md`.

Lean now proves the first variable-base product theorem using the sharp
fiber estimate:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
```

If `a(x)>0` for base-a.e. `x`, `finrank_R(E)/2<s`, and

```text
∫⁻ x, ENNReal.ofReal (a(x)^(finrank_R(E)/2-s)) dmu < infinity,
```

then the product lower integral of `(a(x)+||u||^2)^(-s)` over
`alpha x ball(0,R)` is finite.  The proof uses `lintegral_prod_le`, then the
fixed-fiber sharp bound for a.e. base point, and finally the finite
base-power hypothesis times the finite Japanese-bracket constant.  No finite
base measure or measurability hypothesis on `a` is required.

Boundary: this does not prove the residual-base hypothesis for Aoyagi's
actual residual coordinates, does not cover a positive-measure zero set of
`a`, and does not prove endpoint/divergence, bounded-density/prior transport,
p.13 analytic chart/Jacobian construction, normal crossings, pole order, or
RLCT.

## 2026-06-25 A2 residual-power threshold-shift bridge

Reproduction:
`reproduction-a2-residual-power-threshold-shift-bridge.md`.
Statement card:
`statement-card-a2-residual-power-threshold-shift-bridge.md`.
Review:
`review-a2-residual-power-threshold-shift-bridge.md`.

Lean now proves the finite-side threshold-shift form of the variable-base
product theorem:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

If `a(x)>0` for base-a.e. `x`, `0<t`, and

```text
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity,
```

then the product lower integral of
`(a(x)+||u||^2)^(-(t+finrank_R(E)/2))` over `alpha x ball(0,R)` is finite.
This is the substitution `s=t+finrank_R(E)/2` in the variable-base theorem:
`0<t` gives `finrank_R(E)/2<s`, and `finrank_R(E)/2-s=-t`.

Boundary: this does not prove that Aoyagi's reduced residual coordinates
satisfy the residual negative-power hypothesis, does not cover a
positive-measure zero set of `a`, and does not prove endpoint/divergence,
threshold equality, bounded-density/prior transport, p.13 analytic
chart/Jacobian construction, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual square-sum integrability socket

Reproduction:
`reproduction-a2-residual-square-sum-integrability-socket.md`.
Statement card:
`statement-card-a2-residual-square-sum-integrability-socket.md`.
Review:
`review-a2-residual-square-sum-integrability-socket.md`.

Lean now specialises the residual-power threshold-shift bridge to Aoyagi's
finite coordinate square-sum convention:

```text
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The generic theorem uses
`a(x)=aoyagiCoordinateSquareSum (b x)`.  The residual-block theorem uses
`a(x)=aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value (D x))`.
In both cases, a.e. positivity and finite residual negative `t`-power lower
integral are hypotheses.

Boundary: this is only an interface socket for the p. 13 residual square-sum.
It does not prove positivity or residual negative-power integrability for
Aoyagi's reduced residual coordinates, does not cover a positive-measure zero
set, and does not prove endpoint/divergence, threshold equality,
bounded-density/prior transport, p.13 analytic chart/Jacobian construction,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 Euclidean coordinate square-sum base integrability

Reproduction:
`reproduction-a2-euclidean-coordinate-square-sum-base-integrability.md`.
Statement card:
`statement-card-a2-euclidean-coordinate-square-sum-base-integrability.md`.
Review:
`review-a2-euclidean-coordinate-square-sum-base-integrability.md`.

Lean now proves the local negative-power base theorem for the free Euclidean
residual-coordinate model in `RegularSuspensionSquareSumIntegrability.lean`:

```text
aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero
ae_aoyagiEuclideanCoordinateSquareSum_pos
ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

For `x : EuclideanSpace ℝ eta`, the finite square-sum
`aoyagiCoordinateSquareSum (fun i => x i)` is `||x||^2`.  Hence it is
positive away from the origin, positive a.e. for nonatomic measures, and has
finite local negative `t`-power lower integral on `ball(0,R)` when
`R>0`, `0<=t`, and `2*t < card eta`.  The final theorem composes this base
integrability with the existing square-model product socket.

Boundary: this is only the free Euclidean coordinate model.  It does not prove
residual-base integrability for Aoyagi's product residual `D=prod_s C^(s)`,
does not show that the p.13 residual product map is locally equivalent to free
coordinates, does not cover zero-dimensional residual blocks, and does not
prove endpoint/divergence, threshold equality, bounded-density/prior
transport, p.13 analytic chart/Jacobian construction, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 negative-power lower-bound comparison

Reproduction:
`reproduction-a2-negative-power-lower-bound-comparison.md`.
Statement card:
`statement-card-a2-negative-power-lower-bound-comparison.md`.
Review:
`review-a2-negative-power-lower-bound-comparison.md`.

Lean now proves a reusable residual-base comparison theorem in
`RegularSuspensionIntegrability.lean`:

```text
lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le
```

If `c>0`, `0<=t`, `a(x)>0` a.e., `c*a(x)<=b(x)` a.e., and

```text
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity,
```

then

```text
∫⁻ x, ENNReal.ofReal (b(x)^(-t)) dmu < infinity.
```

The pointwise calculation is
`b^(-t) <= (c*a)^(-t) = c^(-t)*a^(-t)`, using nonpositive exponent
monotonicity and positive-factor multiplicativity.

Boundary: this is only a comparison theorem.  It does not construct a lower
bound for Aoyagi's product residual, does not prove monomial integrability,
does not prove a finite chart cover theorem, and does not prove
bounded-density/prior transport, endpoint/divergence, threshold equality, p.13
analytic chart/Jacobian construction, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 positive-box monomial integrability

Reproduction:
`reproduction-a2-positive-box-monomial-integrability.md`.
Statement card:
`statement-card-a2-positive-box-monomial-integrability.md`.
Review:
`review-a2-positive-box-monomial-integrability.md`.

Lean now proves the positive-box monomial factor theorem in
`MonomialChartIntegrability.lean`:

```text
lintegral_ofReal_rpow_restrict_Ioo_lt_top
lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top
lintegral_ofReal_fintype_rpow_positiveBox_lt_top
lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top
```

The general product theorem says that for finite `i`, `R_i>0`, and
`p_i>-1`,

```text
int^- x, ofReal(prod_i x_i^(p_i))
  d Measure.pi (i |-> volume.restrict (0,R_i))
<
infinity.
```

The Aoyagi-specialized theorem sets `p_i=h_i-2*t*k_i`, so the strict
inequality `2*t*k_i<h_i+1` gives the required `p_i>-1`.

Boundary: this is the positive-coordinate model only.  It does not prove a
residual-loss lower bound, density/prior upper bound, signed-box
absolute-value theorem, finite chart cover, endpoint/divergence, threshold
equality, p.13 analytic chart/Jacobian construction, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 positive-box monomial domination

Reproduction:
`reproduction-a2-positive-box-monomial-domination.md`.
Statement card:
`statement-card-a2-positive-box-monomial-domination.md`.
Review:
`review-a2-positive-box-monomial-domination.md`.

Lean now proves direct positive-box monomial domination transfer in
`MonomialChartIntegrability.lean`:

```text
lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top
lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top
```

If an arbitrary real integrand `f` is a.e. bounded above by
`A * prod_i x_i^(p_i)` on the positive-box product measure, with `0<=A`,
`R_i>0`, and `p_i>-1`, then `int^- ofReal(f)` is finite.  The Aoyagi wrapper
uses `p_i=h_i-2*t*k_i` under the strict inequalities `2*t*k_i<h_i+1`.

Boundary: this is only a domination-transfer theorem.  It does not derive the
upper bound from residual-loss and density estimates, does not handle
signed/absolute-value boxes, and does not prove chart coverage, endpoint or
divergent behavior, threshold equality, p.13 analytic chart/Jacobian
construction, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 positive-box residual/density comparison

Reproduction:
`reproduction-a2-positive-box-residual-density-comparison.md`.
Statement card:
`statement-card-a2-positive-box-residual-density-comparison.md`.
Review:
`review-a2-positive-box-residual-density-comparison.md`.

Lean now proves the positive-box bridge from separate supplied loss/density
bounds to finite lower-integral control in `MonomialChartIntegrability.lean`:

```text
ae_forall_pos_measure_pi_restrict_Ioo
loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos
lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top
```

The finite theorem assumes `c>0`, `C>=0`, `t>=0`, `R_i>0`, the strict
inequalities `2*t*k_i<h_i+1`, and the a.e. positive-box bounds

```text
c * prod_i x_i^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i x_i^(h_i).
```

It concludes

```text
int^- x, ofReal(loss(x)^(-t) * density(x)) < infinity
```

for the product positive-box measure.  The proof uses a.e. coordinate
positivity, real-power order reversal for exponent `-t`, product power
arithmetic on positive coordinates, and the landed monomial domination theorem.

Boundary: this is still positive-box comparison only.  It does not handle
signed or absolute-value boxes, does not prove the supplied bounds for
Aoyagi's actual charts, and does not prove analytic density/Jacobian
transport, chart coverage, endpoint or divergent behavior, threshold equality,
p.13 analytic chart/Jacobian construction, normal crossings, pole order, or
RLCT.

## 2026-06-25 A2 p.13 half loss lower bound

Reproduction:
`reproduction-a2-p13-half-loss-lower-bound.md`.
Statement card:
`statement-card-a2-p13-half-loss-lower-bound.md`.

Lean now proves the lower-bound corollary of the p.13 source-stratum
literal/cleaned factor-`2` comparison in `RegularSuspensionCoordinates.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq
```

The first theorem proves eventually on the fixed-base source-rank stratum

```text
(1/2) * (regularSquareSum + residualSquareSum) <= literalSquareSum.
```

The second composes this with a supplied ambient comparison
`c * literalSquareSum <= loss`, with `c>=0`, to get

```text
(c/2) * (regularSquareSum + residualSquareSum) <= loss.
```

Boundary: this is finite p.13 square-sum bookkeeping only.  It does not prove
the original DLN loss comparison, analytic coordinate status, chart coverage,
Jacobian/prior density transport, regular-suspension additivity, normal
crossings, pole order, or RLCT.

## 2026-06-25 A2 signed-box model-loss adapter

Reproduction:
`reproduction-a2-signed-box-model-loss-adapter.md`.
Statement card:
`statement-card-a2-signed-box-model-loss-adapter.md`.

Lean now proves the generic signed-box comparison adapter in
`MonomialChartIntegrability.lean`:

```text
lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top_of_modelLoss_le_const_mul_loss
```

If `c*M <= modelLoss` and `modelLoss <= K*loss` a.e. with `c>0` and `K>0`,
then `(c/K)*M <= loss` a.e.; the theorem delegates to the existing signed-box
residual/density comparison with constant `c/K`.

Boundary: this is comparison plumbing only.  It does not construct the model
loss, convert p.13 source-filter facts into signed-box a.e. chart hypotheses,
prove density/Jacobian transport, chart coverage, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 regular-square bounded-density wrapper

Reproduction:
`reproduction-a2-regular-square-bounded-density-wrapper.md`.
Statement card:
`statement-card-a2-regular-square-bounded-density-wrapper.md`.

Lean now proves the bounded-density finite-side regular-square-suspension
wrapper in `RegularSuspensionSquareSumIntegrability.lean`:

```text
lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The theorem consumes supplied product-measure hypotheses:

```text
0 < aoyagiCoordinateSquareSum (b x)  a.e.,
int^- x, ofReal(aoyagiCoordinateSquareSum(b x)^(-t)) < infinity,
c * (aoyagiCoordinateSquareSum(b x)+||u||^2) <= loss(x,u),
0 <= density(x,u),
density(x,u) <= C
```

on the regular ball, with `c>0`, `C>=0`, and `t>0`.  It concludes finite
lower integral of `loss^(-(t+dim(E)/2))*density` over the regular ball.

Boundary: this is a one-sided finite-integrability wrapper only.  It does not
prove Aoyagi's p.13 analytic product chart, the lower loss bound,
density/Jacobian transport, residual integrability, endpoint/divergent-side
behavior, threshold equality, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 p.13 regular-coordinate bounded-density adapter

Reproduction:
`reproduction-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Statement card:
`statement-card-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Review:
`review-a2-p13-regular-coordinate-bounded-density-adapter.md`.

Lean now specialises the bounded-density finite-side regular-square theorem to
the fixed-base p.13 regular coordinate index in
`RegularSuspensionSquareSumIntegrability.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
```

The first theorem rewrites the Euclidean regular-coordinate fiber dimension as
`aoyagiTheorem2RegularVariableCount N H r`.  The second consumes supplied
product-measure hypotheses for the residual square-sum, lower loss comparison,
and bounded density, with the p.13 regular term written as
`aoyagiCoordinateSquareSum (fun i => u i)`, and proves finite
lower-integrability at exponent
`t + aoyagiTheorem2RegularVariableCount N H r / 2`.

Boundary: this is source-facing finite-side adapter only.  It does not turn
source-stratum filter facts into product-measure a.e. hypotheses, construct
Aoyagi's p.13 analytic product chart, compare the original DLN loss with the
p.13 literal square-sum, prove Jacobian/prior density transport, prove
residual-base integrability, or prove endpoint/divergence, threshold equality,
normal crossings, pole order, or RLCT.

## 2026-06-25 A2 local measure handoff

Reproduction:
`reproduction-a2-local-measure-handoff.md`.
Statement card:
`statement-card-a2-local-measure-handoff.md`.
Review:
`review-a2-local-measure-handoff.md`.

Lean now proves a generic local support handoff in
`LocalMeasureHandoff.lean`:

```text
exists_open_ae_restrict_inter_of_eventually_nhdsWithin
exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
```

If a property holds eventually in `nhdsWithin x0 S`, then after shrinking to
some open neighborhood `U` of `x0`, it holds almost everywhere for any measure
restricted to `U ∩ S`.  The product version pulls the same base a.e. fact back
along first projection for `(mu.restrict (U ∩ S)).prod nu`.

Boundary: this is only a filter-to-restricted-measure conversion.  It does not
construct a p.13 product chart, identify source coordinates with
residual-base plus regular-fiber product coordinates, compare losses, transport
density/Jacobian factors, prove integrability, produce normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 regular-suspension local measure handoff

Reproduction:
`reproduction-a2-regular-suspension-local-measure.md`.
Statement card:
`statement-card-a2-regular-suspension-local-measure.md`.
Review:
`review-a2-regular-suspension-local-measure.md`.

Lean now packages two p.13 fixed-base source-filter comparisons as
restricted-measure a.e. facts in `RegularSuspensionLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
```

The inputs are a measurable fixed-base source rank stratum and the already
proved p.13 `nhdsWithin` comparisons.  The conclusions produce an open
neighborhood `U` such that the corresponding inequality holds a.e. for
`mu.restrict (U ∩ sourceStratum)`, and in product form after replacing the
base point by `z.1`.

Boundary: the first product forms are first-coordinate handoffs only.  They do
not identify an auxiliary product fiber with p.13 regular coordinates and do
not derive the product-fiber `regularSquareSum(u)` lower bound needed by the
finite-side integrability adapter.  The uniform-in-fiber theorem transports
such loss/density bounds only when they are separately supplied on the source
filter.  None of these wrappers prove source-stratum measurability, chart
construction, original loss comparison, density/Jacobian transport, residual
positivity/integrability, normal crossings, pole order, or RLCT.

The last theorem handles the stronger case where the source filter already
contains uniform-in-fiber loss and density bounds for all p.13 regular
coordinate vectors in a ball.  It intersects those eventual facts and produces
the three product-measure a.e. hypotheses expected by the finite-side p.13
regular-coordinate adapter.  It still does not prove the uniform bounds,
residual positivity, or residual negative-power integrability.

The finite-integral bridge then adds the residual positivity and residual
negative-power integral as explicit source-stratum hypotheses, restricts them
from `sourceStratum` to `U ∩ sourceStratum`, and invokes the p.13 finite-side
bounded-density adapter.  Its conclusion is finite lower-integrability of
`loss^(-(t + regularCount/2))*density` over the local product measure.  It is
not a chart, original-loss, density/Jacobian, residual-integrability,
normal-crossing, pole-order, or RLCT theorem.

## 2026-06-25 A2 source-rank stratum measurability

Reproduction:
`reproduction-a2-source-rank-stratum-measurability.md`.
Statement card:
`statement-card-a2-source-rank-stratum-measurability.md`.
Review:
`review-a2-source-rank-stratum-measurability.md`.

Lean now proves the measurable-source-stratum input under continuous-family
hypotheses.  The finite matrix bridge in `ChartTopology.lean` proves rank
inequalities by determinantal minors, closedness of finite matrix `rank <= r`
loci, and measurability of exact-rank loci for continuous matrix families:

```text
matrix_rank_le_iff_forall_submatrix_det_eq_zero
isClosed_matrix_rank_le
measurableSet_matrix_rank_le_of_continuous
measurableSet_matrix_rank_eq_of_continuous
```

`ProductReductionBoundary.lean` then proves:

```text
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous_finBasisMatrix
measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous_finBasisMatrix
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
```

Boundary: this is measurability, not exact-rank openness.  It requires
continuous finite-basis coordinate matrices, or a globally continuous edge
family `Cedge`; it does not derive global measurability from only a
`ContinuousAt Cedge x0` hypothesis.  It does not prove product-chart
construction, original-loss comparison, density/Jacobian transport, residual
positivity/integrability, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 continuous density local bounds

Reproduction:
`reproduction-a2-continuous-density-local-bounds.md`.
Statement card:
`statement-card-a2-continuous-density-local-bounds.md`.
Review:
`review-a2-continuous-density-local-bounds.md`.

Lean now proves a generic topological density-boundedness handoff in
`LocalMeasureHandoff.lean`:

```text
exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

If a supplied density factor is continuous at `(x0,0)` and positive there,
then for some `R <= Rmax` and `C >= 0`, eventually near `x0` and for every
regular-coordinate vector in `ball(0,R)`, one has `0 <= density <= C`.

`RegularSuspensionLocalMeasure.lean` now also abstracts residual
source-restriction plumbing and gives a p.13 local finite-integral consumer:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
```

Boundary: this removes only the separate supplied density nonnegativity and
upper-bound filters once the transported density factor is supplied as positive
and continuous at the center.  It does not construct that density/Jacobian
factor, prove source-measure transport, prove the original-loss lower
comparison, or prove residual positivity/integrability, normal crossings, pole
order, or RLCT.

## 2026-06-25 A2 residual zero-locus handoff

Reproduction:
`reproduction-a2-residual-zero-locus-handoff.md`.
Statement card:
`statement-card-a2-residual-zero-locus-handoff.md`.
Review:
`review-a2-residual-zero-locus-handoff.md`.

Lean now proves the generic nonnegative-function handoff

```text
ae_pos_of_forall_nonneg_of_measure_zero_eq_zero
```

and applies it to the Aoyagi residual square-sum:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSquareSum_pos_ae_of_zero_set_null
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono_of_zero_set_null
```

This weakens the residual positivity input for downstream local finite-integral
bridges: instead of supplying `0 < residualSquareSum` a.e. directly, it is
enough to supply that the residual zero locus is null for the restricted source
measure.  The residual negative-power integral is still supplied, and the
zero-locus nullity itself is still a real chart/source-measure input.

Boundary: this does not prove residual zero-locus nullity, residual
negative-power integrability, source-measure transport, the original-loss lower
comparison, density/Jacobian transport, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual source-measure map handoff

Reproduction:
`reproduction-a2-residual-source-measure-map-handoff.md`.
Statement card:
`statement-card-a2-residual-source-measure-map-handoff.md`.
Review:
`review-a2-residual-source-measure-map-handoff.md`.

Lean now proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map
```

This is a source-measure transport constructor for the two residual inputs of
the p.13 local finite-integral bridge.  If `mu.restrict source` is supplied as
`Measure.map chart nu`, and residual positivity plus residual negative-power
integrability are supplied after pulling back along `chart`, then the source
side has:

```text
residualSquareSum > 0 a.e.,
residualNegPowerIntegrableOn ...
```

The proof uses `ae_map_iff` for the a.e. positivity statement and
`lintegral_map_le` for the lower-integral finiteness statement.

Boundary: this does not construct the chart, prove the pushforward identity,
compute a Jacobian, bound a density, prove monomial residual lower control,
compare the original DLN loss, produce normal crossings, compute pole order, or
extract an RLCT.

## 2026-06-25 A2 signed-box residual source-measure handoff

Opened a density-free residual source-measure slice after the generic
pushforward handoff.  Scope is only an unweighted signed-box product measure:
given a supplied pushforward identity and a supplied chart-side lower bound
`c * product_i |y_i|^(2*k_i) <= residualSq(chart y)`, derive chart-side
residual positivity and finite `ofReal(residualSq^(-t))` integral under
`t >= 0` and the strict coordinate conditions `2*t*k_i < 1`, then transport
the pair to the source.

Lean adds
`lintegral_ofReal_loss_rpow_neg_signedBox_lt_top` in
`MonomialChartIntegrability.lean` and
`residualSourceHypotheses_of_measure_map_signedBox_monomialLower` in
`RegularSuspensionLocalMeasure.lean`.

This remains unweighted product-measure plumbing.  It does not construct the
chart, prove the pushforward identity, transport Jacobian/density factors,
compare the original DLN loss, prove the density-weighted Aoyagi
`2*t*k_i < h_i+1` calculation for source measures, produce normal crossings,
or extract an RLCT.  Reproduction and statement card:
`reproduction-a2-signed-box-residual-source-measure-handoff.md` and
`statement-card-a2-signed-box-residual-source-measure-handoff.md`.
Review:
`review-a2-signed-box-residual-source-measure-handoff.md`.

Controller verified targeted builds for
`DLNFibre.DLN.Aoyagi.MonomialChartIntegrability` and
`DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure`, full `DLNFibre` build,
`scripts/sorries`, and `git diff --check`.  The full build still emits many
pre-existing style/Core warnings, but no failures.

## 2026-06-25 A2 weighted signed-box residual source-measure handoff

Opened the density-weighted version of the signed-box source-measure handoff.
Scope is still measure plumbing: if the source measure is supplied as the
pushforward of
`signedBox.withDensity (fun y => ENNReal.ofReal (density y))`, and the
residual lower bound plus density nonnegativity/monomial upper bound are
supplied a.e. on the underlying signed box, then the residual source
positivity/integrability pair follows under the Aoyagi-style strict
inequalities `2*t*k_i < h_i+1`.

Lean adds
`residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower`
in `RegularSuspensionLocalMeasure.lean`, reusing the previously landed
`lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top` and generic
pushforward handoff.

This still does not construct the chart, prove the weighted pushforward
identity, compute or regularize a Jacobian/density factor, compare the original
DLN loss, produce normal crossings, compute pole order, or extract an RLCT.
Reproduction and statement card:
`reproduction-a2-weighted-signed-box-residual-source-measure-handoff.md` and
`statement-card-a2-weighted-signed-box-residual-source-measure-handoff.md`.
Review:
`review-a2-weighted-signed-box-residual-source-measure-handoff.md`.

Controller verified the focused
`DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure` build, full `DLNFibre`
build, `scripts/sorries`, and `git diff --check`.  The full build still emits
many pre-existing style/Core warnings, but no failures.

## 2026-06-25 A2 fixed-base triangular multiplier local boundedness

Reproduction:
`reproduction-a2-fixed-base-triangular-multiplier-local-boundedness.md`.
Statement card:
`statement-card-a2-fixed-base-triangular-multiplier-local-boundedness.md`.
Review:
`review-a2-fixed-base-triangular-multiplier-local-boundedness.md`.

Lean now proves generic local-boundedness helpers for continuous real
functions and finite square-sums, then applies them to the deterministic p.13
triangular multiplier product:

```text
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source
```

The source-data consumer

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
```

derives both the self-base product-reduction certificate and the multiplier
bound from `hCedge`/`hbase`, chooses `c=Kmul^{-1}`, and returns a positive
constant for the adapted fixed-base product-difference square-sum lower bound
on the source-rank filter.

Boundary: this is not an original DLN/statistical loss comparison, not
source-rank openness, not analytic chart or measure transport, not normal
crossings, not pole order, and not RLCT extraction.

## 2026-06-25 A2 adapted product-difference local-measure handoff

Reproduction:
`reproduction-a2-adapted-product-difference-local-measure-handoff.md`.
Statement card:
`statement-card-a2-adapted-product-difference-local-measure-handoff.md`.
Review:
`review-a2-adapted-product-difference-local-measure-handoff.md`.

Lean now proves the restricted-measure and product first-projection a.e.
wrappers for the positive self-base adapted fixed-base product-difference
lower bound:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
```

The proof preserves the upstream positive constant and applies the existing
local-measure handoff from `nhdsWithin` eventual predicates to a.e. predicates
on `mu.restrict (U inter sourceStratum)`, and its product-measure
first-projection version.

Boundary: the right-hand side is still only
`paperEndpointFixedBaseAdaptedProductDifferenceSquareSum`.  This does not
compare with original `lossDLN`, construct the p.13 product chart, transport
Jacobian/prior density, prove residual positivity/integrability, produce normal
crossings, compute pole order, or extract an RLCT.

An xhigh original-loss audit is recorded at
`audit-a2-original-loss-to-p13-boundary.md`: any future theorem connecting
original DLN/statistical loss to p.13 coordinates must either prove or assume a
positive local comparison from original loss to the adapted product-difference
square-sum.  Aoyagi p.13 alone is not being treated as that bridge.

## 2026-06-25 A2 adapted product-difference local finite-integral handoff

Reproduction:
`reproduction-a2-adapted-product-difference-local-finite-integral-handoff.md`.
Statement card:
`statement-card-a2-adapted-product-difference-local-finite-integral-handoff.md`.
Review:
`review-a2-adapted-product-difference-local-finite-integral-handoff.md`.

Lean now proves the conditional finite-integral handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem takes an independent product edge-family `CedgeProd`, a supplied
product-coordinate adapted lower bound

```text
c * (residualSquareSumBase(x) + squareSum(u))
  <= paperEndpointFixedBaseAdaptedProductDifferenceSquareSum(CedgeProd(x,u)),
```

and a supplied identification of that adapted square-sum with `chartLoss(x,u)`.
It then delegates to the existing p.13 local finite-integral theorem and
returns a ball-local, indicator-supported finite integral for
`chartLoss^(-(t+regularCount/2))*density`.

Boundary: this does not derive the product-coordinate lower bound from the
base-only self-base comparison, construct a product chart, prove source
coverage, transport Jacobian/prior density, prove residual
positivity/integrability, compare original `lossDLN`, produce normal crossings,
compute pole order, or extract an RLCT.

## 2026-06-25 A2 residual positive-set measurability handoff

Reproduction:
`reproduction-a2-residual-positive-set-measurability-handoff.md`.
Statement card:
`statement-card-a2-residual-positive-set-measurability-handoff.md`.
Review:
`review-a2-residual-positive-set-measurability-handoff.md`.

Lean now proves

```text
measurable_aoyagiCoordinateSquareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.measurableSet_residualSquareSum_pos_of_measurable
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual
```

The first theorem is generic finite square-sum measurability.  The second
derives measurability of the residual square-sum positive set from global
measurability of the p.13 residual coordinate map.  The third removes the
explicit `hpos_meas` premise from the weighted signed-box residual source
constructor under that same residual-coordinate measurability assumption.

Boundary: this does not prove global residual-coordinate measurability from the
edge family or suffix-state recursion, residual positivity/integrability by
itself, the weighted pushforward identity, chart construction, density/Jacobian
transport, original-loss comparison, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 residual-coordinate map measurability

Reproduction:
`reproduction-a2-residual-coordinate-map-measurability.md`.
Statement card:
`statement-card-a2-residual-coordinate-map-measurability.md`.
Review:
`review-a2-residual-coordinate-map-measurability.md`.

Lean now proves the deterministic suffix-recursion measurability bridge:

```text
measurable_matrix_inv_real
measurable_chartLocalSuffixState_suffixState_fields_real
measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
```

The edge hypothesis is the measurable Pi-valued fixed-basis matrix family
`x |-> paperEndpointFixedBaseEdgeMatrixOfReverseEdges ... (fun p => Cedge x p)`.
This is the matrix family actually consumed by the p.13 deterministic suffix
state.  The proof uses finite real matrix Borel operations, including global
measurability of totalized matrix inverse, and then projects the final `D`
block.

Boundary: this deliberately does not assert raw `Measurable Cedge` for
arbitrary non-normed continuous-linear-map spaces.  It also does not prove
source-rank openness, analytic chart construction, pushforward, density or
Jacobian transport, original-loss comparison, residual positivity or
integrability by itself, normal crossings, pole order, or RLCT.

## 2026-06-25 A2 signed-box residual source finite-integral bridge

Reproduction:
`reproduction-a2-signed-box-residual-source-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-signed-box-residual-source-finite-integral-bridge.md`.
Review:
`review-a2-signed-box-residual-source-finite-integral-bridge.md`.

Lean now proves the direct p.13 finite-integral handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem first invokes
`residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`
to obtain residual positivity and residual negative-power integrability on
the source-rank stratum, then passes those two hypotheses to
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top`.

Boundary: source-stratum measurability, fixed-basis edge-matrix
measurability, `0 < t`, signed-box chart a.e.-measurability, source-density
a.e.-measurability, weighted source pushforward, signed-box residual monomial
lower bound, source-density a.e. nonnegativity, signed-box density monomial
upper bound, and local regular-fiber loss/density bounds remain explicit
inputs.  This does not construct a p.13 chart, prove the pushforward, transport
Jacobian/prior density, compare original `lossDLN`, produce normal crossings,
compute pole order, or extract an RLCT.

## 2026-06-25 A2 signed-box residual continuous-density finite-integral bridge

Reproduction:
`reproduction-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.
Review:
`review-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.

Lean now proves the radius-shrinking p.13 finite-integral handoff

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem first obtains residual positivity and residual negative-power
integrability from the measurable-edge weighted signed-box residual-source
constructor, then passes those to
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density`.
The second theorem shrinks the regular-coordinate radius using positivity and
continuity of the supplied product density at `(x₀,0)`.

Boundary: source-stratum measurability, fixed-basis edge-matrix
measurability, `0 < t`, signed-box chart a.e.-measurability, source-density
a.e.-measurability/nonnegativity/upper bound, weighted source pushforward,
signed-box residual monomial lower bound, positive continuous product density,
and the local regular-fiber loss lower bound remain explicit inputs.  This
does not construct a chart, prove the pushforward, transport Jacobian/prior
density, compare original `lossDLN`, produce normal crossings, compute pole
order, or extract an RLCT.

## 2026-06-25 A2 continuous-edge signed-box continuous-density finite-integral bridge

Reproduction:
`reproduction-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.
Statement card:
`statement-card-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.
Review:
`review-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.

Lean now proves the global-continuous-edge variant

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density
```

in `RegularSuspensionLocalMeasure.lean`.

The theorem derives source-rank-stratum measurability from
`measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous`, derives
fixed-basis endpoint edge-matrix measurability by composing `Continuous Cedge`
with `continuous_linearMap_toMatrix`, and then delegates to the signed-box
continuous-density finite-integral bridge.

Boundary: this assumes global `Continuous Cedge`; it does not derive the
result from only `ContinuousAt Cedge x₀`, does not assert source-rank openness,
and does not introduce a raw `Measurable Cedge` interface.  The signed-box
chart, weighted pushforward, source-density hypotheses, residual lower bound,
positive continuous product density, and local regular-fiber loss lower bound
remain explicit inputs.  This does not construct a chart, prove the
pushforward, transport Jacobian/prior density, compare original `lossDLN`,
produce normal crossings, compute pole order, or extract an RLCT.
