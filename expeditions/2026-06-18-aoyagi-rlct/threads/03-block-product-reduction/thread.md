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
