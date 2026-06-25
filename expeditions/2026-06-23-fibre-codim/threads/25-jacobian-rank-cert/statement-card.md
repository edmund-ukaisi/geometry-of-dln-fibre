# Statement card — H3a: the fibre Jacobian + tangent = ker identity

Module `lean/DLNFibre/Core/FibreJacobian.lean` (new file, imports `Core.MultDifferential`,
`Core.CotangentJacobian`). Plus an in-place generalisation of `Core.CotangentJacobian` (the Jacobian
row index `Fin m → Fintype ι`). Import to be appended to `DLNFibre.lean` (single-writer; controller
wires it):

    import DLNFibre.Core.FibreJacobian

Sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`). Commit `ad5cfe06`.
Reviewed (fidelity, SURVIVED, all six questions FAITHFUL; decorrelated Codex on Q1+Q4).

**Scope (name = content).** Rung H3a of the HEIGHT-DIRECT route: the *mechanical setup* — assemble
the Jacobian of the fibre generators and establish the tangent = `ker(Jacobian)` identity at a
rational point of the fibre. **No result here computes the rank value `C + δ`** (that is H3b, the
pen-and-paper job) and **none invokes genericity or smoothness** (H3c). No result claims
`codim = C + δ`.

**Notation.** `d : Fin (N+1) → ℕ` the dimension vector; `RepCoord d = Σ i : Fin N, Fin (d i.succ) ×
Fin (d i.castSucc)` (one coordinate per matrix entry; `card (RepCoord d) = Σ_i d_{i+1}·d_i` = total
matrix entries); `Tuple d` the composable matrix tuple; `mult d A` the ordered product; `B : Matrix
(Fin d_N) (Fin d_0) k` the target; `multPoly d r c`, `fibreGenSet d B`, `fibreGenIdeal d B`,
`canonicalCoord d` from `Core.MultComorphism`/`Core.OrbitCodim`; `multSuffix`/`multPrefix` the
suffix/prefix products and `eval_pderiv_multPoly` the evaluated differential from
`Core.MultDifferential`. `[Field k]` throughout (the cotangent identity needs a field).

---

> **Generalisation (CotangentJacobian, `Fin m → Fintype ι`).** The Jacobian
> (`jacobianMatrix`/`jacobian`/`jacobianTranspose`) and the headline
> `finrank_cotangentSpace_eq_finrank_ker_jacobian` now take a generator family `g : ι → MvPolynomial
> σ k` for an arbitrary `[Fintype ι] [DecidableEq ι]` row index (was `Fin m`).
>
> - **Lean:** `Core.CotangentJacobian` — every changed line is a pure type substitution; proof
>   bodies (incl. the conormal/Kähler chain `finrank_tensor_kaehler_eq_coker`) unchanged.
> - **Gloss.** The rows of the Jacobian are indexed by whatever type is natural for the generators.
> - **Proved.** Statement identical in meaning; the only `Fin m` usages were `Pi.basisFun`/`Pi.single`,
>   which work for any `Fintype + DecidableEq`. **Assumed / Cited / Deferred.** none.

> **Claim 1 (fibre generators as a family).** The fibre generators
> `g_{(r,c)} = multPoly d r c − C (B r c)`, indexed by the output entry `(r,c) : Fin d_N × Fin d_0`;
> their range is `fibreGenSet d B` and their span is `fibreGenIdeal d B`.
>
> - **Lean:** `fibreGen (d) (B) : Fin d_N × Fin d_0 → MvPolynomial (RepCoord d) k`;
>   `range_fibreGen : Set.range (fibreGen d B) = fibreGenSet d B` (`rfl`);
>   `span_range_fibreGen : Ideal.span (Set.range (fibreGen d B)) = fibreGenIdeal d B` (`rfl`).
> - **Proved.** Definitional. **Assumed / Cited / Deferred.** none.

> **Claim 2 (vanishing at a fibre point).** At a tuple `A` with `mult d A = B`, every fibre
> generator vanishes at the rational point `canonicalCoord d A`.
>
> - **Lean:** `eval_fibreGen_eq_zero (d) (B) (A) (hA : mult d A = B) (rc) :
>   eval (canonicalCoord d A) (fibreGen d B rc) = 0`.
> - **Gloss / proof.** `map_sub`, `eval_multPoly` (the bridge), `eval_C`, `hA`, `sub_self`.
> - **Proved** from `mult d A = B` alone. **Assumed / Cited / Deferred.** none.

> **Claim 3 (the fibre Jacobian, closed-form entry).** The fibre Jacobian matrix at `A` has rows =
> output entries `(r,c)`, columns = variables `⟨i,s,t⟩`; entry
> `= multSuffix d A i.succ r s · multPrefix d A i.castSucc t c` (the constant `C (B r c)` killed by
> `pderiv`, so the entry is the bare `multPoly` differential `eval_pderiv_multPoly`).
>
> - **Lean:** `fibreJacobianMatrix (d) (B) (A) : Matrix (Fin d_N × Fin d_0) (RepCoord d) k :=
>   jacobianMatrix (fibreGen d B) (canonicalCoord d A)`; `fibreJacobian (d) (B) (A) := jacobian …`;
>   `fibreJacobianMatrix_apply (d) (B) (A) (r) (c) (i) (s) (t) :
>   fibreJacobianMatrix d B A (r,c) ⟨i,s,t⟩ = multSuffix d A i.succ r s * multPrefix d A i.castSucc t c`.
> - **Gloss / proof.** `map_sub`, `pderiv_C`, `sub_zero`, `eval_pderiv_multPoly`.
> - **Proved.** The closed-form entry. **Assumed / Cited / Deferred.** none.

> **Claim 4 (tangent = ker Jacobian, UNCONDITIONAL).** For `A` in the fibre, the local cotangent
> space of the fibre coordinate ring (`MvPolynomial / fibreGenIdeal d B`) at the rational point
> `canonicalCoord d A` has `k`-dimension equal to `finrank (ker (fibreJacobian d B A))`.
>
> - **Lean:** `finrank_cotangentSpace_fibre_eq_finrank_ker (d) (B) (A) (hA : mult d A = B) :
>   finrank k (CotangentSpace (Localization.AtPrime (maxIdealAt (fibreGen d B) (canonicalCoord d A) _)))
>   = finrank k (LinearMap.ker (fibreJacobian d B A))`.
> - **Gloss.** The m/m² Zariski cotangent space of the fibre ring localised at `A` = kernel of the
>   Jacobian of the generators. The localised ideal is `maxIdealAt (fibreGen d B) (canonicalCoord d A)`,
>   whose base ideal is `span (range (fibreGen d B)) = fibreGenIdeal d B`.
> - **Proved** unconditionally (verbatim instantiation of `Core.CotangentJacobian`'s headline; the
>   only hypothesis is the rational-point vanishing). **No smoothness, no genericity, no reducedness.**
> - **Cited.** none reproved here beyond the engine's own cotangent = ker lemma (LANDED, this repo).
> - **Deferred.** The rank *value* (`rank = C + δ`, H3b) and the local-dim = tangent-dim step at a
>   generic smooth point (H3c). This card does **not** claim either.

> **Claim 5 (card-rank reading).** `finrank (ker (fibreJacobian d B A)) + rank (fibreJacobianMatrix
> d B A) = card (RepCoord d)`.
>
> - **Lean:** `finrank_ker_add_rank_fibreJacobianMatrix (d) (B) (A)`.
> - **Gloss / proof.** Rank-nullity on the domain `RepCoord d → k`
>   (`LinearMap.finrank_range_add_finrank_ker`) + `finrank(range) = matrix.rank` (`rfl`, since
>   `fibreJacobian = matrix.mulVecLin`).
> - **Proved.** The bookkeeping `finrank(ker) + rank = card`. **Assumed / Cited.** none.
> - **Deferred.** Plugging `rank = C + δ` (H3b) gives `finrank(ker) = card − C − δ`; not done here.

---

**Non-vacuity.** The `(2,2,2)` witness `example` (over `ℚ`): the fibre-Jacobian entry at output
`(0,0)`, variable `⟨0,0,0⟩` equals `1` (a genuinely nonzero entry, exercising
`fibreJacobianMatrix_apply`), so the assembly is non-vacuous.

**Interface H3b/H3c consume.** The object `fibreJacobianMatrix d B A` (entry `=
eval_pderiv_multPoly`) + the two identities: `finrank_cotangentSpace_fibre_eq_finrank_ker`
(tangent = ker) and `finrank_ker_add_rank_fibreJacobianMatrix` (card − rank). H3b supplies
`rank (fibreJacobianMatrix d B A) = C + δ` at a generic `A`; H3c supplies smoothness so the kernel
finrank is the local dimension of the fibre.
