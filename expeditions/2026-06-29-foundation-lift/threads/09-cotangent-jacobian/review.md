# Decorrelated review — P3-R1 `CotangentJacobian` re-home (cokernel–finrank bridge)

**Reviewer:** independent (read-only, no full build). **Target HEAD:** `12d25fca`,
branch `expedition/foundation-lift-p3`, worktree `…/worktrees/foundation-lift`.
**Files audited:**
- `lean/DLNFibre/Core/RingTheory/MvPolynomial/CotangentJacobian.lean`
- `lean/DLNFibre/Core/RingTheory/Ideal/CotangentLocalization.lean`

## Verdict

| Item | Verdict |
|---|---|
| (1) Cokernel–finrank bridge + B2 transpose orientation | **PASS** |
| (2) Headline name = content (no smoothness, arbitrary rational point) | **PASS** |
| (3) Faithful re-home + `[Field k]→[CommRing k]` weakening + clean split | **PASS** |
| **Overall** | **PASS — no blocking findings.** |

---

## (1) The transpose orientation — re-derived from scratch (PASS)

I re-derived the orientation independently before reading the Codex artefact, checking
every Mathlib lemma the proof leans on against the v4.29 source.

**Mathlib semantics confirmed (not taken on trust):**
- `Matrix.mulVecLin_apply` (`…/Matrix/ToLin.lean:290`): `(M.mulVecLin v) i = ∑ j, M i j * v j`
  (row-by-vector). So `jacobian = J.mulVecLin : (σ→k) →ₗ (ι→k)` has `(J v)_i = ∑_x J_{i,x} v_x
  = ∇g_i(a)·v`, and `ker J = {v : ∇g_i(a)·v = 0 ∀i}` is the Zariski **tangent** space, dim
  `card σ − rank`.
- `jacobianTranspose = Jᵀ.mulVecLin : (ι→k) →ₗ (σ→k)`; `(Jᵀ c)_x = ∑_i J_{i,x} c_i`
  (`jacobianTranspose_apply`, lines 81–84). Hence `Jᵀ(Pi.single i 1)_x = J_{i,x} =
  (∂g_i/∂x)(a)` — **the i-th gradient row, indexed by variables `σ`**. The columns of `Jᵀ`
  are the gradient rows of `g`, living in `σ→k`.
- `mvPolynomialBasis_repr_apply` (`…/Kaehler/Polynomial.lean:80`): `(mvPolynomialBasis k σ).repr
  (D p) i = pderiv i p`, **indexed by the variable `i ∈ σ`**. So `Ψ = ((basis.baseChange A).baseChange
  k).equivFun` produces a `σ→k` vector. The `ext x` with `x : σ` (line 279) pins the index type
  to `σ` — a wrong-orientation `Ψ` landing in `ι→k` would not typecheck here.

**B2 (`finrank_tensor_kaehler_eq_coker`).** I traced `Ψ_D` (273–284) and `hPsi_i` (339–347)
fully: `Ψ(1 ⊗ (1 ⊗ D(g i)))_x = evalAug(algebraMap (pderiv x (g i)))`; via `evalAug_mk` +
`aeval_def`/`eval₂_id` (base structure-map is `RingHom.id k`, confirmed `…/MvPolynomial/Eval.lean:305,602`)
this is `eval a (pderiv x (g i))`. The `Finset.sum_eq_single i` (line 346) collapses
`jacobianTranspose_apply`'s sum to exactly that. So `Ψ(conormal generator i) = Jᵀ(eᵢ)` and `Ψ`
carries `span{conormal generators}` onto `range Jᵀ`, giving `k ⊗_A Ω[A/k] ≅ (σ→k)/range Jᵀ =
coker Jᵀ`. Cotangent lives in `σ→k` (dim `card σ − rank`), **not** `ι→k`. Orientation correct.

**B1 (`finrank_ker_jacobian_eq_finrank_coker`).** Both rank-nullity instances confirmed against
Mathlib: `finrank_range_add_finrank_ker J` gives `rank J + finrank(ker J) = card σ` (domain
`σ→k`); `finrank_quotient_add_finrank (range Jᵀ)` gives `finrank(coker Jᵀ) + rank Jᵀ = card σ`
(codomain `σ→k`). `Matrix.rank = finrank(range mulVecLin)` is `rfl` (`…/Matrix/Rank.lean:121`),
so `finrank_range_jacobian_eq` (87–92) is sound, and `Matrix.rank_transpose` requires `[Field R]`
— present. `omega` closes (both `= card σ − rank`). The two `finrank_pi` collapses are correct.

**Decorrelated worked examples (mine, exact via sympy).** The Codex example `g₁=x+2y, g₂=3x+6y`
is **square** (2 gens, 2 vars): there `dim coker Jᵀ = #vars−rank` and `dim coker J = #gen−rank`
**coincide**, so it cannot detect a transpose error. I added **rectangular** cases that do:

| Generators / vars | rank | `dim ker J = coker Jᵀ` (#vars−r) | wrong `coker J` (#gen−r) | geometric tangent |
|---|---|---|---|---|
| `x, 2x, 3x` (3 gen, 2 var) | 1 | **1** | 2 | line `x=0`: 1 ✓ |
| `x²−y` (1 gen, 2 var, smooth) | 1 | **1** | 0 | curve: 1 ✓ |
| `x+y+z` (1 gen, 3 var) | 1 | **2** | 0 | plane: 2 ✓ |
| `x²−y²` (1 gen, 2 var, **node, singular**) | 0 | **2** | 1 | whole plane: 2 ✓ |

In every rectangular case the headline (`#vars − rank`) matches the geometric tangent dimension
and **differs from the wrong orientation** — confirming the transpose is on the correct side, not
a square-coincidence artefact. The node case is the non-smooth point the headline explicitly
claims to handle, and it comes out right.

## (2) Headline name = content (PASS)

`finrank_cotangentSpace_eq_finrank_ker_jacobian` (386–392): sole hypothesis `hg : ∀ i, eval a
(g i) = 0` (point on `V(I)`); section vars `[Field k] [Fintype σ/ι] [DecidableEq σ/ι]`. **No
smoothness, no genericity, arbitrary `k`-rational `a`.** Statement is exactly `finrank(CotangentSpace
(Localization.AtPrime m_A)) = finrank(ker(jacobian g a))`. The name says "cotangent space =
Jacobian kernel" — content matches with no overclaim (it does **not** assert `½·codim`, smoothness,
or any analytic interface). `[Field k]` is genuinely load-bearing here (`Matrix.rank_transpose`,
residue field `κ(m_A)=k`). Minimal-hyp claims in the card are accurate.

## (3) Faithful re-home + `[CommRing k]` weakening + split (PASS)

- **Old file deleted**, both new modules imported at the **end** of `DLNFibre.lean` (505–506),
  single-writer respected. No stale `Core.CotangentJacobian` path, no old `aug`/`aug_mk`/
  `aug_surjective` anywhere (only `evalAug`).
- **Consumers re-pointed:** `FibreJacobian.lean` → MvPolynomial half; `OrbitTangentCotangent.lean`
  → Ideal half with the call qualified `Ideal.finrank_cotangentSpace_localization_eq_cotangent`
  (line 644).
- **Split is clean.** The `Ideal` half imports **no** MvPolynomial / Kaehler / DLN module and its
  body references none — genuinely network-free, needs only `[CommRing A] + p.IsMaximal`. Its sole
  consumer (`normalFormIdeal M`, a non-polynomial quotient) justifies the separate home.
- **`[Field k]→[CommRing k]` weakening is sound.** The localization proof
  (`CotangentLocalization.lean:122–132`) uses only `restrictScalars k` of `T`/`A`-linear equivs +
  `LinearEquiv.finrank_eq` (the general CommRing-base `finrank` transport, `…/Dimension/Constructions.lean:295`);
  no field-specific step. `tensorCotangentEquiv` needs `Module.Flat R T` (supplied by localization
  flatness) and `map_eq_maximalIdeal` involves no `k` — consistent with the three support decls
  dropping `k` entirely.

## Notes (non-blocking)

- The card's "bridge proofs moved verbatim" is a *faithfulness* convenience; git records the
  re-home as a rename-with-split so a line-by-line verbatim diff isn't directly extractable, but
  this is immaterial to soundness — I verified the **mathematical content** of B1/B2/the transport
  directly, which is the load-bearing guarantee. No action needed.
- Inherited `unusedSectionVars`/`unusedDecidableInType`/`unusedFintypeInType` info-lints persist
  (shared-section-variable design), as disclosed. Note-level; a follow-up could tighten section
  variables. Not blocking.

## Bottom line

The flagged risk — that a wrong transpose orientation could give a wrong dimension that still
typechecks — is **closed**. The orientation is `coker Jᵀ` in `σ→k`, dim `card σ − rank`, the
geometrically correct Zariski cotangent/tangent dimension; my rectangular worked examples (which
the square Codex example could not) separate it from the wrong `coker J`. Headline name = content,
no smoothness assumed. Re-home faithful, split clean, `[CommRing k]` weakening sound. **No
blocking-the-PR findings.**
