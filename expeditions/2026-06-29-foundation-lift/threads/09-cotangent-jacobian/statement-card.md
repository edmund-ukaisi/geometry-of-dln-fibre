# Statement card — P3-R1: Zariski cotangent = Jacobian kernel (re-home of `CotangentJacobian`)

**Rung:** P3-R1 (Phase 3, the cotangent crux). **Branch:** `expedition/foundation-lift-p3`.
**Source:** `lean/DLNFibre/Core/CotangentJacobian.lean` (deleted; fully re-homed).

## New homes + namespaces (the re-home was a 2-module split)

The source split cleanly along its two distinct Mathlib homes, matched to its two distinct consumers:

| New module | Namespace | Mathlib mirror | Content |
|---|---|---|---|
| `Core/RingTheory/Ideal/CotangentLocalization.lean` | `Ideal` | `Mathlib.RingTheory.Ideal.Cotangent` / `…CotangentBaseChange` | localize-the-cotangent-space comparison (general `k`-algebra `A`, maximal `p`) |
| `Core/RingTheory/MvPolynomial/CotangentJacobian.lean` | `MvPolynomial` | `Mathlib.RingTheory.Kaehler.Polynomial` / `…Smooth.StandardSmoothCotangent` | the point-Jacobian + the headline |

**Why split (justification).** The `Localization` section is genuinely network-free and
MvPolynomial-free — it only needs `[CommRing A]` + `p.IsMaximal`, and its sole consumer
(`OrbitTangentCotangent`, applied to `normalFormIdeal M : Ideal (orbitRing M)`) is a non-polynomial
quotient ring. The Jacobian half is MvPolynomial-specific and depends on the `Ideal` half. The split
gives two clean extraction targets with minimal imports (the `Ideal` half drops all of Kähler/MvPoly),
mirroring the P1 R4-core / R5-transport pattern. The `MvPolynomial` half imports the `Ideal` half.

## Cotangent-dim headline — exact signature + minimal hyps

`MvPolynomial.finrank_cotangentSpace_eq_finrank_ker_jacobian`:

    variable {k : Type*} [Field k] {σ : Type*} [Fintype σ] [DecidableEq σ]
      {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → MvPolynomial σ k) (a : σ → k)

    theorem finrank_cotangentSpace_eq_finrank_ker_jacobian
        (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
        finrank k (CotangentSpace (Localization.AtPrime (maxIdealAt g a hg)))
          = finrank k (LinearMap.ker (jacobian g a))

where `jacobian g a : (σ → k) →ₗ[k] (ι → k) := (jacobianMatrix g a).mulVecLin`, and
`jacobianMatrix g a i x = eval a (pderiv x (g i))` (rows = generators `ι`, cols = variables `σ`).
**No smoothness / genericity hypothesis** — holds at an arbitrary `k`-rational point `a` of
`V(span (range g))`. This is strictly more general than Mathlib's smooth/square submersive Jacobian
(which yields a scalar det with `#relations = #vars`).

Minimal hyps **confirmed** (matches source): `[Field k]` (the Jacobian is `k`-linear; the residue
field `κ(m_A) = k` from `a` rational); `[Fintype σ] [Fintype ι]` (`mulVecLin` / `finrank_pi` /
`mvPolynomialBasis` over a `Fintype`); `[DecidableEq σ] [DecidableEq ι]` (carried by the section,
not load-bearing in every lemma — the inherited `unused{SectionVars,Decidable,Fintype}InType` info
lints are present identically to the source). `Finite` would not suffice as-stated:
`finrank`/`mulVecLin` use `Fintype`.

## THE CRUX — the cokernel–finrank bridge (decorrelated-review target)

Two statements carry the index/transpose bookkeeping. **Review exactly these.**

**(B1) `MvPolynomial.finrank_ker_jacobian_eq_finrank_coker`** (pure rank-nullity):

    theorem finrank_ker_jacobian_eq_finrank_coker :
        finrank k (LinearMap.ker (jacobian g a))
          = finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a))

Proof: rank-nullity on `J` gives `rank(range J) + finrank(ker J) = card σ` (card of the **domain**
`σ→k`); rank-nullity on the quotient gives `finrank(coker Jᵀ) + rank(range Jᵀ) = card σ` (card of
`σ→k`, the **codomain** of `Jᵀ`); `finrank(range J) = finrank(range Jᵀ)` via `Matrix.rank_transpose`;
`omega`. Both sides `= card σ − rank J`.

**(B2) `MvPolynomial.finrank_tensor_kaehler_eq_coker`** (the geometric half — where a transpose error
would hide):

    finrank k (k ⊗[A] Ω[A⁄k]) = finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a))

The coordinate iso `Ψ : k ⊗[A] (A ⊗[R] Ω[R⁄k]) ≃ₗ[k] (σ → k)` (`Ψ_D`) sends the base-changed conormal
generator `1 ⊗ (1 ⊗ D(g i))` to the gradient row `x ↦ ε(pderiv x (g i)) = (eval a (pderiv x (g i)))_x`
**indexed by variables `σ`**, which `hPsi_i` identifies with `jacobianTranspose g a (Pi.single i 1)`
— a **column of `Jᵀ`** = the `i`-th gradient row of `g`. So `Ψ` carries `span{conormal generators}`
onto `range (jacobianTranspose)`, giving `k ⊗[A] Ω[A⁄k] ≅ (σ→k) ⧸ range Jᵀ`. The transpose is
load-bearing: the cotangent space is `coker Jᵀ` (lives in `σ→k`, dim `card σ − rank`), **not**
`coker J` (lives in `ι→k`, the wrong space/dimension).

**Faithfulness:** the bridge proof bodies (`finrank_ker_jacobian_eq_finrank_coker`,
`finrank_tensor_kaehler_eq_coker`, including the `Ψ_D`/`hRange`/`hPsi_i` transport) were moved
**verbatim**; only the augmentation name `aug → evalAug` and the cross-module reference
`finrank_cotangentSpace_localization_eq_cotangent → Ideal.…` changed (plus one `show → change` for the
style linter, semantically identical). Compiles unchanged.

**Decorrelated review (Codex, xhigh):** all three checks SOUND. Worked example
`g₁ = x+2y, g₂ = 3x+6y` at `(0,0)` — a **rank-deficient** (genuinely non-smooth, rank 1 not 2) point:
`J = [[1,2],[3,6]]`, `dim ker J = 1`, `range Jᵀ = span{(1,2)}`, `dim coker Jᵀ = 1`, matching the
geometric tangent dim of the line `x+2y=0`. Confirms transpose bookkeeping and the `#vars − rank`
reading. Prompt+answer: `codex/bridge-{prompt,answer}.md`.

## Localization lemma (the `Ideal` half) — minimal hyps

`Ideal.finrank_cotangentSpace_localization_eq_cotangent`
`{A} [CommRing A] (p : Ideal A) [p.IsMaximal] {k} [CommRing k] [Algebra k A]`:

    finrank k (CotangentSpace (Localization.AtPrime p)) = finrank k (p.Cotangent)

**Minimal-hyp weakening (bonus over source):** the source carried `[Field k]`; it is **unused** here
(the maps are `k`-linear equivs, so the `finrank`s agree over any base `[CommRing k]`). The three
supporting decls (`cotangent_isLocalizedModule_id`, `cotangentLocalizationTensorEquiv`,
`cotangentTensorRidEquiv`) need **no `k` at all** — only `[CommRing A]` + `p.IsMaximal` — so `k` is
dropped from their scope. Faithful otherwise (verbatim bodies).

## Sibling-clash gate (pre-flight, cleared)

`rg` over `.lake/packages/mathlib` for every new top-level name: all `NONE` except `aug` (a local
field in `Matroid.IndepAxioms`) — and `aug` was **renamed to `evalAug`** anyway (too terse for
Mathlib-grade; zero external consumers). No clash on `jacobianMatrix`, `jacobian`,
`jacobianTranspose`, `maxIdealAt`, `evalAug`, the headline, the bridge lemmas,
`Ideal.finrank_cotangentSpace_localization_eq_cotangent`, `cotangent_isLocalizedModule_id`,
`cotangentLocalizationTensorEquiv`, `cotangentTensorRidEquiv`. Project-local: no clash.

## Re-pointed

- `Core/FibreJacobian.lean` — import → `…RingTheory.MvPolynomial.CotangentJacobian`; unqualified
  `jacobianMatrix`/`jacobian`/`maxIdealAt`/headline resolve via its existing `open MvPolynomial`;
  3 docstring refs `Core.CotangentJacobian.* → MvPolynomial.*`.
- `Core/OrbitTangentCotangent.lean` — import → `…RingTheory.Ideal.CotangentLocalization`; the one call
  qualified to `Ideal.finrank_cotangentSpace_localization_eq_cotangent`.
- `DLNFibre.lean` — removed stale mid-list `import …CotangentJacobian`; added the 2 new modules at the
  end with an explanatory comment.
- L2 sweep: no stale `DLNFibre.Core.CotangentJacobian` path, no old `aug`/`aug_mk`/`aug_surjective`,
  no unqualified `finrank_cotangentSpace_localization_eq_cotangent` anywhere. (`FibreSmoothPlumbing`'s
  `.jacobian` is the unrelated `PreSubmersivePresentation.jacobian` field — not our `jacobian`.)

## Status

- **Build:** `./scripts/lb DLNFibre` green — **3821 jobs** (= prior 3820 − 1 old + 2 new modules).
- **Sorries:** `scripts/sorries` clean — 0 sorry / 0 #exit / 0 native_decide / 0 axiom.
- **Axioms:** `#print axioms` = `[propext, Classical.choice, Quot.sound]` on the headline
  (`MvPolynomial.finrank_cotangentSpace_eq_finrank_ker_jacobian`), both bridge lemmas (B1, B2), and
  the localization lemma. No DLN payoff axioms touched.
- **L4 (longLine):** all new-file longLines reflowed to ≤100 codepoints; `show`→`change` and the
  `maxHeartbeats`-comment style lints cleared.

## Holes / surprises (honesty)

- **None on the math.** Name = content throughout; the headline says exactly `cotangent dim = ker
  Jacobian dim` and proves that (no overclaim of smoothness/codim).
- **Inherited info-lints kept (faithful, not new):** `unusedSectionVars` / `unusedDecidableInType` /
  `unusedFintypeInType` / one `unusedSimpArgs` (`Matrix.mulVecLin_apply` in `jacobian_apply`) fire on
  the early lemmas — identically to the source (the shared-section-variable design). These are
  `Note`-level/disableable and were tolerated in the source; left as-is to preserve crux-proof
  faithfulness rather than scatter `omit` clauses. A follow-up could tighten the section variables.
- **Decorrelated-review flag (full disclosure):** the one place I cannot personally certify beyond the
  Codex worked-example + verbatim-move evidence is the `Ψ`/`Ψ_D`/`hPsi_i` orientation in B2 — that the
  conormal generator lands variable-indexed (`σ→k`) and equals `Jᵀ(eᵢ)` rather than a generator-indexed
  vector. The Lean `Ψ_D` lemma pins it to `σ→k` and `hPsi_i` proves the `= jacobianTranspose (Pi.single
  i 1)` identity, and Codex independently confirmed the orientation, but **this is the exact bookkeeping
  the decorrelated reviewer should re-derive.**
