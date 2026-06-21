# Thread 12 — general-`r` RLCT payoff (Brick A PROVE + Brick B CITE + R2-general) — statement card

Module: `lean/DLNFibre/DLN/RlctPayoffGeneral.lean` (272 LoC, sorry-free, axiom-clean). Extends the
LANDED corner-`0` `lean/DLNFibre/DLN/RlctPayoff.lean` (thread 10) to a general rank-`r` target `B`.
Build: whole `DLNFibre` library green (`lake build`, 3677 jobs); `scripts/sorries` = 0 sorry / 0 #exit
/ 0 native_decide / 0 axiom (whole library).
Axioms (`#print axioms`): `[propext, Classical.choice, Quot.sound]` on `codimRepCanonical_productRankLocusLE_eq_cCodim`
(Brick A), `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` (R2-general), and both `(2,2,2)` `r=1`
witnesses — both Cited facts (Aoyagi rlct + the Lemma 4.5/4.6 shift) are carried structure FIELDS
(`RlctInterface.cited_aoyagi_dln` / `BundleShiftInterface.cited_bundle_shift`, both guarded `0 < N`),
NOT global axioms.
Pinned commit: see thread-12 commit on `expedition/rlct-payoff`. **Update (PR #5 review, commit 7a52633):**
Brick A moved to the network-free Core module `lean/DLNFibre/Core/SigmaCodim.lean` (no `DLN` import); the
two Cited fields gained a `0 < N` guard (false at `N = 0`, the empty product); `cited_bundle_shift_lemma46`
renamed → `cited_bundle_shift` and restated as the combined LR Lemma 4.5 + Lemma 4.6 (see Brick B).

## The destination, plainly

The paper's RLCT payoff at a general rank-`r` target `B`: the square-Frobenius DLN loss `K^DLN_B` has
real log-canonical threshold `(C + r(d_0+d_N−r))/2`, where `C = cCodim d r` is the combinatorial
codimension and the `+ r(d_0+d_N−r)` is the bundle shift of Lehalleur–Rimányi Lemma 4.6. Two bricks of
**different status**: Brick A (`codim Σ̄^r = C`) is PROVED zero-cited; Brick B (the `Σ̄^r ⤳ mult⁻¹(B)`
shift) is CITED to Lemma 4.6 (the fibre-dimension wall, thread 11). The honest headline is **PROVE
Brick A + CITE Brick B**, NOT a single proved `codim mult⁻¹(B) = C + shift`.

## Brick A — `codim Σ̄^r = C` (PROVED, zero-cited, general in `r`)

> **Claim.** The geometric codimension of the closed rank-`≤ r` product locus `Σ̄^r =
> productRankLocusLE d r` equals the combinatorial `C = cCodim d r`.
>
> - **Lean:** `Core.codimRepCanonical_productRankLocusLE_eq_cCodim` (now in the network-free Core module
>   `lean/DLNFibre/Core/SigmaCodim.lean`, `[IsAlgClosed k] [CharZero k]`); `ℕ∞` form `…_eq_cCodim_enat`;
>   bridge (a) `codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim`; definitional
>   `…_eq_height_sigmaIdeal`.
> - **Gloss.** `((codimRepCanonical (productRankLocusLE k d r)).toNat : ℤ) = cCodim d r h`.
> - **Proved.** Mirrors the LANDED `r = 0` chain (`codimRepCanonical_fibre_zero_eq_cCodim`), but stated
>   *about `Σ̄^r` itself* — every brick is general in `r`. `codim Σ̄^r = height (sigmaIdeal d r)` (rfl)
>   `= ⨅` orbit-codim over corner-`≤ r` orbits (`minimalPrimes_sigmaIdeal_eq` + `sigmaIdeal = sInf
>   orbitIdeals`, **general in `r`**, LANDED `Core.SigmaComponents`) `= cCodim d r`. Lower bound: the
>   per-orbit `cCodim_le_codimRepCanonical_of` fed with the LANDED **weak** monotonicity
>   `Core.CCodimZeroMono.cCodim_zero_mono`. Upper bound: the realizer (`realizerD`) of a minimising
>   Kostant partition attains `cCodim`.
> - **WEAK monotonicity only.** `cCodim_le_codimRepCanonical_of` takes only the weak `hMono`
>   (`e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`, the `≤` form — `CCodimCornerMono.lean:296`), NOT the open
>   strict `hMonoStrict`. So **Brick A is INDEPENDENT of the θ-strict gap** (the one remaining open
>   `cCodim_zero_strict`). Confirmed: no `hMonoStrict` / `cCodim_corner_strict` / `cCodim_zero_strict` /
>   `exists_kostantPartition` anywhere in the proof chain.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]` (the Voigt-discharge scope where `cCodim` is the
>   geometric codimension); `(kostantPartitions d r).Nonempty`.
> - **Cited / Deferred.** none — Brick A is the genuinely-new general-`r` geometric content, proved.
> - **No fibre-dim wall.** `Σ̄^r` is `GL_d`-stable (a finite union of orbit closures), so the landed
>   orbit-closure machinery applies directly. The wall is only Brick B's `Σ̄^r ⤳ mult⁻¹(B)`.

## Brick B — the bundle shift (CITED, named: LR Lemma 4.5 + Lemma 4.6)

> **Claim.** `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` for `B` of *exact* rank `r ≤ min d`, `0 < N`.
>
> - **Lean:** `BundleShiftInterface` (structure), field `cited_bundle_shift`.
> - **Gloss.** `BundleShiftInterface d K ι` carries `cited_bundle_shift : ∀ B r, 0 < N → B.rank = r →
>   (∀ k', r ≤ d k') → codimRepCanonical (fibre K d (B.map ι)) = codimRepCanonical (productRankLocusLE
>   K d r) + ((r * (d 0 + d (Fin.last N) − r) : ℕ) : ℕ∞)`.
> - **Cited.** The *closed-locus* shift combines two LR §4 facts: Lemma 4.6 = `lem:rank_vs_fibers`
>   (main.tex:844–858) gives `codim mult⁻¹(B) = codim Σ^r + r(d_0+d_N−r)` for the *exact-rank* `Σ^r`
>   (`mult⁻¹(B)` is a locally-trivial bundle over the rank-`r` matrix orbit `Mat^{rk=r}`, dim
>   `r(d_0+d_N−r)`); Cor 4.4 (`cor:irred_comp`) + Lemma 4.5 (`lem:rank_0`, main.tex:816–833) give
>   `codim Σ̄^r = codim Σ^r` (Zariski closure preserves codimension), so the field's `Σ̄^r` form is
>   honest. A fibre-dimension / locally-trivial-bundle count Mathlib v4.29 lacks (thread 11: four routes,
>   all hit the same wall). The field is a CARRIED hypothesis, NOT a global `axiom` (so `#print axioms`
>   stays clean).
> - **`0 < N` guard.** restricts the field to a genuine deep network — where Lemma 4.6 holds. At `N = 0`
>   the "product" `mult` is the empty product (`mult = 1`) and the shift identity is false.
> - **Why separate from `RlctInterface`.** Different source (the Lemma 4.5/4.6 geometric bundle
>   statement, vs Aoyagi Thm 1, an analytic rlct statement), so the two Cited dependencies are
>   independently visible in any consumer's type.
> - **Honest-subtraction guard.** the shift is a `ℕ`-cast `((r * (d 0 + d (Fin.last N) − r) : ℕ) : ℕ∞)`;
>   the `∀ k', r ≤ d k'` guard keeps `d 0 + d_N − r` the genuine integer (no `ℕ`-truncation).
> - **`B.rank` over ℝ.** matches `RlctInterface.cited_aoyagi_dln` exactly (a ring embedding preserves
>   matrix rank, so `B.rank = (B.map ι).rank`).

## R2-general — the payoff (transport via BOTH Cited interfaces)

> **Claim.** `rlct(K^DLN_B) = (C + r(d_0+d_N−r))/2` for `B` of rank `r ≤ min d`.
>
> - **Lean:** `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi (I : RlctInterface d K ι)
>   (J : BundleShiftInterface d K ι) (hN : 0 < N) (hB : B.rank = r) (hr : ∀ k', r ≤ d k') (h) :
>   I.rlct (lossDLN d B) = (((cCodim d r h).toNat : ℝ) + (r * (d 0 + d (Fin.last N) − r) : ℕ)) / 2`.
> - **Proved.** Pure transport: `I.cited_aoyagi_dln B r hN hB` (general in `r`, LANDED) gives `rlct =
>   ½·codim mult⁻¹(B.map ι)`; `J.cited_bundle_shift B r hN hB hr` rewrites the fibre codim as
>   `codim Σ̄^r + shift`; Brick A (`…_eq_cCodim_enat`) rewrites `codim Σ̄^r = cCodim d r`; the
>   `ℕ∞.toNat`-of-sum splits because both summands are finite (Brick A finite; shift a `ℕ` literal).
>   The Aoyagi guard `r ≤ univ.inf' d` is `∀ k, r ≤ d k` via `Finset.le_inf'_iff`.
> - **Assumed.** both interfaces `I`, `J` (explicit hypotheses; both Cited dependencies in the type);
>   `0 < N` (the Cited scope, a genuine deep network); `[IsAlgClosed K] [CharZero K]`;
>   `(kostantPartitions d r).Nonempty`; `B.rank = r`; `∀ k', r ≤ d k'`.
> - **Cited.** `I.cited_aoyagi_dln` (Aoyagi Thm 1 / LR Thm 8.6) AND `J.cited_bundle_shift`
>   (LR Lemma 4.5 + Lemma 4.6). Both carried fields, not global axioms.
> - **Name = content.** both `I` and `J` explicit in the type (both Cited dependencies visible);
>   `via_aoyagi` names the rlct source; the `+ shift` is visibly the Lemma-4.6 contribution, NOT claimed
>   as proved geometry. NO unconditional `rlct = (C + shift)/2`. `θ` is absent (R is `C/2` + shift only).

## (2,2,2) `r = 1` non-vacuity

> - `codimRepCanonical_productRankLocusLE_d222_one : (codimRepCanonical (productRankLocusLE
>   (AlgebraicClosure ℚ) d222 1)).toNat = 1` — the geometric reading of the LANDED `cCodim d222 1 = 1`
>   (`Core.CTheta.cCodim_d222_one`), via Brick A.
> - `rlct_lossDLN_d222_one_eq_two_via_aoyagi (I : RlctInterface d222 ℂ Complex.ofRealHom)
>   (J : BundleShiftInterface d222 ℂ Complex.ofRealHom) (hB : B.rank = 1) : I.rlct (lossDLN d222 B) = 2`
>   — `C = 1`, shift `1·(2+2−1) = 3`, so `rlct = (1+3)/2 = 2` (the predicted fibre codim is `4`,
>   independently confirmed by direct Jacobian rank in thread 11). Codim over `AlgebraicClosure ℚ`, rlct
>   over `ℂ` (which carries `ℝ →+* ℂ`), as the LANDED `r = 0` `(2,2,2)` witness does.

## Paper-notation note (recorded by the reviewer; no Lean change)

The paper's *printed* set-builder for `\overline{Σ}^r` (main.tex:758) reads `{rk mult ≥ r}`, but the
Lean `productRankLocusLE d r` (the docstring's `Σ̄^r`) is `{rk mult ≤ r}`. The printed `≥` is a paper
typo: the paper's *operative* definition — its orbit stratification `\overline{Σ}^r = ⊔_{m∈M^{≤r}}
O_m` (main.tex:793), the `M^{≤r}`/`R^{≤r}` index sets, the "determinantal variety" remark, and
"closure of `Σ^r`" (Cor 4.4) — all use rank `≤ r` (sanity: literal `≥ r` gives `Σ̄^0 = Rep`, codim 0,
contradicting `codim Σ̄^0 = C > 0`). The Lean `{rk ≤ r}` is faithful to the paper's intended object;
flagged only so a reader comparing against main.tex:758 is not misled.

## Status

sorry-free + **reviewed** (fidelity AUDIT gate passed, commit `933e424`). Reviewer verdict: FIDELITY
OK on all four checks — (1) Brick A genuinely PROVED zero-cited (`#print axioms` clean, only LANDED
Core machinery); (2) Brick A uses ONLY weak monotonicity (`cCodim_le_codimRepCanonical_of` +
`cCodim_zero_mono`; no `hMonoStrict`/strict leak — independent of the open θ-strict gap); (3) both
Cited facts honestly carried named interfaces (Aoyagi `cited_aoyagi_dln`; Lemma 4.6
`cited_bundle_shift_lemma46`, a SEPARATE structure, not folded into `RlctInterface`, not a global
`axiom`); (4) R2-general name=content (both `I`, `J` explicit in the type; `via_aoyagi`; no
unconditional `rlct = (C+shift)/2`). Decorrelated Codex (xhigh) convergent: no hidden fibre-dimension
content in Brick A, shift faithful to Lemma 4.6. Codex artefacts: `codex/fidelity-{prompt,answer}.md`.

**PR #5 review update (commit `7a52633`, fidelity re-audited PASS).** Three points above are superseded:
(i) the Lemma-4.6 field is renamed `cited_bundle_shift_lemma46 → cited_bundle_shift` and restated as the
combined LR Lemma 4.5 + Lemma 4.6 (the closed-locus form folds in `codim Σ̄^r = codim Σ^r`); (ii) Brick A
now lives in the network-free Core module `Core.SigmaCodim` (no `DLN` import); (iii) the "open θ-strict
gap" is closed — `Core.CCodimZeroStrict.cCodim_zero_strict` is proved, the θ-count headline
`numTop_eq_ncard_topComponents` is unconditional. Brick A still uses only the weak monotonicity (its
independence from the strict version is unaffected). Both Cited fields gained a `0 < N` scope guard.
