# Thread 12 — general-`r` RLCT payoff (Brick A PROVE + Brick B CITE + R2-general) — statement card

Module: `lean/DLNFibre/DLN/RlctPayoffGeneral.lean` (272 LoC, sorry-free, axiom-clean). Extends the
LANDED corner-`0` `lean/DLNFibre/DLN/RlctPayoff.lean` (thread 10) to a general rank-`r` target `B`.
Build: whole `DLNFibre` library green (`lake build`, 3677 jobs); `scripts/sorries` = 0 sorry / 0 #exit
/ 0 native_decide / 0 axiom (whole library).
Axioms (`#print axioms`): `[propext, Classical.choice, Quot.sound]` on `codimRepCanonical_productRankLocusLE_eq_cCodim`
(Brick A), `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` (R2-general), and both `(2,2,2)` `r=1`
witnesses — both Cited facts (Aoyagi rlct + Lemma 4.6 shift) are carried structure FIELDS
(`RlctInterface.cited_aoyagi_dln` / `BundleShiftInterface.cited_bundle_shift_lemma46`), NOT global axioms.
Pinned commit: see thread-12 commit on `expedition/rlct-payoff`.

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
> - **Lean:** `codimRepCanonical_productRankLocusLE_eq_cCodim` (`[IsAlgClosed k] [CharZero k]`); `ℕ∞`
>   form `…_eq_cCodim_enat`; bridge (a) `codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim`;
>   definitional `…_eq_height_sigmaIdeal`.
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

## Brick B — the bundle shift (CITED, named: LR Lemma 4.6)

> **Claim.** `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` for `B` of rank `r ≤ min d`.
>
> - **Lean:** `BundleShiftInterface` (structure), field `cited_bundle_shift_lemma46`.
> - **Gloss.** `BundleShiftInterface d K ι` carries `cited_bundle_shift_lemma46 : ∀ B r, B.rank = r →
>   (∀ k', r ≤ d k') → codimRepCanonical (fibre K d (B.map ι)) = codimRepCanonical (productRankLocusLE
>   K d r) + ((r * (d 0 + d (Fin.last N) − r) : ℕ) : ℕ∞)`.
> - **Cited.** Lehalleur–Rimányi Lemma 4.6 = `lem:rank_vs_fibers` (main.tex:844–858): `mult⁻¹(B)` is a
>   locally-trivial bundle over the rank-`r` matrix orbit `Mat^{rk=r}` (dim `r(d_0+d_N−r)`), so its
>   codim is that of `Σ̄^r` shifted by the base dimension. A fibre-dimension / locally-trivial-bundle
>   count Mathlib v4.29 lacks (thread 11: four routes, all hit the same wall). The field is a CARRIED
>   hypothesis, NOT a global `axiom` (so `#print axioms` stays clean).
> - **Why separate from `RlctInterface`.** Different source (Lemma 4.6, a geometric bundle statement,
>   vs Aoyagi Thm 1, an analytic rlct statement), so the two Cited dependencies are independently
>   visible in any consumer's type.
> - **Honest-subtraction guard.** the shift is a `ℕ`-cast `((r * (d 0 + d (Fin.last N) − r) : ℕ) : ℕ∞)`;
>   the `∀ k', r ≤ d k'` guard keeps `d 0 + d_N − r` the genuine integer (no `ℕ`-truncation).
> - **`B.rank` over ℝ.** matches `RlctInterface.cited_aoyagi_dln` exactly (a ring embedding preserves
>   matrix rank, so `B.rank = (B.map ι).rank`).

## R2-general — the payoff (transport via BOTH Cited interfaces)

> **Claim.** `rlct(K^DLN_B) = (C + r(d_0+d_N−r))/2` for `B` of rank `r ≤ min d`.
>
> - **Lean:** `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi (I : RlctInterface d K ι)
>   (J : BundleShiftInterface d K ι) (hB : B.rank = r) (hr : ∀ k', r ≤ d k') (h) :
>   I.rlct (lossDLN d B) = (((cCodim d r h).toNat : ℝ) + (r * (d 0 + d (Fin.last N) − r) : ℕ)) / 2`.
> - **Proved.** Pure transport: `I.cited_aoyagi_dln B r hB` (general in `r`, LANDED) gives `rlct =
>   ½·codim mult⁻¹(B.map ι)`; `J.cited_bundle_shift_lemma46 B r hB hr` rewrites the fibre codim as
>   `codim Σ̄^r + shift`; Brick A (`…_eq_cCodim_enat`) rewrites `codim Σ̄^r = cCodim d r`; the
>   `ℕ∞.toNat`-of-sum splits because both summands are finite (Brick A finite; shift a `ℕ` literal).
>   The Aoyagi guard `r ≤ univ.inf' d` is `∀ k, r ≤ d k` via `Finset.le_inf'_iff`.
> - **Assumed.** both interfaces `I`, `J` (explicit hypotheses; both Cited dependencies in the type);
>   `[IsAlgClosed K] [CharZero K]`; `(kostantPartitions d r).Nonempty`; `B.rank = r`; `∀ k', r ≤ d k'`.
> - **Cited.** `I.cited_aoyagi_dln` (Aoyagi Thm 1 / LR Thm 8.6) AND `J.cited_bundle_shift_lemma46`
>   (LR Lemma 4.6). Both carried fields, not global axioms.
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

## Status

sorry-free; awaiting reviewer fidelity AUDIT (name=content; Brick A proved; Aoyagi + Lemma 4.6 both
honestly Cited as named carried interfaces; Brick A uses only weak monotonicity).
