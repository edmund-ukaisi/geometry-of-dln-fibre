# Statement card — CThetaValue: the Thm 7.10 closed forms for `C` and `θ`

Module `lean/DLNFibre/Core/CThetaValue.lean` (new file, imports `Core.CThetaDropM`, transitively
`Core.CThetaExplicit`). Lehalleur–Rimányi Thm 7.10 (`r = 0`): the QIP minimum and minimiser-count in
closed form. Import appended to `DLNFibre.lean` (single-writer). Sorry-free, axiom-clean
(`propext, Classical.choice, Quot.sound`). Commit `d72f199`.

**Scope (name = content).** This file proves two things about the **QIP** (`Gqip`/`qipMin` of
`Core.CThetaQIP`) for `Monotone d`: (i) `qipMin d = cValue d`, the explicit `C` closed form; (ii) the
number of `Gqip`-minimisers equals `cTheta d = C(m, |δ|)`, the explicit `θ`. It does **not** touch
`cCodim`/`numTop` (the Kostant-side `C`/`θ` of `Core.CTheta`); the C-side bridge to those is the
upstream `cCodim_eq_qipMin`, and **there is no θ-side bridge `numTop d 0 = qipNumMinimisers` yet**. No
geometric (Voigt) content; `cValue`/`cTheta` are functions of a ℤ-objective's optimum/optimiser-count,
nothing more.

**Notation.** `m = qipM d`, `S = qipS d = ∑_{i=0}^m d_i`, `a = qipRound d = (2S+m)/(2m)` (Int div),
`δ = qipDelta d = S − m·a`, `qipLow d = {i : Fin N | (i:ℕ) < m}` (card `m`), `qipT d e i = e_i +
d_{i+1} − a` (`= (e_i − s_i) − (a − d_0)`, `s = qipShift`).

---

> **Claim (C closed form, Thm 7.10 `r=0`).** For `Monotone d`, `qipMin d = cValue d`, where
> `cValue d = ½(d_0² − ∑_{i=1}^m (d_i − d_0)² + m(a − d_0)² + 2(a − d_0)δ + |δ|)`.
>
> - **Lean:** `qipMin_eq_cValue (d) (hd : Monotone d) (hne : (qipFeasible d).Nonempty) :`
>   `qipMin d hne = cValue d`.
> - **Gloss / proof.** `N=0`: feasibility forces `d_0=0`, both sides `0`. `N≥1`: antisymmetry. `≤`:
>   the rounded witness `qipWitness` (m-face: `e_i = (a + r_i − d_{i+1}).toNat`, `r = qipRoundT` the
>   `[i<|δ|]·sgn δ` indicator) is feasible (`qipWitness_feasible`) and attains `cValue`
>   (`cValue_eq_Gqip_witness`, the numerator `= 2·G(eW)` via `Phi_on_mface` + the `G↔Φ` transfer
>   `two_Gqip_eq_Phi_add` + `∑ r² = |δ|`). `≥`: any `Gqip`-minimiser is a `Φ`-minimiser, drops to the
>   m-face (`qip_minimiser_support_le_m`), and `∑_{qipLow}(qipT)² ≥ |δ|` (`abs_sum_le_sumSq`) gives
>   `G ≥ cValue` (`cValue_le_Gqip_of_min`). In-face nonnegativity of the witness bracket needs the
>   within-prefix bound `m·d_i ≤ S` (`qip_within_prefix`) + branch-sensitive rounding (`qip_d_le_round`
>   for `δ≥0`, `qip_d_le_round_sub_one` for `δ<0`).
> - **Proved.** Full equality, all in ℤ. **Hypothesis:** `Monotone d` (load-bearing — `qip*` read `d`'s
>   prefix structure) + feasible-set nonempty. **Foundational bound** `abs_qipDelta_le_m : |δ| ≤ m`
>   (so `isLeast_sumSq`/the witness apply). **Assumed / Cited / Deferred.** none.

> **Claim (θ closed form, Thm 7.10 `r=0`).** For `Monotone d`, the number of `Gqip`-minimisers is
> `cTheta d = Nat.choose m |δ|.natAbs`.
>
> - **Lean:** `qipNumMinimisers_eq_cTheta (d) (hd : Monotone d) (hne : (qipFeasible d).Nonempty) :`
>   `((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card = cTheta d`.
> - **Gloss / proof.** `N=0`: unique feasible point, `m=0`, `|δ|=0`, `C(0,0)=1`. `N≥1`: bijection
>   (`Finset.card_bij'`) between the minimiser set and `powersetCard |δ| (qipLow d)`, then
>   `Finset.card_powersetCard` gives `C(#qipLow, |δ|) = C(m, |δ|)`. Forward `e ↦ {i ∈ qipLow :
>   (qipT ↑e) i ≠ 0}`; inverse `A ↦ eOfSupport d A` (`eOfSupport A i = (a + [i∈A]·sgn δ − d_{i+1}).toNat`
>   on `qipLow`, `0` off). Well-definedness + mutual inverse stand on the **integer-square equality
>   characterization** `sumSq_eq_abs_characterization`: a feasible `t` over a finite set (`∑t=δ`)
>   attaining `∑t²=|δ|` is `{0, sgn δ}`-valued with exactly `|δ|` nonzeros. A minimiser's `t = qipT ↑e`
>   has `∑t=δ` (`sum_qipLow_qipT`, prefix support) and `∑t²=|δ|` (`qipMinimiser_sumSq`), so its
>   support-set has card `|δ|`; `eOfSupport A` is feasible and attains `cValue` for any `A ⊆ qipLow`
>   with `#A=|δ|` (`eOfSupport_feasible`, `Gqip_eOfSupport`).
> - **Proved.** The exact count `= Nat.choose m |δ|.natAbs`. **Hypothesis:** `Monotone d` + nonempty.
>   **Assumed / Cited / Deferred.** none.

> **Claim (integer-square equality, reusable).** For `t : ι → ℤ` and finite `s`, if `∑_s t = δ` and
> `∑_s t² = |δ|` (the lower bound `abs_sum_le_sumSq` attained) then `t` is `{0, sgn δ}`-valued on `s`
> with `#{i ∈ s : t i ≠ 0} = |δ|`.
>
> - **Lean:** `sumSq_eq_abs_characterization (s) (t) (δ) (hsum) (hsq) :`
>   `(∀ i ∈ s, t i = 0 ∨ t i = δ.sign) ∧ (s.filter (fun i ↦ t i ≠ 0)).card = δ.natAbs`. Pointwise
>   helper `int_sq_eq_abs_cases : t²=|t| → t ∈ {−1,0,1}`.
> - **Gloss.** `∑(t²−|t|)=0` with each term `≥0` ⟹ each `t²=|t|` ⟹ `t∈{−1,0,1}`; then `δ = #pos − #neg`,
>   `|δ| = #pos + #neg` force the nonzeros to the common sign `sgn δ` and `#nonzero = |δ|`.
> - **Proved.** The full equality case (the converse-direction content the value tide left open).

> **Claim (witnesses, non-vacuity).** The closed-form objects evaluate to the paper's numbers.
>
> - **Lean (all `decide +kernel`, axiom-clean):** `cValue_d222 = 3`, `cTheta_d222 = 1` (Ex 6.2,
>   `m=2,a=3,δ=0`); `qipRound_qipDelta_d639` (`a=12,δ=1`), `cValue_d639 = 55`, `cTheta_d639 = 4`
>   (Ex 6.3 rearrangement `d639 = (8,8,11,11,11,13,13,13,15)`). Both `cTheta` witnesses non-trivial
>   (`1` and `4`), so the count theorem is not vacuously about a singleton.

---

## Permutation invariance (Cor 5.10) — obstruction, NOT proved here

The honest statement is that the **combinatorial** `cCodim d r` / `numTop d r` (Kostant-side,
`Core.CTheta`) depend only on the multiset `{d_0,…,d_N}`. This is **not** a corollary of this file:

- `cValue`/`cTheta` are functions of `qipM`/`qipS`/`qipRound`/`qipDelta`, which read `d` through its
  **order-sensitive** prefix data (`qipA d l = ∑_{i=0}^l d_i − l·d_l`, the `findGreatest` threshold
  `qipM`, the prefix sum `qipS`). They are the correct QIP/closed-form invariants only for `Monotone
  d` — the whole tide assumes it.
- The bridges `cCodim_eq_qipMin` and `qipMin_eq_cValue` both require `Monotone d`. A permutation `d∘σ`
  is generally non-monotone, so neither applies to it; `cValue (d∘σ)` need not equal `cCodim (d∘σ) 0`.
- There is **no sort-normalisation bridge** in the engine (no `cCodim (d∘σ) r = cCodim (sort d) r`),
  and `codimForm`/`kostantPartitions` carry no manifest permutation symmetry (the interval-module
  index `[i,j]` and the Kostant constraint `d_k = ∑_{i≤k≤j} m_{ij}` are anchored to chain positions).
- The paper proves Cor 5.10 via the **Poincaré series** (Bundle 3) — genuinely new machinery.

**Verdict.** A real lift, not a clean corollary. Left for the controller to roadmap (Poincaré route or
a sort-normalisation bridge on the Kostant side; the latter would also need the missing θ-side bridge
`numTop d 0 = qipNumMinimisers`).

---

## Audit

- `lean/scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `lake build` green (1800 jobs); `lake build DLNFibre.Core.CThetaValue` green, no errors and no
  line-length / unused warnings in the new code (one pre-existing `show`-style linter note at the
  upstream `sum_qipLow_qipShift_sq`, untouched).
- `#print axioms qipNumMinimisers_eq_cTheta` (and `qipMin_eq_cValue`, `sumSq_eq_abs_characterization`,
  `cTheta_d639`): `[propext, Classical.choice, Quot.sound]` only.
- Numerics: `scratch/value_derivation.py` — brute `qipMin`/minimiser-count vs closed form, 0 mismatches
  on (2,2,2)→(3,1), Ex 6.3 (8,8,11,11,11,13,13,13,15)→(55,4), (4,5,8,9,10,10)→(20,2),
  (2,5,6,7,10)→(10,2), (2,2,3)→(4,2), (1,4,4,9)→(4,2), (3,3,3,3)→(6,1).
- Fidelity review (Lean ↔ informal claim): **PASS** (reviewer, 2026-06-18; decorrelated Codex at
  `codex/bijection-equality-{prompt,answer}.md` + an independent `Gqip` brute-forcer). All five checks
  survived: (1) `qipNumMinimisers_eq_cTheta` filter predicate = minimiser condition, `cTheta = C(m,|δ|)`,
  weakest hypotheses, `N=0` branch genuine; (2) `sumSq_eq_abs_characterization` correct across `δ<0`,
  `δ=0`; (3) the `card_bij'` bijection genuinely inverse (no `simp` gap), `eOfSupport_feasible`/
  `Gqip_eOfSupport` proved for ARBITRARY `A ⊆ qipLow`, `#A=|δ|`; (4) `cTheta_d222=1`, `cTheta_d639=4`
  non-vacuous; (5) perm-invariance (Cor 5.10) obstruction verdict honest (no over/under-claim). No
  discrepancies.
- **Status: sorry-free + reviewed.**

## Judgement calls

- **`eOfSupport` generalises `qipWitness`.** The C-side used the canonical indicator witness
  `qipRoundT = [i<|δ|]·sgn δ`; the θ-bijection needs an arbitrary support `A`, so `eOfSupport d A` uses
  `[i∈A]·sgn δ`. Its feasibility/value lemmas (`eOfSupport_feasible`, `Gqip_eOfSupport`) re-run the same
  m-face assembly with `#A` in place of `|δ|.natAbs` (equal by `mem_powersetCard`), so the value
  computation is unchanged.
- **`sumSq_eq_abs_characterization` kept local to `CThetaValue`** (first use). It is the equality case
  of `Core.CThetaExplicit.abs_le_sumSq`/`isLeast_sumSq`; if a second consumer appears it should lift to
  `CThetaExplicit`.
