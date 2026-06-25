# Review #68 — Fidelity gate: `codim(fibre d B) = C + δ` vs paper Lemma 4.6

**Reviewer:** independent (controller-commissioned, thread 31 dispatch). **Function:** fidelity
(report-only). **Target HEAD:** `265c28fd`. **Verdict: PASS.**

Target:
`Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`
(`lean/DLNFibre/Core/FibreCodimFinal.lean:165`).

Source of truth: Lehalleur–Rimányi 2024, **Lemma 4.6** (`lem:rank_vs_fibers`,
`paper-sources/.../source/main.tex:844-859`):

> for `d ∈ ℕ^{N+1}`, `0 ≤ r ≤ min d`, `B ∈ Mat_{d_N,d_0}^{rk=r}`:
> `codim_{Rep_d} mult⁻¹(B) = codim_{Rep_d} Σ^r_d + r(d_0 + d_N − r)`.

## The 7 fidelity points

1. **`codimRepCanonical (fibre d B)` = the paper's `codim_{Rep_d} mult⁻¹(B)`.** `fibre d B =
   {A | mult d A = B} = mult⁻¹{B}` (`Setup.lean:64,83`); `Rep_d = Tuple d` is the composable-tuple
   space (`Setup.lean:33`), `mult d A = A_N⋯A_1` the paper's product (`Setup.lean:51`, order verified
   by the `(2,2,2)` witness `Setup.lean:105`, `A₂A₁`). `codimRepCanonical` is `Ideal.height` of the
   vanishing ideal of `canonicalCoord '' Z` — the entry-flattening `Rep_d ≃ (RepCoord d → k)`
   (`OrbitCodim.lean:107,134`): the standard codim of the Zariski closure in the affine coordinate
   ring, one variable per matrix entry. **Match.**

2. **`cCodim d r` = the paper's `C = codim Σ^r`.** `cCodim` is `inf'` of `codimForm` over
   `kostantPartitions d r` (`CTheta.lean:160`); `codimForm` is *literally* the Cor 3.5 form
   `Σ_{1≤i≤u≤j≤v≤N} m_{(i−1)(j−1)} m_{uv}` (`CTheta.lean:74`, `= main.tex:642`,
   `codimForm_multiplicityArray` is `rfl`). `codim Σ̄^r = cCodim` is LANDED
   (`SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`), and `codim Σ̄^r = codim Σ^r` (the
   closure bridge `ClosureBridge`, paper Cor 4.4 + Lemma 4.5). **Match.**

3. **`r·(d (Fin.last (N+1)) + d 0 − r)` = the paper's `δ = r(d_0 + d_N − r)`.** The theorem is at
   `d : Fin (N+2)`, so under the dictionary `d_0 ↦ d 0`, `d_N ↦ d (Fin.last (N+1))` (= `d_{N+1}`, the
   re-parametrized outer width), the shift is exactly `δ`. `δ` is symmetric in the two outer widths.
   `hp,hq` (`r ≤` each outer width) keep the ℕ-subtraction honest. **Match.**

4. **`Fin (N+2)` indexing — no depth off-by-one.** `Setup.Tuple` is for `d : Fin (M+1)` with `M`
   matrices; at `M = N+1` this is `N+1` factors `A₀,…,A_N`, dimension vector `(d_0,…,d_{N+1})` of
   length `N+2`. Identifying `N_paper = N+1` preserves the matrix count. The older `Fin (N+1)`
   theorem in `FibreCodimMinPrimes` is the same engine at a shifted parameter; `Fin (N+2)` is the
   intended outer indexing and forces **depth ≥ 1** (≥ 2 widths) — the degenerate `mult = const`
   case is structurally excluded, which is correct (the bundle argument needs ≥ 1 edge).

5. **Hypotheses are the paper's, and minimal-up-to-redundancy.**
   - `h : (kostantPartitions d r).Nonempty` ⟺ paper's achievability `r ≤ min d`: forward
     `corner_le_dim_of_mem` (`CCodimCornerMono.lean:259`, a Kostant corner `r` forces `r ≤ d k`
     everywhere); converse `kostantPartitions_nonempty_of_le` (`:245`, for depth ≥ 1). **Not vacuous,
     not secretly excluding cases** — for every `(d,r)` with `r ≤ min d` it holds and the fibre is
     nonempty (`fibre_normalForm_nonempty`).
   - `hp : r ≤ d (Fin.last (N+1))`, `hq : r ≤ d 0`: **redundant** given `h` (both follow from
     `corner_le_dim_of_mem`). Harmless, not a restriction.
   - `hN : (0:Fin(N+2)) ≠ Fin.last (N+1)`: **vacuously provable for every `N : ℕ`** (`0 = N+1`
     impossible; verified by `omega`). Carried only to reuse generically-stated `Setup` lemmas.
   - `[IsAlgClosed k][CharZero k]`: matches the paper (works over ℂ, descends by Thm `base_field`;
     alg-closed char 0 covers ℂ).

6. **`k : Type 0` scope.** A universe restriction (all `Type 0` alg-closed char-0 fields, incl. ℂ),
   not an unsoundness. Acceptable.

7. **No overclaim.** Name `codimRepCanonical_fibre_eq_cCodim_add_shift` — `codim`, not `rlct`.
   Conclusion is a codimension identity only. Every `rlct`/Watanabe/Aoyagi mention in `Core` is a
   docstring flagging the `½·codim` reading as a **separate, Cited, DLN-side** payoff
   (`DLNFibre/DLN/RlctPayoff*.lean`); none is a `Core` theorem. **No RLCT smuggled.**

## Concrete-case check (by hand + Lean `decide`)

`(2,2,2)`, `Rep` dim = 8.
- `r=0`: `C = cCodim ![2,2,2] 0 = 3` (`CTheta.cCodim_d222_zero`, `decide +kernel`), `δ = 0·(2+2−0) = 0`,
  so `codim mult⁻¹(0) = 3`. Paper Ex (`main.tex:775`): `Σ^0_{(2,2,2)}` top component codim 3. **Match.**
- `r=1`: `C = cCodim ![2,2,2] 1 = 1` (`CTheta.cCodim_d222_one`), `δ = 1·(2+2−1) = 3`, so
  `codim mult⁻¹(B) = 4` for rank-1 `B`; `dim = 8 − 4 = 4`. Internally coherent with the bundle count.

`![2,2,2] : Fin (1+2) → ℕ` is `def`-eq `d222` (`example … := by decide`), so the central theorem
instantiates non-vacuously at the paper's headline example (`N=1`, depth 2).

## Independent checks run

- `#print axioms codimRepCanonical_fibre_eq_cCodim_add_shift` = `[propext, Classical.choice,
  Quot.sound]` (re-verified; no `sorryAx`, no `native_decide`).
- `omega` proof that `hN` holds for all `N`.
- Decorrelated **Codex (gpt-5, xhigh)** read on Lean↔paper match: independent **PASS** on all 6
  posed points, all marked `[fact]`, no new discrepancy. Its one note matches mine: `h` is exactly
  the paper's realizability condition expressed via Kostant partitions.

## Verdict

**PASS / survived.** The Lean central theorem is a faithful encoding of Lemma 4.6: the geometric
codimension of the multiplication-map fibre, `= C + δ`, with `C` and `δ` the paper's combinatorial
codimension and matrix-stratum shift. No mis-encoding, no depth off-by-one, no vacuity, no overclaim.
Redundant hypotheses (`hp`, `hq`, `hN`) are harmless — a simplification thread could drop them, but
that is a quality note, not a fidelity defect.
