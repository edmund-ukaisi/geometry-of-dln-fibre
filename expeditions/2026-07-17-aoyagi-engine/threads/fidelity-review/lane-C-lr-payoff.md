# Lane C (raw) — LR §§5–9 ((C,θ) forms + perm-inv + RLCT payoff) enumeration + cross-check

Read-only scout output (elder-commissioned, 2026-07-23). Source main.tex 874–2038; cross-checked against
`Core/QSeries*`, `Core/CTheta*`, `DLN/RlctPayoff*`, `DLN/RLCT/AoyagiCited.lean`, `AxCheck.lean`. 16 load-bearing
Core files sorry/axiom-audited (clean). Synthesized into `../../paper-fidelity-review.md` §C.

## §5 Poincaré
- Pochhammer `𝒫`, `Q^r_ud`: PROVEN `QSeries.P`/`Qseries` (power-series ℤ⟦X⟧ model, faithful).
- lem:Qs_codim (Q=θq^C+h.o.t): PROVEN `Qseries_coeff_cCodim`/`numTop_pos`/`cCodim_eq_of_Qseries_eq` (QSeriesExtraction).
- **thm:Pseries**: PROVEN `thm55` (general r) + `thm55_zero` (QSeriesThm55.lean:104). `altP` = paper's `(−1)ˢX^{s(s−1)/2}P` exactly.
- thm:PdPm (Durfee/pentagon): PROVEN `sum_Qseries_eq_Pmult` (QSeriesFivegon) + `durfee` (QSeriesDurfee) — ALGEBRAIC
  (paper cites Reineke + spectral sequence).
- spectral-sequence route / `𝒫=P(H*BGL)`: ABSENT (reached algebraically instead — RIGHTLY-SKIPPED).
- lem:shift: PROVEN `Qseries_corner_shift` (QSeriesShift).
- **cor:PermutationInvariance**: PROVEN `cCodim_comp_perm`/`numTop_comp_perm` (CThetaPermInvariance) + `_of_le`/`_comp_sort`/`_rev`.

## §6 QIP
- **thm:QIP** (codim=minQIP; θ=#minimisers): PROVEN value `cCodim_eq_qipMin` (CThetaQIPConverse); count
  `numTop_zero_card_eq_qipNumMinimisers` (CThetaThetaBridge). Monotone d (lifted to arbitrary d in CThetaArbitrary).
- lem:horiz_rep: PROVEN NARROWED (minimiser only) `minimiser_isHL`/`mOfE_surj_of_hl`; paper claims EVERY partition.
- ex:223withQIP: MODELED `cCodim_d232_zero=4`/`numTop_d232_zero=2`.
- ex:N8: ABSENT (no #eval).

## §7 explicit formulas
- `m=max{l:Σd'≥l d'_l}`: PROVEN `qipM` (CThetaDropM, Nat.findGreatest).
- thm:QIPreduced2closestpoint: PROVEN `qipMin_eq_cValue` (CThetaValue).
- closest-point count `k=binom(m,δ)` (Conway–Sloane): PROVEN `cTheta=choose(qipM,δ)` via `isLeast_sumSq`
  (paper CITES ConwaySloane; Lean proves).
- **thm:main-codim** (codim + fibre codim + count): PROVEN 3 parts — `cCodim_eq_cValue_comp_sort`,
  `codimRepCanonical_fibre_eq_cCodim_add_shift` (=C+r(d₀+d_N−r), zero-cite, FibreCodimFinal), `numTop_eq_cTheta_comp_sort`.
- the paper's fractional-form expression (lem:delta / prop:Dhat): value-equivalent (`cValue`), NOT form-identical
  (fractional parts recast as Int rounding residues).
- ex:closestpoint, constant-d example: ABSENT.

## §8 RLCT payoff — the crux
- Def 8.1 rlct: PROVEN built `rlctGlobal` (cite-free sSup) + local `rlctAt`.
- archimedean zeta / rlcm: CITED `cited_local_zeta_pole` (meromorphic continuation — Atiyah, genuine monument).
- prop:rlct_elem: (i) upper `≤codim/2` = `cited_watanabe_upper_ax`; (iv) Thom-Sebastiani PROVEN
  (`product_min_rlct`/`rlct_additive_smooth_block`); (ii)/(iii) ABSENT.
- **thm:aoyagi-rlct `rlct=C/2`** — TWO tracks:
  (A) CITED general: `rlct_lossDLN_zero_eq_half_cCodim_aoyagi` — `le_antisymm` of `cited_watanabe_upper_ax` +
      `cited_aoyagi_lower_ax` (AoyagiCited:56,66), guard `0<N ∧ B.rank=r ∧ r≤min d`. Codim side PROVEN zero-cite
      (real↔complex transfer, fibre codim, codim=cCodim=C).
  (B) FROM-SCRATCH: `aoyagi_learning_coefficient_L2` PROVEN clean-three; `_L1` PROVEN; `_gen` clean conditional on
      `hbox`; `_gen_le` clean unconditional; `aoyagi_learning_coefficient` sorryAx (general; the monument
      `exists_coreResolution`). Kill-path: `via_engine` does NOT invoke the two cites (AxCheck-confirmed).
- rlcm value formula `m²{S̃/m}(1−{S̃/m})…`: ABSENT/DEFERRED (`poleOrder` defined; value not proven — the ρ-seam).

## §9 Appendix A
- avoiding-ideal `ℛ/ℋ/ψ/φ/𝒜`, thm:UsingAvoidingIdeal, ex: ABSENT. A DIFFERENT θ-characterization IS built:
  `chainHeight_boxPart`/`bindingSet_chainHeight_eq_thetaCount` (chain-height of binding-minimiser poset, clean-three).

## Least-sure (scout)
1. from-scratch value identification `2·aoyagiLambda = cCodim`: numerically matches ((2,2,2)→3/2); assembled
   through bridge lemmas (not one single audited end-to-end theorem for the from-scratch headline). ~0.8 holds / ~0.5 single-theorem.
2. lem:horiz_rep narrowed to minimisers (sufficient for QIP; full generality not separately proven).
3. cValue vs the paper's fractional form: value-equivalent, not proven form-identical (cosmetic bridge gap).

## What §8 rests on (precise)
CITED general (2 axioms, codim side fully proven zero-cite) + from-scratch clean at L≤2, conditional general-L,
open (sorryAx = the monument) at summit. rlcm value + Appendix A absent/deferred. Payoff root footprints
= [propext, Classical.choice, Quot.sound] + the two DLN cites.
