# Fidelity cert — `resolution_value_of_atlas` (S-min refactor, #34/pp2 #134)

Reviewer: focused fidelity pass on `cover/resolution-atlas-value` @1c4b9b5
(`lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean`). The VALUE step the final `resolution_charts`
assembly plugs into. Build GREEN (2672 jobs, 0 sorry in-file).

## Verdict: SURVIVED — sound, faithful (cleaner equivalent), non-vacuous, S2-confined. No over-claim.

### (1) SOUND — the `le_antisymm` has no gap. CONFIRMED.
`resolution_value_of_atlas` (lines 197-204): after `rw [ofReal_lambdaCore_eq_half_inf]` the goal is
`⨅ monomialThreshold = ½·m₀` (`m₀ = (Adm M).inf' Mval |>.toNat`). `le_antisymm`:
- `½·m₀ ≤ ⨅`  via `le_iInf hatlas.threshold_ge` — (C≥): every path's threshold ≥ ½·m₀.
- `⨅ ≤ ½·m₀`  via `iInf_le_of_le i₀ (le_of_eq hi₀)` from `hatlas.achiever` — (C=∃): one path = ½·m₀.
Both directions present, correct order (a=⨅, b=½·m₀), green. No gap. The `⨅` only needs one achiever
at the min + a uniform lower bound — exactly the two clauses supplied.

### (2) FAITHFUL — the (S-min) form is a correct, cleaner equivalent; it does NOT improperly weaken.
- `ofReal_lambdaCore_eq_half_inf` (lines 147-170) proves `ofReal(lambdaCore M) = m₀/2` in ℝ≥0∞, using
  `Mval_nonneg_adm` (locally re-proven, clean) so `(inf' Mval).toNat` round-trips through the ℤ-cast.
  `lambdaCore := ½·(inf' Mval : ℤ)` (Lambda.lean:80), so `½·m₀ = lambdaCore` is definitional. Faithful.
- `of_mult_and_achiever` (lines 180-190) HONESTLY DERIVES both clauses from the geometry, not assumes:
  - (C≥) via `monomialThreshold_ge_of_mult'` — built on `monomial_rlct.1` (S2 threshold = ⨅ axisRatio)
    + `axisRatio_ge_of_mult` (PROVEN, pure ℝ≥0∞ arithmetic from `m₀·k ≤ h+1`, Skeleton:64). Spectator
    `k=0` axes give `axisRatio=⊤` (sound: a free axis imposes no bound, can't lower the ⨅).
  - (C=∃) via `monomialThreshold_eq_half_of_binding = le_antisymm (le_regularSeq) (ge_of_mult')`; the
    upper half `monomialThreshold_le_regularSeq` (PROVEN, Skeleton:149) gives `= c/2` from the binding
    regular-sequence divisor `(k,h)=(1,c−1)`. So the achiever is derived from a concrete binding divisor.
- (S-min) correctly weakens "full surjectivity onto Adm M" → "the MINIMISER is reached" — which is
  exactly and only what `le_antisymm` over the `⨅` consumes. Strictly weaker, NOT improperly so: the
  uniform (C≥) covers all non-minimising paths; only one minimiser need realise `= ½·m₀`. Correct.

### (3) NON-VACUITY — end-to-end. CONFIRMED.
`M = ![1,1]`: `m₀ = 1` (decided), `lambdaCore = ½`. The one-path atlas (`ι=Unit, d=1, k=![1], h=![0]` —
binding divisor `(1,0)=(1,m₀−1)`) satisfies both clauses (`isResolutionAtlas_M11`), and the in-file
`example` (line 239) returns `⨅ = ofReal(lambdaCore ![1,1]) = ofReal(½)`. Re-compiled independently.
The achiever is a GENUINE finite nonzero value (½), not a vacuous `⊤`/`0`. The predicate has a model.

### (4) clean-three / S2-confinement — CONFIRMED EXACTLY as the dispatch states.
`#print axioms`:
- `resolution_value_of_atlas` : **[propext, Classical.choice, Quot.sound]** — NO `monomial_rlct`. ✓
- `ofReal_lambdaCore_eq_half_inf`, `Mval_nonneg_adm` : clean-three.
- The per-chart bracket lemmas (`monomialThreshold_ge_of_mult'`, `_eq_half_of_binding`), the
  constructor `of_mult_and_achiever`, the M11 witness : carry `monomial_rlct` (S2) — LEGITIMATE (they
  ARE the per-chart RLCT-of-monomial facts; S2 is the single cited axiom for exactly that).
So S2 is confined to the bracket lemmas; the value lemma's own proof is S2-free.

### The single open obligation: ONLY the (S-min) achiever. CONFIRMED.
No sorries in-file (grep hits are docstring "sorry-free" mentions). `achiever` is an explicit `Prop`
field, satisfiable whenever the cover supplies a minimising stratum with the binding regular-sequence
divisor — the genuine cover-exhaustiveness residual, correctly isolated, NOT a buried sorry, NOT a
false/unsatisfiable claim (the M11 witness discharges it concretely).

## No over-claim
The statement concludes `⨅ monomialThreshold = ofReal(lambdaCore M)` — the value of the min-over-charts
of monomial thresholds, NOT `rlctAtOn(dlnLoss M 0) 0 = lambdaCore`. The scope note (lines 28-29) is
honest: core-only, the regular `[−r²+r(H⁰+Hᴸ)]/2` shift is L2/Fubini elsewhere; `IsResolutionAtlas`
carries no `nReg`. The `⨅ monomialThreshold → rlctAtOn` bridge (the cover `∫⁻=Σ∫⁻` decomposition) is a
separate downstream obligation. The name "resolution_value" accurately denotes the resolution chart-tree
value given the scope note. No over-claim.

## Net
The value half of the assembly is sound and faithful. The (S-min) refactor is a clean, correct
equivalent of the #133 4-conjunct form — strictly weaker only in the proper way (minimiser-reached, not
full surjectivity). The whole geometric residual is the single `achiever` Prop. Gating obligation for
the assembly value half is met; the per-chart S2 dependency is the designed confinement.
