<task>
An RLCT (real-log-canonical-threshold) double-induction question. A finiteness proof descends on
chain arity; each peel frees a block and couples it to a recursively-handled remainder. I want your
independent analysis of HOW joint finiteness holds at an EXACT saturation point. Reasoning only.

## Setup
We prove `∫ (loss)^{−c'} dμ < ∞` for all `c' < ½·minAdm(M)`, by induction on chain arity. One peel of
chain `M` produces, in resolved corner coordinates on a units sector:
- a FREED block: a free matrix `Γ` of dimension `P` (= peelCharge), entering the loss as `‖Γ‖²` times
  a bounded-below unit `U₀ ≍ 1`;
- a REMAINDER: the reduced chain `M'` (arity one less), whose loss `V(w)` is the object of the
  induction hypothesis. The IH gives: `∫ V(w)^{−c''} dw < ∞` for all `c'' < ½·minAdm(M')`.
- The arithmetic identity at the binding cut: `minAdm(M) = P + minAdm(M')`.

The freed block and the remainder share a common radial. Write `R = minAdm(M')`. The combined loss on
the sector has the form `F = u₀²·(U₀ + V_scaled)`, where `u₀` is the freed block's radial magnitude
(so the block-radial Jacobian contributes `u₀^{P−1}`) and `V_scaled` is the remainder's loss placed at
the same corner. All units are bounded BELOW by a positive constant on the sector (this is the "units
sector"; off it, a lower-dimensional stratum recurses separately).

## The saturation
The target threshold is `c' < ½·minAdm(M) = ½(P+R)`. But:
- the freed block ALONE (ignore the remainder) integrates only for `c' < P/2` (`∫ u₀^{P−1−2c'} du₀`);
- the remainder ALONE (the IH) gives only `c'' < R/2`;
- and `½(P+R) = P/2 + R/2` sits EXACTLY at the sum of the two individual bounds.
So a naive split — bound `F^{−c'} ≤ (freed part)^{−c'} · (remainder part)^{−c'}` and integrate the two
factors separately, or Hölder-split the exponent `c' = c_f + c_r` — is infeasible at `c' = ½(P+R)`:
one needs `c_f < P/2` AND `c_r < R/2` with `c_f + c_r = P/2 + R/2`, impossible for strict inequalities.

<questions>
State FACT vs JUDGEMENT.
1. Given the naive split provably fails at the saturation `c' = ½(P+R)`, what is the mechanism by
   which the JOINT integral `∫ u₀^{P−1} · F^{−c'} · (remainder measure) < ∞` is nonetheless finite for
   all `c' < ½(P+R)`? Describe the change of variables / corner structure that makes it work, and
   pinpoint exactly WHERE the remainder's `R` worth of "budget" combines with the freed block's `P`.
2. What must the induction hypothesis provide about the remainder `V` BEYOND the bare finiteness
   `∫V^{−c''}<∞ (c''<R/2)` — i.e. is a black-box RLCT bound on `V` enough, or is structural
   information about `V` (its own resolved/radial form) required to make the coupling go through? Why?
3. What ROLE does the units-sector hypothesis (`U₀` and the remainder's units bounded below by a
   positive constant) play — specifically, if a unit were allowed to approach 0 (a rank-drop
   sublocus), where exactly would the argument break, and is excising that sublocus to a separate
   recursive branch legitimate (finite measure / the sublocus is lower-dimensional)?
</questions>
</task>

<output_contract>
Three numbered answers, each 4-8 sentences, FACT/JUDGEMENT tagged. End with a one-line
"JOINT-MECHANISM:" summary naming the single structural device that defeats the saturation, and a
one-line "IH-MUST-CARRY:" stating the minimal extra the induction hypothesis must provide beyond bare
finiteness.
</output_contract>

<grounding_rules>
Ground in the setup. RLCT facts permitted: for a free block of dimension N over a bounded box,
`∫ ‖block‖^{−2c'} < ∞ ⟺ c' < N/2`; and `∫₀¹ u^{k}(A+u²B)^{−c'}du` is finite (A>0 bounded below) with a
value bounded uniformly in the units, but is NOT finite as A→0 for large c'. Do not invent structure
beyond what the setup states; if you need an assumption, name it.
</grounding_rules>
