# Thread 08 — CThetaValue (value-assembly tide)

Owner: ctheta-value (lean-formaliser). Branch `expedition/c-theta`. Module
`lean/DLNFibre/Core/CThetaValue.lean` (new; imports `Core.CThetaDropM` + `Core.CThetaExplicit`).

## Target
Thm 7.10 (r=0) closed form: `qipMin d = cValue d` and the minimiser count `= cTheta d`, where
`a = (2S+m)/(2m)`, `δ = S − m·a`, `cValue = ½(d_0² − ∑_{i=1}^m(d_i−d_0)² + m(a−d_0)² + 2(a−d_0)δ + |δ|)`,
`cTheta = Nat.choose m |δ|`. `m = qipM d`, `S = qipS d` from CThetaDropM.

## Status
- **#13 DONE** (sorry-free): defs `qipRound`/`qipDelta`/`cValue`/`cTheta`; `abs_qipDelta_le_m : |δ| ≤ m`
  (via `Int.mul_ediv_add_emod` + `nlinarith`); witnesses `cValue_d222=3`, `cValue_d639=55`,
  `cTheta_d222=1`, `cTheta_d639=4`, `qipRound_qipDelta_d639` — all `decide +kernel`, axiom-clean.
- **#14 IN PROGRESS** (HARD, currently `sorry`): `qipMin_eq_cValue`.
- **#15 PENDING** (`sorry`): `qipNumMinimisers_eq_cTheta` (θ-count) + perm-invariance.

## Codex consult (xhigh) — `codex/assembly-{prompt,answer}.md`
Strategy for #14, route (i):
- **≥**: attain `qipMin` at `e*` (`Finset.exists_mem_eq_inf'`); via `two_Gqipℤ_sub_sq` `e*` is a
  `Phi`-minimiser; via `qip_minimiser_support_le_m` (drop-to-m) `e*` has zero tail; set
  `t_i = e*_i + d_{i+1} − a` (∑ t = δ), apply `isLeast_sumSq` lower bound `|δ| ≤ ∑ t²`. The `≥`
  direction needs NO e≥0 (isLeast_sumSq is unconstrained over ℤ).
- **≤**: explicit rounded witness on the m-face: `t_i ∈ {0,1}` (δ≥0) or `{−1,0}` (δ<0), `|δ|` nonzero;
  `e_i = a + t_i − d_{i+1}` on prefix, `0` on tail. Needs in-face nonnegativity.
- **THE GAP (Codex, verified numerically):** witness nonnegativity for `δ < 0` needs the STRONGER
  `d_i ≤ a − 1` (not `d_i ≤ a`), because some `t_i = −1`. Both follow from the within-prefix bound
  `m·d_i ≤ S` (= `qip_within_prefix`, which I validated but the lead did NOT commit to CThetaDropM —
  I add it locally in CThetaValue) + rounding: δ≥0 ⟹ S<m(a+1) ⟹ d_i≤a; δ<0 ⟹ S<m·a ⟹ d_i≤a−1.
- Boundary cases to test: `δ=0`, `δ<0`, `m=N` (empty tail), `m=1`.
- 8-step Lean skeleton in the answer; hardest: Fin N ↔ m-prefix reindex, t-substitution sum algebra,
  inf' attainer.

## Numerics
`scratch/value_derivation.py` — brute `qipMin`/minimiser-count vs closed form, 0 mismatches on
(2,2,2)→(3,1), (8,8,11,11,11,13,13,13,15)→(55,4) [paper Ex6.2/6.3], (4,5,8,9,10,10)→(20,2),
(2,5,6,7,10)→(10,2), (2,2,3)→(4,2), (1,4,4,9)→(4,2), (3,3,3,3)→(6,1). Nonneg gap confirmed.

## Commit discipline
CThetaValue carries 2 sorries (#14/#15) — NOT committed and NOT wired into the aggregator until
sorry-free (sorry gate). Building locally as the working skeleton.
