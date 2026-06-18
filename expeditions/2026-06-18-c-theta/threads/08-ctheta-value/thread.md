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
- **#14 DONE** (sorry-free, axiom-clean): `qipMin_eq_cValue : qipMin d = cValue d` (m-face assembly:
  drop-to-m + `isLeast_sumSq` lower bound + the rounded witness `qipWitness`).
- **#15 DONE** (sorry-free, axiom-clean): `qipNumMinimisers_eq_cTheta` — the count of `Gqip`-minimisers
  is `cTheta d = C(m, |δ|)`. Route: the integer-square equality characterization
  `sumSq_eq_abs_characterization` (a feasible `t` attaining `∑t²=|δ|` is `{0,sgn δ}`-valued with `|δ|`
  nonzeros) pins minimisers; the bijection `e ↦ {i ∈ qipLow : (qipT ↑e) i ≠ 0}` ↔
  `powersetCard |δ| qipLow` (inverse `A ↦ eOfSupport d A`) via `Finset.card_bij'`, then
  `Finset.card_powersetCard`. `N=0` handled separately (unique minimiser, `C(0,0)=1`).
  - **Perm-invariance (Cor 5.10): NOT a corollary — genuine obstruction, reported, not forced.**
    `cValue`/`cTheta` read `d` through `qipM`/`qipS`/`qipRound`/`qipDelta`, all order-sensitive (prefix
    sums `∑_{i=0}^l d_i` + the `findGreatest` threshold). The C-bridge `cCodim_eq_qipMin` and
    `qipMin_eq_cValue` both require `Monotone d`; a permuted `d∘σ` is generally non-monotone, so the
    closed form does not apply to it, and there is no sort-normalisation bridge in the engine. Honest
    route is the paper's Poincaré-series argument (Bundle 3) — for the controller to roadmap. Also no
    `numTop d 0 = qipNumMinimisers` θ-side bridge exists yet (only the C-side `cCodim_eq_qipMin`), so
    even relating this file's `cTheta` to the Kostant-side `numTop` needs that bridge first.

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
CThetaValue is now sorry-free (#13/#14/#15 all done), wired into `DLNFibre.lean` (single-writer
append), whole library green. Committed on `expedition/c-theta`. Statement card: `statement-card.md`.
