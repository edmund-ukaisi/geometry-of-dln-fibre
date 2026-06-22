# DeepestGaugeChart — exact-algebra certificate for #44 sub-lemmas 3+4 (pp-hall, 2026-06-22, #150)

**The pen-and-paper cert gating #44's two heavy sub-lemmas** (`deepest_gauge_chart_exists` +
`deepest_loss_in_gauge_coords`), the #131/g131 pattern applied to the L2/D1 deepest-point normal form.
Produces the explicit `DeepestGaugeChart` construction on a rank-r-exact node + the det-unit/non-MP
Jacobian fact + the loss-form germ + `chart_zero`. crux2 transcribes into the #44 sub-lemmas 3/4. NB the
**NON-MP** transport (`rlctAtOn_unit_invariant_aux` + germ-locality, NOT `comp_homeomorph`).

## Setup (rank-r-exact deepest point, the `IsDeepLayers` scope-cut)
At a deepest point `w0` with `IsDeepLayers H r B w0` (`w0 ∈ optimalSet H B ∧ ∀ s, (w0 s).rank = r` —
every layer rank EXACTLY `r`), gauge-slice each layer `C_s : H_s × H_{s+1}`. By `block_elimination` there
are units `P_s, Q_s` with `P_s (w0 s) Q_s = blockdiag[I_r, 0]`. In the gauge coords (the local deviation
from `w0`), each layer is

    C_s = [[ I_r + X_s , Y_s ], [ Z_s , T_s ]]
          (X_s: r×r, Y_s: r×(H_{s+1}−r), Z_s: (H_s−r)×r, T_s: (H_s−r)×(H_{s+1}−r) = the REDUCED block).

The **reduced widths** `M_s = H_s − r`; the **reduced core** is `‖∏ T_s‖² = dlnLoss M 0`.

## The construction (sub-lemma 3, `deepest_gauge_chart_exists`)
**The 2-factor block-product (folded over `L`).** For two rank-r layers (`g150_gauge_chart.py`),
`C_1·C_2` has blocks:
- `(0,0) = (I_r+X_1)(I_r+X_2) + Y_1 Z_2 = I_r + (regular)` — regular;
- `(0,1) = (I_r+X_1)Y_2 + Y_1 T_2` — regular;
- `(1,0) = Z_1(I_r+X_2) + T_1 Z_2` — regular;
- `(1,1) = Z_1 Y_2 + T_1 T_2` — the **reduced block** (`T_1 T_2` = the reduced chain + a cross `Z_1 Y_2`).

**The regular coordinates** are the **product regular-residual blocks**
`E := (∏C − blockdiag[I_r,0])` restricted to the `(0,0),(0,1),(1,0)` positions; the **reduced
coordinates** are the `T_s` blocks. Verified (`g150_jac_fix.py`): the regular residuals `(E00,E01,E10)`
have **Jacobian rank `= 3`** over the gauge regular coords at `w0` (linear parts `E00 ↔ {X_1,X_2}`,
`E01 ↔ Y_2`, `E10 ↔ Z_1`), so they are independent regular directions; completing them with a transversal
(e.g. `X_1, Y_2, Z_1`) gives a **det-unit coordinate change**, KEEPING the `T_s` as reduced.

**`nReg = r(H_0 + H_last − r)`** (the rank-r gauge-orbit slice dimension — the regular residuals live at
the two chain ENDPOINTS, the interior rank-r spine absorbed). Verified to match the interface for
`(2,2,2)r1→3`, `(3,3,3)r2→8`, `(4,3,2)r2→10`, `(2,2,2)r2→4`, `(3,2,1)r1→4` (`g150_general_r.py`).

## The loss-form germ (sub-lemma 4, `deepest_loss_in_gauge_coords`)
Near `w0` (all regular coords `→ 0`):

    dlnLoss H B ∘ chart  =ᶠ[𝓝 0]  (∑ᵢ E_i²)  +  dlnLoss M 0 (T-blocks),    dlnLoss M 0 = ‖∏ T_s‖².

The split is **EXACT** (a germ equality via the c-o-v, NOT a squeeze): the reduced block
`(1,1) = T_1 T_2 + Z_1 Y_2` carries the cross `Z_1 Y_2`, which is **regular×regular** (order 2 in regular
coords) and is **absorbed into the regular block** `E` by the chart c-o-v — NOT into the reduced core.
Verified (`g150_loss_form.py`): on `{reg = 0}`, `(1,1) = T_1 T_2` exactly; `(1,1) − T_1 T_2 = Z_1 Y_2 ∈
ideal(regular)`. So the regular coords `E` (the full product residuals) capture the cross term, and the
reduced core is the clean `‖∏ T_s‖² = dlnLoss M 0`. This is the #131 pattern (the residual is a smaller
matrix-chain core), here the L2/D1 deepest-point version.

## The det-unit / NON-MP Jacobian (the KEY — sub-lemma 5 input)
The chart's Jacobian determinant is a **bounded UNIT** near `w0` (`jac_unit`: `∃ U ∈ 𝓝 0, ∃ a b, 0 < a ∧
∀ x ∈ U, a ≤ |det Dchart| ≤ b`), but is **NOT identically 1** — the regular-residual c-o-v
(`E = product residuals`, which mixes the gauge blocks nonlinearly) has a Jacobian that is the rank-3
unit block × the spectator identity, a unit `≠ 1`. So the RLCT transport is **NON-MP**:
`rlctAtOn_unit_invariant_aux` (peel the bounded-unit `|det Dchart|` weight) + `rlctAtOn_germ_local`
(the germ equality) — **NOT `rlctAtOn_comp_homeomorph`** (which requires MP, `det = 1`). This is the
exact distinction the dispatch flagged: the deepest-gauge chart is a genuine c-o-v with a nontrivial
(but unit) Jacobian, transported by the unit-invariance + germ-locality lemmas, not the MP-homeomorph one.
The `weightedThreshold_transport` use-site (S1.1) carries the `|det Dπ|` weight; the bounded-unit peel
then strips it (the weight is a unit near `w0`).

## `chart_zero` (the basepoint pin)
`chart 0` is the gauge origin (all deviation blocks `= 0`), which by `block_elimination`'s `P_s,Q_s`
units maps back to `w0 = deepestPoint H r B`: `(paramsEquivFlat H).symm (chart 0) = deepestPoint H r B`.
So the chart fixes the deepest point — the transport's basepoint is `w0` (the singular zero of the loss),
exactly where the RLCT is computed (the #130 `χ 0 = 0` discipline, here `chart_zero`).

## The `r = 0` base (clean)
`r = 0`: `hB : B.rank = 0 ⟹ B = 0`; `IsDeepLayers` forces all layers rank 0 ⟹ `deepestPoint = 0`;
`M = H − 0 = H`, `nReg = 0·(H_0+H_last) = 0`. The gauge chart is the **IDENTITY** (no regular block, no
gauge to fix), and `dlnLoss H 0 ∘ id = dlnLoss M 0` directly. So sub-lemma 1 (`deepest_regular_core_r0`):
`rlctAt (dlnLoss H 0) 0 = rlctAtOn (dlnLoss M 0) 0` by `rlctAtOn_eq_rlctAt`. No chart needed
(`g150_general_r.py`).

## The scope-cut (Codex, adopted)
Prove the chart for **arbitrary `w0` with `IsDeepLayers H r B w0`**, then apply `deepestPoint_isDeep` to
specialise to `deepestPoint`. The algebra reduces to a **2-factor block-multiplication lemma folded over
`L`** (the per-layer-pair block product above; the regular residuals accumulate at the chain endpoints,
the reduced core is the `∏ T_s` chain). This avoids the full `L`-fold expansion — each fold step is the
2-factor block product, the interior rank-r spine contracting to the next reduced factor.

## What crux2 transcribes (the #44 sub-lemma map)
- **sub-lemma 3 `deepest_gauge_chart_exists`:** the `DeepestGaugeChart` structure with `chart` = the
  gauge-slice + regular-residual c-o-v (block_elimination units per layer, det-unit completion), `split`
  = `(E_reg, T-reduced, spectators)`, `nReg = r(H_0+H_last−r)`, `nGauge` = the spectator count,
  `chart_zero` (gauge origin ↦ `w0`), `hasDeriv` + `jac_unit` (the bounded-unit Jacobian), `loss_form`
  (the germ split below).
- **sub-lemma 4 `deepest_loss_in_gauge_coords`:** the germ `dlnLoss H B ∘ chart =ᶠ ∑E² + dlnLoss M 0`,
  via the 2-factor block product (regular residuals + the reduced `∏T` core, cross terms ∈ ideal(reg)
  absorbed into `E`). Uses `dlnLoss_nonneg` for the `Real.sqrt (dlnLoss M 0)` wrapper (`G := √∘dlnLoss M 0`,
  `G² = dlnLoss M 0`).
- feeds **sub-lemma 5** (`deepest_nonMP_chart_transport_unit`): `jac_unit` + `weightedThreshold_transport`
  + bounded-unit peel (NON-MP, NOT `comp_homeomorph`).

## Most likely thing to break this
The det-unit completion: the regular residuals `(E00,E01,E10)` are independent (Jacobian rank
`= nReg`), but completing them to a FULL det-unit coordinate change needs the spectator directions
(`nGauge` coords — the gauge redundancy `block_elimination`'s `P_s,Q_s` removes) to be chosen so the
total Jacobian is a unit. The gauge-fixing (`P_s,Q_s` units, `det ≠ 0`) supplies this — the gauge slice
is a transversal to the `GL_r × GL_r` gauge orbit, so the spectator block is the orbit-tangent
complement, det a unit. The one Lean-side check: the per-layer gauge units `P_s, Q_s` (from
`block_elimination`, `IsUnit`) compose into a det-unit chart Jacobian — `block_elimination` gives `IsUnit
P_s`/`IsUnit Q_s` (det `≠ 0`), and the product of units is a unit; the regular-residual c-o-v on top is
the rank-`nReg` unit block. So `jac_unit` holds, but the explicit `a, b` bounds need the compactness of a
small nbhd of `w0` (standard). [Decorrelated Codex check on the loss-form exactness + the Jacobian-unit +
the nReg fold is fired; folded when it lands.]

## Provenance
The #44 normal-form (`g147-normalform-skeleton-answer.md`, sub-lemmas 3+4), the #131/g131 pattern
(residual = smaller matrix-chain core), `block_elimination` (`Skeleton.lean:279`, the rank-r normal form),
`IsDeepLayers`/`deepestPoint` (`Skeleton.lean:502/932`). Exact algebra: `g150_gauge_chart.py` (the gauge
slice + block product), `g150_loss_form.py` (the loss-form germ + cross-term ∈ ideal(reg)), `g150_jac_fix.py`
(the det-unit Jacobian rank `= nReg`), `g150_general_r.py` (general-r + the `nReg` formula + the `r=0`
base) — all in `g129-scripts/`. NON-MP transport (`rlctAtOn_unit_invariant_aux` + germ-locality), the key
distinction from the MP/blow-up work.
