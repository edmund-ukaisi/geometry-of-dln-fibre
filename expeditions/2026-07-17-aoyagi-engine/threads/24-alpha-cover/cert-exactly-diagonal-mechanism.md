# cert — the exactly-diagonal mechanism (pnp-diag, thread 24)

**Seat**: pen-and-paper (pnp-diag), expedition 2026-07-17-aoyagi-engine. Two truth-values, one seat.
Exact `sympy` only (`/tmp/diag_mech.py`, `/tmp/q1_min.py`, `/tmp/ripple.py`); MC never used. Codex DOWN
env-wide — this seat is the sole decorrelated instrument. Pinned to `GeoAlphaGauge.lean:121-287`
(`schurCells`/`residualSchurShear`/`alphaGauge`), `GeoInvValWalk.lean:118-189` (`InvVal3` + leaf
discharge), `worked.tex:482-519` (the D_J recursion + the Q,P step), and pnp-fold's own value battery
`threads/18-fold-regroup/battery/value_threaded_verify.py` PART C.

---

## HEADLINE

- **Q1 (minimality): FULL block (option 2) is minimal; pivot-cross-only (option 3) is KILLED.** The
  Schur complement `D_{J+1} = W − b·a` reads the interior `W`, which a pivot-cross-only carry discards.
  Confirms the elder. Exact witness below. (The current Lean design — option C, expose `prod` — carries
  the full residual, so it is on the right side of this line.)

- **Q2 (the pivot-row/col mechanism): MECHANISM (ii) — `alphaGauge` is GENUINELY INCOMPLETE.** The
  interior-only Schur leaves the pivot cross `(a,b)` nonzero to the leaf, so `prod M (chartMap w)` is
  **NOT diagonal** at a leaf — already at `(2,2,2)`, with no rank-drop available. Mechanisms (i-a)
  rank-drop and (i-b) subsequent-product do **not** rescue it. `InvVal3` is FALSE at cleared rows over
  the current gauge; the four-case maintenance (task #21) is building toward an unprovable target. This
  is an `alphaGauge` **construction change** (add Aoyagi's Q,P); the ripple is assessed in §4.

This is the same gap the loss cert (`threads/19`, W1/W3) and pnp-fold's value battery already flagged at
the *math* level ("the off-diagonal needs the Q,P Schur gauge"); the new content is that the *Lean*
`alphaGauge` (`residualSchurShear`) implements only the interior Schur, not the Q,P — so the
implementation does not match what those certs said was needed.

---

## 1. Q1 — full block vs pivot-cross (exact, `/tmp/q1_min.py`)

At `(S,J)` the next residual is the Schur complement of the pivot (corner normalized to `1`):

    D_{J+1} = W − b·a,   W = interior block,  a = pivot row,  b = pivot col.

`D_{J+1}[0,0] = W[0,0] − b[0]·a[0]` reads `W[0,0]` (`= D_J[1,1]`), which pivot-cross `{a,b}` **discards**.

**Kill witness.** Two reachable `3×3` residuals with IDENTICAL pivot cross, differing only in the
interior `w11 = D_0[1,1]`:

| | cross `(a01,a02,a10,a20)` | interior `w11` | `D_1[0,0] = w11 − a01·a10` |
|---|---|---|---|
| A | `(½,0,⅓,0)` | `1` | `5/6` |
| B | `(½,0,⅓,0)` | `2` | `11/6` |

Same cross → different `D_1` → step `J+1`'s hypothesis (which reads `D_1`) cannot be established from
the cross alone. **Option 3 fails; option 2 (full block / option-C exposure) is minimal.**

## 2. Q2 — the leaf is NOT diagonal under `alphaGauge` (exact, `/tmp/diag_mech.py`)

**The Lean α is interior-only — Lean-PROVEN, not assumed.** `schurCells` (GeoAlphaGauge.lean:128-144)
targets only interior cells `a = (cleared+1+i', cleared+1+j')` (both `> cleared`), reading pivot
col `b = (·, cleared)` and pivot row `c = (cleared, ·)` as sources; `schurCells_snd_ne` (:176) **proves**
the pivot row/col coordinates pass through the whole fold **unchanged**. So `α` does `interior ↦ interior
− b·a` and leaves the pivot cross in place: the block `u·[[1,a],[b,ab+ρ]]` becomes `u·[[1,a],[b,ρ]]`, not
`u·[[1,O],[O,ρ]]`.

Faithful chart model (`geoChartMapNorm = β ∘ S ∘ α`, source→old; per-layer β blow-up scaling the block
by the pivot; α interior Schur on `node.layer`; pivot = the diagonal corner so `S = id`), then
`prod = ∏_s C^{(s)}`:

| M | interior-only α (the Lean gauge) | full Q,P (Aoyagi control) |
|---|---|---|
| `(2,2,2)` | **NOT diagonal** — off-diag `(0,1) = a0₀₀²·a1₀₀·(a0₀₁+a1₀₀a1₀₁)·(a0₀₁a0₁₀−a0₁₁)·(a1₀₁a1₁₀−a1₁₁)` | diagonal ✓ |
| `(2,2,2,2)` | **NOT diagonal** — off-diag `(0,1) ≢ 0` (factor shown in the script) | diagonal ✓ |

`(2,2,2)` has running-min width `2` at every layer ⟹ **no row ever drops** ⟹ the leaf discharge needs
ALL rows cleared (diagonal). Row `0` is cleared but carries a nonzero pivot-row entry `u·a` ⟹
`prodPrefix` off-diagonal `≠ 0` ⟹ `InvVal3`'s cleared clause (`GeoInvValWalk.lean:127`) is FALSE. This is
decisive for (ii): with no drop, nothing can save the cross.

## 3. Mechanisms (i-a)/(i-b) do NOT rescue it

- **(i-a) rank-drop — RULED OUT.** Width-drop instance `(3,2,3)` (running-min widths `[3,2,2]`), interior-α
  leaf: the CLEARED rows `0,1` carry nonzero off-diagonals, e.g.
  `(row 0,col 1) = a0₀₀²·a1₀₀·(a0₀₁+a1₀₀a1₀₁)·(a0₀₁a0₁₀−a0₁₁)·(a1₀₁a1₁₀−a1₁₁) ≠ 0` and three more. The
  drop only zeroes rows AT/BEYOND the running-min ceiling (the DROPPED rows); it never touches the pivot
  cross of a CLEARED row. So the drop-zeroing lead, while real for dropped rows, does not clear the cross.
- **(i-b) subsequent product / adjacent layer — DOES NOT APPLY to this gauge.** `residualSchurShear` reads
  and writes only `node.layer`'s flat coords; no later node's α touches an earlier step's pivot row/col
  (a later α's interior is strictly deeper), and no gauge reaches into layer `S+1`. The product's
  off-diagonal `(C^{(S)}C^{(S+1)})[0,1] = C^{(S)}_{00}C^{(S+1)}_{01} + C^{(S)}_{01}C^{(S+1)}_{11}`
  survives because β only *scales* cells (never zeroes) and α never touches `C^{(S)}_{01}` or `C^{(S+1)}`.
  (The h5 hunt chart, `threads/03-hunt/h5_composed_chart_222.py`, DID clear the pivot row by shearing it
  into the next layer `C2_00 = g0 − a·c2₁₀` — an adjacent-layer normalization the Lean `alphaGauge` does
  not implement. That is precisely the missing piece.)

**The mechanism, named precisely.** `residualSchurShear` is the **Schur-complement-of-the-interior only**
— it is the `(interior,interior)`-block of Aoyagi's `Lg` (it produces the correct next residual
`D_{J+1} = W − ba` in the interior) but omits (1) the rest of `Lg` that clears the pivot **column** `b`
within layer `S`, and (2) `Rg` entirely, which clears the pivot **row** `a` and is a **cross-layer** op
absorbed into layer `S+1`. Both omitted pieces are unipotent, det-1; their absence is invisible to the
Jacobian (`det Lg = det Rg = 1`) but not to the value.

## 4. Ripple under (ii) — concrete

`frobSq(prod) = D²·residualCore` with `D = ∏ z_divCoord` **still factors cleanly** under interior-α
(`/tmp/ripple.py`: `frobSq/(uv)² = 1 + a²bp² + … + ρ²rhop²`, exact). The failure is **only the lower
bound**: `residualCore` = `‖(product of the [[1,a],[b,ρ]] blocks)‖²` **hits 0 on the closed unit box**
(e.g. `(a,b,ρ,a',b',ρ') = (1,0,0,0,−1,0)` gives `0`; min over `{−1,0,1}⁶` is `0`) — the W3 determinantal
box-zero. Diagonalization (full Q,P) is what forces `residualCore = 1 + Σ(ratios)² ≥ 1`. Shrinking the
box does not help (the singularity is non-toric, loss cert W3); the Q,P is required.

The fix strengthens `alphaGauge` to clear the pivot cross. Concrete ripple to banked artifacts:

- **`schurCells_snd_ne` + the `elemShearFold_*` independence lemmas (GeoAlphaGauge:157-275): become
  FALSE.** They currently prove the pivot row/col are read-only; the new `Lg/Rg` WRITE the cross (and
  `Rg` writes layer `S+1`). The whole "interior cells disjoint from the pivot cross, independent shears"
  scaffold must be rebuilt (the gauge is no longer a fold of coordinate-disjoint interior shears; it is
  cross-writing and cross-layer).
- **det-1 (`residualSchurShear_abs_det_one`/`alphaGauge_abs_det_one`, :410,:427): CONCLUSION survives**
  (Lg, Rg unipotent), proof re-done for the new support.
- **srcBox bound (`residualSchurShear_srcBox`/`alphaGauge_srcBox_bounded`, :441,:484): CHANGES** — more
  shears ⟹ the preimage bound compounds beyond `R(1+R)`. pnp-cover's enlarged-cube cover (radius thread
  `ρ_{n+1}=ρ_n(1+ρ_n)`) STRUCTURE survives (finite radius per leaf, uniform `R`) but the per-node bump
  constant changes.
- **`geoAtlasNorm_leaf_leafJacobian` (walk-t20, task #5 LANDED): CONCLUSION survives** — the leaf
  Jacobian is det-based and det is blind to the det-1 Q,P; re-prove the det-1-transparency for the new
  gauge (mechanical).
- **The value lane (`GeoInvValWalk`, task #21 in progress): this is where the MATH lands.** The four-case
  maintenance is provable only with the pivot-cross-clearing gauge; over the current interior-only
  `alphaGauge` the cleared-row-diagonal step is FALSE. Statement SHAPES survive; the `α` they reference
  must be the strengthened one.
- **`(B)`-discharge (`chartBridgeFaithful_buildTree`) + `GeoAtlasTransfer`**: gauge-generic (compare
  against `gauge = id`); re-check but expected to survive.

**Net**: det-1 / cover / Jacobian CONCLUSIONS survive (Q,P is det-1; the cover is robust to a det-1
homeo); their PROOFS and the `srcBox` constant need redoing over the new gauge; the independence lemmas
become false and must be rebuilt; the VALUE lane genuinely requires the new gauge and is currently
blocked at exactly this point.

## 4b. ADDENDUM — the per-column split of row J (team-lead live input; `/tmp/q2_columns.py`)

loss-t15's per-column decomposition of row `J = s.cleared` is a sound *decomposition*, but under the
interior-only α the *disposition* is (d) for **all three** column classes, not just the live one. Key
refinement: `prodPrefix` at the state where row `J` becomes cleared is a **single transformed layer**
(`prefixColFin` covers layers `0..S`; for these instances layer `S` alone), so the live-column subcase
is testable uncontaminated.

**Live columns `J < j < running_min` — (d), cleanest at `(2,2,2)`.** Row `0`, `running_min = 2`, so `j=1`
is the ONLY off-diagonal (no cleared-cols since `J=0`, no dropped-cols since width `= running_min = 2`).
At the clearing state `(layer 0, cleared 1)`, `prodPrefix = ` transformed `C^{(0)} = u·[[1,a],[b,ρ]]`,
row `0 = [u, u·a]`, so `(0,1) = u·a ≠ 0` (exact: `−a00_0²·a00_1·(a00_1·a01_0−a01_1)`). Nonzero at the
clearing step AND at the leaf. This is a *pure* live-column test, and it is (d):
- **(a) blow-up structural-zero — NO.** Pre-α (pure β) `(0,1)` is already nonzero; β only scales.
- **(b) bmon absorbs — NO.** `(0,1) = a·(0,0)` is proportional to the diagonal value but sits at a genuine
  off-diagonal position `(0,1)`; `InvVal3`'s cleared-clause (`i≠j ⟹ =0`) is violated by `a·bmon ≠ 0`.
- **(c) eventually drops / clearedOf retiming — NO.** In `(2,2,2)` `running_min = 2` is constant, so
  `j=1` never drops and `(0,1)` is nonzero at the leaf. In general the immediately-super-diagonal live
  column `j = J+1` persists whenever `running_min > J+1`, and (see below) the drop-zeroing itself needs
  the full Q,P. Retiming `clearedOf` does not rescue it.
- **(d) needs `Rg = [[1,−a],[0,1]]` — CONFIRMED.**

**Cleared columns `j < J` — ALSO (d) (needs `Lg`), contra the "already 0" assumption.** The interior-α
clears NO pivot column (`Lg` is the omitted part). `(4,3,4)`, row `1`: `(1,0)` NONZERO at both the
clearing step (`prodPrefix = C^{(0)}`) and the leaf. So the cleared-column entries are *not* zero from
prior clearing — they need `Lg`.

**Dropped columns/rows `j ≥ running_min` — ALSO (d) (no column-drop under interior-α).** `(4,3,4)`
(`running_min 3`, full width `4`), row `1`: `(1,3)` NONZERO at the leaf. And the dropped-ROW clause
fails: row `3` has nonzero entries (`rank(prod) = 3`, so row `3` is a linear combination of rows `0–2`,
NOT a zero row). The "dropped = 0" of the three-state `InvVal3` is a consequence of the full Q,P
normalization (as the `clearedof_walk_trace.py` battery's `clear_pivot` = full row+col reduction
encodes); under interior-α rank deficiency shows up as linear dependence, not zero rows.

**Net for the split:** live-col = (d), cleared-col = (d, needs `Lg`), dropped-col/row = (d, the
drop-zeroing needs full Q,P). The entire off-diagonal of row `J` (plus the dropped-row zeroing) requires
Aoyagi's Q,P; the interior-only α produces neither the diagonalization nor the drop-zeroing. This is the
largest-ripple branch (d), and it confirms the §4 fix (`alphaGauge → Q,P`) is necessary in full, not a
corner patch.

## 5. Close

- **Firmest result**: (Q1) full block minimal / pivot-cross-only killed — exact witness §1. (Q2)
  mechanism (ii): `alphaGauge` = interior-only Schur is genuinely incomplete; `prod` is not diagonal at
  a `(2,2,2)`/`(2,2,2,2)` leaf (exact off-diagonals §2), no-drop so nothing rescues it; (i-a)/(i-b) do
  not clear the cross (§3). `frobSq` still factors `D²·residualCore`, but `residualCore` vanishes on the
  closed box (§4) — the lower bound needs the diagonalizing Q,P.
- **Most likely to break the verdict**: a re-reading in which `residualSchurShear` is meant as the whole
  Q,P rather than the interior Schur — ruled out by `schurCells`'s interior-only targets and the
  `schurCells_snd_ne` proof (the pivot cross is Lean-PROVEN read-only). A second: the leaf discharge only
  needing `D`-factoring (not full diagonality) — ruled out because the lower bound then fails on the
  closed box (§4).
- **Next construction step this points to**: strengthen `alphaGauge` to Aoyagi's Q,P — a same-layer col
  clear (`Lg`, subsuming the current interior update) plus a **cross-layer** row clear into layer `S+1`
  (`Rg`, the h5 shape). This is the reshape the loss/value lane needs; the four-case InvVal3 maintenance
  should be paused until the gauge is corrected (it cannot close over the current one). (Codex skipped —
  down env-wide.)
