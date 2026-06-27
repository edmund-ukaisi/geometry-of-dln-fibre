# Certificate — the achiever-chart decoder DET fix (R1-lower atom ∀M)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. **Direction:** witness — exhibit the corrected
chart shape that separates "produces both rate `(x_p)²·U` and det `|x_p|^{minAdm−1}` in ONE chart" from
the current decoder's failure. **Decorrelated Codex:** `codex/decoder-fix-{prompt,answer}.md` (xhigh,
independent — confirms every load-bearing point below).

All algebra here is exact (sympy symbolic / integer); no floats are load-bearing.

---

## 1. VERDICT on the wall — CONFIRMED, and STRICTLY WORSE than "off by one"

The formaliser's wall is real. But the current decoder's flat-map Jacobian is **identically zero**, not
`|x_p|^{minAdm}`. Two independent defects, each alone fatal:

**(D1) Dead leaf slots ⟹ rank-deficient ⟹ `det Dφ ≡ 0` (decoder-structural, every chain).**
`genBlkFlatStruct` has `Rfin := fun _ => 0`, and the chain engine's leaf transition is `C_L = u • Rfin L`
(`Cgen` at `k = L`, `RouteMGenChain.lean:91`). So `C_L = 0`. Separately, the `chartIdxEquiv` role-slot
`schurDim (L−1)` (the boundary-`s=L` Schur frame) feeds `readK/X/N/E` at `k = L−1`, which the decoder
assembles into `Bmat L`, `Nblk L`, `Rmat L` — and `Cgen`/`Agen` (`RouteMGenChain.lean:87,94`) only read
indices `k < L`. So those slot coordinates **never appear in any output entry**. Their count is
`schurDim (L−1) = Text L · Wext L = Text(L) · M(L) ≥ 1` for any genuine chain. After a column permutation
the Jacobian is `[ * | 0_{N × r} ]` with `r = Text(L)·M(L) > 0`, hence `rank Dφ ≤ N − r < N` and
`det Dφ = 0` **identically**, including off `{x_p = 0}`. (Sympy-exact for (2,2,2) `t=(2,1,1)`: the 8×8
Jacobian has 2 zero columns ⟹ det 0; `/tmp/jac_full_222.py`. Generic count `/tmp/unused_slots.py`.)

**(D2) No fixed-1 pivot slot ⟹ even ignoring D1, the "all-residual-free" block gives `u^{m}` (×2), never
`u^{m−1}`.** The proper achiever blow-up is `(u, z₁,…,z_{m−1}) ↦ (u, u·z₁,…,u·z_{m−1})`, with the pivot a
DISTINCT slot mapping to itself and scaling a FIXED residual entry `= 1`. Det `= |u|^{m−1}` (the pivot row
contributes the diagonal `1`, the `m−1` active non-pivot rows each contribute `u`). The current decoder
scales the residual `E`-entries by `u•Rmat` with NO fixed-1 / no distinct pivot column: if you treat all
`m` residual entries as free and set `u = e₁`, you get `(e₁,…,e_m) ↦ (u·e₁,…,u·e_m) = (u², u·e₂,…)`, det
`2u^m` (Codex Q2). The clean `|u|^{m−1}` is unreachable without the fixed-1 slot.

So the formaliser's "`|u|^{minAdm}`, off by one — or malformed" reading is directionally correct on the
*mechanism* (the `u•Rmat`-only structure cannot give `u^{m−1}`); the *value* is `det ≡ 0` (D1 dominates).
**A green build of any "det = `|u|^{minAdm−1}`" claim on this decoder would be false.** The wall holds.

`pivotBlowupOnDeriv_det` (`S1G5Charts.lean:509`) is exactly the correct mechanism, and it is already
banked: `det (pivotBlowupOnDeriv active p x) = (x p)^{active.card − 1}`, with `pivotBlowupOn` keeping the
pivot coord as itself (`S1G5Charts.lean:384,393` — `if i = p then proj p`). The decoder simply does not
route through it for the chart's radial direction.

---

## 2. THE CHOSEN FIX — option (C): full-rank decoder + a SEPARATE radial `pivotBlowupOn` factor

Neither (A) nor (B) as the brief framed them is right unmodified:

- **(B) as literally stated FAILS.** "Keep `genBlkFlatStruct` UNTOUCHED and compose a radial factor" cannot
  work: `det D(S ∘ R) = det DS(R(x)) · det DR(x)`. `S = genBlkFlatStruct`-decode is ALREADY degenerate
  (D1: `det DS ≡ 0`), so the product is `0 · (anything) = 0` (Codex Q3). You cannot rescue a rank-deficient
  decoder by post-composing a blow-up.

- **(A) is algebraically valid but heavier and re-opens the rate engine.** Baking a fixed-1 pivot column +
  a nonzero `Rfin` (with a designated constant `= 1` entry) into the chain decoder works — the rate stays
  safe (the banked `chain_telescope_zero` extracts exactly ONE `u` from the whole telescoped suffix
  regardless of how many `u•Rmat`/`u•Rfin` terms carry `u`, so `prod = u·H`, `F = u²·V` — `/tmp/leafcheck.py`).
  But it requires re-deriving `C0_eq_one`/`hC0` for the altered leaf, threading a fixed-1 entry through the
  dependent-width `rmatPad`/`bmatStack` algebra, AND it still must separately kill the dead `schurDim(L−1)`
  slot (give it to the blow-up or drop it). Larger blast radius, and it entangles the rate proof.

- **(C) — the validated template, generalised.** Build the chart as
  `φ = Q_fullrank ∘ pivotBlowupOn(active, p)`, where:
  - `pivotBlowupOn(active, p)` is the SEPARATE radial factor (already a banked `ChartFactor`:
    `radialFactor`, `RouteMRadialFactor.lean:33`), with `active` the `m = minAdm` normal coords (pivot `p`
    + `m−1` free actives) and det `|x_p|^{minAdm−1}` (`radialFactor_abs_det`).
  - `Q_fullrank` is a structured decode-and-pack that is FULL RANK: NO unused flat slots, NO `x_p`
    double-duty, the pivot a distinct slot scaling a fixed-1 residual entry, the layer-ops (Schur shear,
    LDU, `b=aβ` substitution) supplied as their OWN `pivotBlowupOn`/linear `ChartFactor`s contributing
    spectator monomials (on `k=0` axes — they do not lower the threshold).

  This is **literally what both banked anchors do** and what the factor-fold infrastructure (`composeFold`,
  `composeFold_abs_det`, `phiTarget_abs_det_of_factored`, `radialFactor`, `linearFactor`) was built for:
  - `(4,4,2,2)` (pure radial, `minAdm=4`): `phi4422 = composeFold [linearFactor Q4422CLM, radialFactor
    {0,1,2,3} 0]`, `|det| = |u 0|³ = |u 0|^{minAdm−1}` (`RouteM4422Bridge.lean:32,62`). `Q4422CLM` is LINEAR,
    full-rank, `|det| = 1`; the radial supplies both the loss's `u²` (`A2 = u₀·M̄₂`) and the det `u₀³`.
  - `(3,3,4)` (genuine layered Schur, `minAdm=8`): `T334 = bsubst334 ∘ shear334 ∘ pb334`
    (`RouteMLayerCoverGEL2.lean:738`), `|det Dφ| = |u 0|⁷·|u 1|²`: `pb334 = pivotBlowupOn {0,6..12} 0`
    gives `|u 0|^{8−1}=|u 0|⁷` (the radial, `minAdm−1`); `bsubst334 = pivotBlowupOn {1,2,3} 1` gives the
    spectator `|u 1|²` (the `b=aβ` layer-op); `shear334` is det-1 unitriangular. The pivot scales the
    fixed-1; the layer-ops each carry their own monomial.

  **Why (C) over (A):** the rate proof (`routeMCore_phiFlatStructV`, banked ∀M via the decoder-agnostic
  `routeMCore_phiGen`) is consumed by `composeFold`-side reasoning unchanged IF the chart is `composeFold`'d
  in a way whose `paramsEquivFlat.symm`-image reproduces the chain layers — but the cleanest path is the one
  the anchors took: prove `phi = composeFold fs` for the explicit per-case factor list, get the rate from the
  loss factorization on the packed `Params` (as `dlnLoss_chartParams4422`/`prod_chartParams4422_entry`), and
  get the det from `phiTarget_abs_det_of_factored` + the per-factor `radialFactor_abs_det`/`linearFactor_abs_det`.
  No chain-engine surgery; the degenerate `genBlkFlatStruct` is simply NOT the chart (it served only to bank
  the rate identity, which transfers).

**The decision: option (C).** The radial `pivotBlowupOn` (det `|x_p|^{minAdm−1}`) is a SEPARATE factor; the
decode/pack `Q` must be FULL-RANK (the current `genBlkFlatStruct` is not — it is rate-only scaffolding).

---

## 3. THE CONCRETE CORRECTED CHART (formaliser-implementable precision)

The chart for a general achiever node `M` (with `hpos : 1 ≤ minAdm M`), at the achiever descent path `t`:

    φ_M := Q_M ∘ ( bsubstₖ ∘ … ∘ shearₖ ∘ … ∘ radial )       (composeFold, deepest-first)

with the factor list (each a banked `ChartFactor (routeMAmbient M)`):

1. **`radial := radialFactor active p`** — `active = the m = minAdm normal coords`, `p` the pivot.
   - The pivot `p` maps to ITSELF (`pivotBlowupOn … p`: `if i = p then x p`), scaling the FIXED-1
     residual entry of the deepest rank-deficient factor.
   - The `m−1` other actives map `x_j ↦ x_p · x_j` (the free angular directions).
   - `radialFactor_abs_det` gives `|det| = |x_p|^{active.card − 1} = |x_p|^{minAdm − 1}`. ← the binding
     exponent `leafH_pivot : leafH p = minAdm M − 1`.

2. **layer-op factors** (one per interior Schur/LDU boundary with `r_k ≥ 1`): each a
   `pivotBlowupOn(active_k, p_k)` (the `b=aβ`-style substitution, det `|x_{p_k}|^{r_k·c_k − …}`, a SPECTATOR
   monomial on a `k=0` axis) and/or a det-1 unitriangular `shear`/`linearFactor` for the Schur frame /
   chainA reassociation. These carry the GENUINE spectator monomials of `leafH` (the `(3,3,4)` `|u 1|²`
   pattern; Codex-confirmed they are real, on `k=0` axes so the threshold stays `½·minAdm`).

3. **`Q := linearFactor Q_M_CLM`** — the LINEAR, full-rank, measure-preserving pack
   `paramsEquivFlat ∘ pack_M` (det `±1`), reshaping the blown-up flat coords into the `Params M` layer
   slots. `linearFactor_abs_det` + `…_abs_det_eq_one_of_measurePreserving` (the `Q4422CLM`/`Q334CLM`
   pattern). **This replaces the degenerate `genBlkFlatStruct` decode.** It MUST be a genuine bijection on
   the flat coords (every input coord lands in some output entry — no `Rfin=0` dead slots).

**Det assembly** (the banked telescope): `|det Dφ_M| = ∏ (per-factor |det|) = |x_p|^{minAdm−1} ·
∏_k (spectator monomials) · 1 = ∏_j |x_j|^{leafH j}` via `phiTarget_abs_det_of_factored`
(`RouteMPhiTargetDet`) + `composeFold_abs_det`.

**Rate** (`(x_p)²·U`): comes from the loss factorization on the PACKED `Params` — the deepest factor is
`u·(fixed-1 ⊕ angulars)`, so `prod = u·H` (the chain telescope's single `u`), `F = u²·‖H‖²`. Established
the way `dlnLoss_chartParams4422` is, or transported from the banked `routeMCore_phiFlatStructV` THROUGH the
`composeFold = φ` bridge (the `paramsEquivFlat.symm`-image reproduces the chain layers). The `u²` originates
in the DEEPEST FACTOR scaling a fixed-1 residual by `u`, NOT in the radial-factor's coordinate scaling — the
two `u`-powers (`u²` rate vs `u^{minAdm−1}` det) are DIFFERENT mechanisms (loss vanishing-order vs Jacobian),
both correct, and the chart carries both consistently because the deepest factor `= u·(1, angulars)` simultaneously
(a) makes the product divisible by exactly one `u` (rate) and (b) is the pivot-row-of-1 in the blow-up (det).

**Decoder-agnostic interface preserved:** `routeMCore_phiGen`/`routeMCore_phiFlatStructV` consume only
`GenBlk`/`hle`/`hC0` — `hC0` is re-checkable for the full-rank pack (identity boundary `Bmat 0 = I`,
`Rmat 0 = 0`, `c_0 = 0`). The rate engine does not read the chart's coordinate map, so the fix touches only
the det/cov side.

---

## 4. WORKED CROSS-CHECK

### 4a. The brief's (2,2,2) `t=(2,1,1)` anchor — a CAUTION the formaliser MUST heed

**`minAdm M222 = 3`** (Aoyagi layer-peel: `min_t [(2−t)(2−t) + minAdm(t,2)]`, min at `t=1`: `1 + 1·2 = 3`;
verified `/tmp/minadm_correct.py`, Codex Q4 independently). So (2,2,2) IS a valid node (`hpos: 3 ≥ 1`).

BUT the anchor's path `t222 = (2,1,1)` gives `Text = [2,2,1,1]`, whose per-boundary "chain codim"
`∑ₖ (Textₖ − Text_{k+1})(M_k − Text_{k+1}) = 0 + (1)(1) + 0 = 1`. **1 ≠ minAdm = 3.** (Both numbers exact;
Codex Q4 agrees.) So `t222 = (2,1,1)` is **NOT the achiever path** — its center has codim 1, not 3.

**Consequence the formaliser must not miss:** for this path the radial blow-up has `m = 1`, so
`leafH_pivot = m − 1 = 0`, which CANNOT equal `minAdm − 1 = 2`. Building a `NodeAchieverChart M222` from
`t222 = (2,1,1)` would VIOLATE `leafH_pivot : leafH p = minAdm M − 1`. The (2,2,2) `t=(2,1,1)` anchor is a
fine validate-small for the **rate / decoder-machinery** (I verified `prod = u·H`, `F = u²·V` exactly on it
— `/tmp/chain_222b.py`: `prod = u·[[0,0],[e₁w₀, e₁w₁]]`), but it is **NOT a valid validate-small for the DET
identity `|det Dφ| = |x_p|^{minAdm−1}`** — the path codim disagrees with `minAdm`. Use it only for the rate;
pick a path with chain-codim `= minAdm` for the det.

(The chain `Text`-path ↔ `minAdm`-codim correspondence is non-trivial — the naive per-boundary `∑ r_k c_k`
does not realize `minAdm` for any of the banked anchors either; `/tmp/achiever_path.py`. Pinning the exact
achiever `Text` from the Aoyagi peel is a separate lift, NOT this certificate's scope. Flagged as a
kill-condition below.)

### 4b. A VALID layered cross-check — `M = (2,2,1)`, `minAdm = 2` (the fix, end-to-end, exact)

The smallest genuinely-layered node where the corrected chart is full-rank. `minAdm(2,2,1) = 2`
(`min_t[(2−t)² + t·1]`, min at `t=1` or `t=2`: `2`). `N = M₀M₁ + M₁M₂ = 4 + 2 = 6`. `F = ‖A₀·A₁‖²`,
`A₀ : 2×2`, `A₁ : 2×1`.

**The corrected chart (option C):**

    A₁ = [[u₀], [u₀·u₁]]      (deepest factor: entry (0,0)=u₀ scales the FIXED 1; entry (1,0)=u₀·u₁ active)
    A₀ = [[u₂,u₃],[u₄,u₅]]    (free spectators; identity in the flat map)

i.e. `pivotBlowupOn {0,1} 0` on the `A₁`-slot coords (pivot `p=0`, one active coord `1`; `active.card =
m = 2`) ∘ a linear full-rank pack. Identify: **pivot `= u₀` (axis 0); fixed-1 residual = `A₁(0,0)`'s `1`;
the `m−1 = 1` active free coord = `u₁`; spectators = `u₂..u₅`.**

**RATE** (sympy-exact, `/tmp/crosscheck_221.py`):
`P = A₀·A₁ = u₀·[[u₂ + u₁u₃], [u₄ + u₁u₅]] = u₀·H` (H is u₀-free), so

    F(φ) = ‖P‖² = u₀² · U,   U = u₁²u₃² + u₁²u₅² + 2u₁u₂u₃ + 2u₁u₄u₅ + u₂² + u₄²   (u₀-free). ✓ matches (x_p)²·U.

**DET** (sympy-exact): the flat map `(u₀..u₅) ↦ (u₂,u₃,u₄,u₅, u₀, u₀u₁)` (the 6 entries of `A₀, A₁`) has

    |det Dφ| = |u₀|¹ = |u₀|^{minAdm − 1}   (minAdm = 2). ✓

The `m−1 = 1` active coord `u₁` is scaled by `u₀`; the pivot `u₀` maps to itself (the fixed-1 row); the 4
spectators are identity. Pivot exponent exactly `minAdm − 1 = 1`. Both rate `u₀²` and det `u₀¹` hold in ONE
chart, by the DIFFERENT mechanisms (the single deepest `u₀` for the rate; the `m`-coord blow-up for the det).
This is the (4,4,2,2) spine on a layered node, exactly the corrected shape §3 prescribes.

---

## 5. KILL-CONDITIONS / RESIDUAL RISK for the formaliser

1. **(Most likely to bite) The achiever `Text`-path ↔ `minAdm` arithmetic.** This certificate does NOT
   pin the exact achiever descent path that realizes `m = minAdm` as a chain `Text` sequence. The naive
   per-boundary `∑ r_k c_k` does NOT equal `minAdm` for any banked anchor — the Aoyagi peel and the chain
   stratification are different parametrizations. Before assembling `nodeChartGeneral M`, the controller/
   formaliser must establish: *the achiever path's blow-up `active.card = minAdm M`* (so
   `leafH_pivot = minAdm − 1` holds). KILL if no path gives `active.card = minAdm` — but the banked anchors
   (4422: 4, 334: 8) prove such a path exists per case; the ∀M version is the open lift.

2. **The full-rank pack `Q_M` for general `M`.** The `(4,4,2,2)`/`(3,3,4)` `pack`/`Q…CLM` are HAND-BUILT
   per case (explicit `Fin N ≃ FlatIdx` tables, `decide`-checked). The ∀M version needs a full-rank
   structured pack over opaque `Text`/`Wext` widths with NO dead slots — the genuine remaining
   dependent-width build. RISK: reproducing the dead-slot bug (D1) at the general width algebra. Guard:
   prove `Q_M` is a bijection (measure-preserving) BEFORE trusting its det.

3. **Spectator-monomial bookkeeping (`leafH`).** The layer-op factors (Schur shear det 1; `b=aβ`/LDU
   substitutions) carry GENUINE spectator monomials on `k=0` axes (the `(3,3,4)` `|u 1|²`). `leafH` must
   carry them; only `leafH p = minAdm − 1` is threshold-relevant (Codex-confirmed). RISK: dropping a
   spectator power breaks `composeFold_abs_det = ∏|u_j|^{leafH j}`. The det must telescope to the FULL
   product, spectators included.

4. **The rate bridge under the new chart.** §3 transports the rate either by a direct loss factorization on
   the packed `Params` (the `dlnLoss_chartParams4422` route — cleanest per-case) or through
   `routeMCore_phiFlatStructV` + `composeFold = φ`. The banked rate is decoder-agnostic, so it survives, BUT
   `hC0` (the identity boundary `C 0 = 1`) must be re-checked for the full-rank pack — it reads only
   `Bmat 0 = I`, `Rmat 0 = 0`, `c_0 = 0`, all preserved (`C0_eq_one_gen`, `RouteMFlatStructV.lean:42`).

---

## Structure & ideas observed (data, not a Lean route)

- **The two `u`-powers are NOT a contradiction — they are orthogonal invariants.** Rate `u²` = the loss's
  vanishing order along the radial ray (set by the deepest factor carrying exactly one `u`, squared by the
  Frobenius norm). Det `u^{minAdm−1}` = the blow-up Jacobian exceptional-divisor power. The SAME deepest
  factor `= u·(fixed-1, angulars)` realizes both: it makes `prod` divisible by one `u` (rate) AND is the
  pivot-1 row of the `m`-coordinate blow-up (det). Any correct achiever chart MUST tie them through this one
  object — which is exactly why a separate radial factor over a degenerate decoder cannot work.

- **The current `genBlkFlatStruct` is rate-only scaffolding, and that is fine.** It correctly banked the ∀M
  rate identity (`routeMCore_phiFlatStructV`) via the decoder-agnostic engine. Its degeneracy as a *chart*
  is not a regression to undo — it should simply NOT be the chart's coordinate map. The det/cov needs the
  full-rank factor-composition (§3), and the rate transfers.

- **The `pivotBlowupOn` family is the universal achiever brick.** Both anchors are pure compositions of
  `pivotBlowupOn`/linear/shear `ChartFactor`s. The radial is `pivotBlowupOn(m-coords, p)` (det `u^{m−1}`);
  every layer-op is another `pivotBlowupOn`/shear (spectator monomial / det 1). The general chart is a
  per-boundary fold of these — the design space is "which coords are active at which boundary," and the
  invariant is `active.card = minAdm` at the radial.

**Firmest result:** the current decoder's `det Dφ ≡ 0` (D1, triple-confirmed: hand, sympy, Codex); the fix
is option (C) — full-rank pack + separate `radialFactor`, the validated `(4,4,2,2)`/`(3,3,4)` template;
cross-checked end-to-end exact on the layered `M=(2,2,1)` (`minAdm=2`): rate `u₀²·U`, det `|u₀|¹=|u₀|^{minAdm−1}`.
**Most likely to break it:** the achiever-`Text`-path ↔ `minAdm` arithmetic (kill-condition 1) and
reproducing the dead-slot bug in the general full-rank pack (kill-condition 2). **Next construction that
settles the open part:** pin the achiever descent `Text` path with `active.card = minAdm` ∀M (the Aoyagi
peel → chain-path bridge), then build the full-rank `Q_M` pack and verify it is a bijection before its det.
