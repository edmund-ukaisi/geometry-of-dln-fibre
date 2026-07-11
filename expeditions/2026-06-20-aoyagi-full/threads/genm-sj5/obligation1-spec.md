# Obligation-1 pre-audit spec — the per-block codim allocation for `g_le_qPeelIntegral_on_cell` (b2)

**Seat:** pen-and-paper (pre-derivation of the soundness gate's audit target). **Date:** 2026-07-11.
**NO Lean.** **Decorrelated:** derived ONLY from banked certs (`prodD-general.md` #127, `corankq-cert.md`
#131, `qpeel-soundness-cert.md` #133, `onePeel334` banked header, `qPeel_threshold_eq_half_minAdm_334`
anchor) — did NOT read genm-sj5-schur's `(b2)` code. **Exact algebra (mine):** `/tmp/prodD/oblig1.py`.
**Purpose:** this is the comparison-target for the obligation-1 audit at `(b2)`'s close: when
`g_le_qPeelIntegral_on_cell` lands, compare its actual `(h, m)` allocation against §1 and run the §3
checklist.

The abstract `qPeelIntegral_lt_top` is sound (PASS, #133). Its soundness for the ACTUAL (□) rests on
`(b2)` casting the DLN chart into the abstract interface with the CORRECT per-block `(h_i, m_i)`. This
spec derives what that allocation must be.

---

## 1. The allocation — per collapse direction (anchored + the general principle)

For a corank-`q` cell (collapse set `S`, `|S|=q`), the two per-block vectors `h, m : Fin q → ℕ`:

**`h_i + 1` = the `i`-th nonzero per-boundary charge of the binding rank-branch** (`Mval_decompose` /
`sjChargeBudget_le`). For the binding branch `T` (`T_{−1}:=M₀`), `charge_j = (T_{j−1}−T_j)(M_{j+1}−T_j)`;
the nonzero charges, indexed by collapse direction, are `h_i+1`. **`Σ_i(h_i+1) = minAdm(M)`** (the total
= the codim), so the threshold `c' < ½·Σ(h_i+1) = ½·minAdm` — the ADD (#131).

**`m_i + 1` = the dimension of the deep-data slice collapse direction `i` reads** (the free block `X_i` in
the clean-coordinate casting; `onePeel334`: `U_i = ‖X_i‖²`). It is the **per-direction** product-rank
codim of that direction (#127) — each direction its OWN codim.

**Anchor `(3,3,3,4)`, `t=1`, `q=2` (verified `oblig1.py`):**
- binding branch `T=(1,0,0)`, charges `[(3−1)(3−1), (1−0)(3−0), 0] = [4,3,0]` → nonzero `h+1 = [4,3]`,
  `h = ![3,2]`; `Σ(h+1) = 7 = minAdm(3,3,3,4)`, threshold `7/2 = ½·minAdm` ✓ (`qPeel_threshold_eq_half_minAdm_334`).
- deep dims `m+1 = [8,4]` (`m = ![7,3]`): `onePeel334`'s row-blocks `rows_i × M_last = (M₀−t, t)×M_last =
  (2,1)×4 = (8,4)`, which coincide with `#127`'s `D_prod = (8,4,1)` truncated to `q=2`.
- **gate `h_i+1 ≤ m_i+1`: `(4≤8, 3≤4)` ✓** (slack; the threshold binds at the u-charges `[4,3]`, the deep
  blocks are non-binding).

**Why the gate holds (geometric source):** the deep slice reads the FULL deep width `M_last` (`m_i+1 =
rows_i × M_last`), while the corner charge uses a REDUCED width `≤ M_last` (`h_i+1 = rows_i ×
(reduced width)`) — so `m_i+1 ≥ h_i+1` per direction. Equivalently, the per-direction PRODUCT-rank codim
`≥` the corner charge (#127 + `Mval_decompose`).

---

## 2. ★ The load-bearing subtlety — the allocation must be MATCHED per-direction (a concrete failure witness)

A naive allocation can VIOLATE the gate even when finiteness is true. **Concrete witness (`oblig1.py`,
`(3,3,3,3,4)`, a 3-layer deep product):** binding charges `[1,2,3,0]` → `h+1 = [1,2,3]`, `Σ=6=minAdm`,
threshold `3`. A naive **branch-order** allocation `m_i+1 = D_prod(i) = minAdm(reduced by i−1) = [7,3,1]`
pairs `(charge, dim) = (1,7),(2,3),(3,1)` — **direction 3 VIOLATES: `1 < 3`.** Yet the true integral is
finite (`minAdm=6`). The resolution: the deep dims and charges must be **matched by magnitude** (large
charge ↔ large deep-slice codim); the correct matching `[1,2,3] ≤ [1,3,7]` (sorted) holds. So:

> The per-block `m_i` is the dim of the slice THAT direction reads — a MATCHING determined by the geometry,
> NOT a flat branch-order list, NOT a total, NOT a uniform max. A wrong matching gives `min(h_i+1, m_i+1) =
> m_i+1 < h_i+1` for the deficient block ⟹ the joint threshold `½·Σ min(h_i+1,m_i+1) < ½·minAdm` ⟹ the
> RLCT-collapse (finiteness fails below `½·minAdm`, #131/#133 Q2).

**Multi-layer deep products** (`L≥4`, deep = `A₁···A_{L−1}` a genuine product): `qPeelIntegral` is applied
**per descent level** (immediate corank block vs immediate deep factor), NOT as a single flat `q`-block
with branch-order `D_prod` — the chain-length descent (B5-desc) supplies the per-level per-direction dims.
The `(3,3,3,3,4)` naive violation is the SIGN that a flat single-`qPeelIntegral` allocation is wrong for
multi-layer; the descent is required. (The `(3,3,3,4)` anchor is `q=2`, and the casting is `onePeel334`'s
single clean-coordinate step — no descent needed there.)

---

## 3. The obligation-1 CHECKLIST — the soundness predicate `g_le_qPeelIntegral_on_cell` must satisfy

When `(b2)` lands, verify ALL of:

1. **Per-direction charges `h_i`:** `h_i+1` = the binding branch's nonzero per-boundary charges
   (`Mval_decompose`), `Σ(h_i+1) = minAdm(M)`. (Anchor: `![3,2]`, `Σ+2 = 7`.)
2. **Per-block deep dims `m_i`, MATCHED:** each collapse direction `i` carries the dim of ITS OWN deep
   slice `X_i` (the coordinates `U_i` reads), with **`m_i ≥ h_i` PER BLOCK** — the matched per-direction
   product-rank codim (#127). **NOT** an unallocated total `D_q` split arbitrarily; **NOT** a uniform
   `max_i`; **NOT** a flat branch-order `D_prod` (which violates — §2). (Anchor: `![7,3]`, `(8,4)≥(4,3)`.)
3. **Additive loss, correct direction:** `g(Q)` (the cell's front integral) `≤ qPeelIntegral` via
   `frobSq(A₀·Q) ≍ Σ_i u_i²‖X_i‖²` (the ADDITIVE form, block `i` = `X_i`), the LOWER bound on the loss
   (upper bound on `g^{−c'}`) — NOT `radialAttach` (multiplicative → `min→3/2`).
4. **Full product rank + bounded-Jacobian CoV:** the deep-data map `A → (X_i)_i` has full product rank and
   a bounded-Jacobian (measure-comparable) change of coordinates to Lebesgue on `∏_i [−T,T]^{m_i+1}`.
5. **Zero-loss locus joint-null:** `{Σ_i u_i²‖X_i‖² = 0}` is joint-null (no identically-vanishing block) —
   so the rpow-0 convention is harmless (#133 Q3/Q4 obligation-2).
6. **Multi-layer via descent:** for a genuine deep product (`L≥4`), the cast is per descent level, not a
   single flat `q`-block (§2).

**Failure modes (what a WRONG allocation looks like):**
- **TOTAL** (`Σ m_i ≥ Σ h_i = minAdm` but some `m_i < h_i`): the deficient block's deep-Morse integral
  diverges (`2w_ic' → h_i+1 > m_i+1`), the joint threshold drops to `½·Σmin(h_i+1,m_i+1) < ½·minAdm` — the
  RLCT-collapse. This is the `7/2-not-9/2` / product-vs-free failure surfacing as a per-block deficit.
- **MAX** (uniform `m_i = max_j(m_j+1)−1`): the gate trivially holds, but the allocation mis-represents the
  ACTUAL deep-slice dims; if the real slice `i` is smaller (`< h_i+1`), the theorem is applied to the wrong
  geometry (sound theorem, false instantiation — #133's "artificially choose large `m_i`" trap).
- **WRONG MATCHING** (branch-order flat `D_prod`): violates at multi-layer (`(3,3,3,3,4)`, §2), a false
  divergence in the bound (the correct matched allocation is finite) — signals the descent is needed.

---

## 4. Close

- **The allocation (audit target):** `h_i+1` = binding-branch per-boundary charges (`Mval_decompose`,
  `Σ=minAdm`); `m_i+1` = the MATCHED per-direction deep-slice codim (`onePeel334` row-blocks `rows_i ×
  M_last`, `= #127 D_prod` per direction). Anchor `(3,3,3,4)`: `h=![3,2]`, `m=![7,3]`, gate `(4,3)≤(8,4)`,
  threshold `7/2=½minAdm`. Verified `oblig1.py`.
- **The soundness predicate (the checklist §3):** per-block `m_i ≥ h_i` MATCHED (each its own codim), NOT
  total / max / branch-order-flat. The `(3,3,3,3,4)` witness (§2) shows a naive allocation violates ⟹ the
  matching is load-bearing and must be verified against the ACTUAL casting.
- **When `(b2)` lands:** hand me its `(h, m)` allocation + the `frobSq ≍ Σ u_i²‖X_i‖²` comparison; I check
  (i) `h_i+1` = binding charges (`Σ=minAdm`), (ii) `m_i ≥ h_i` per block against the actual deep slices
  (not a total/max), (iii) the additive-loss direction, (iv) joint-null zero-loss, (v) descent for
  multi-layer. If the casting supplies the matched per-direction dims, PASS; if it lumps a total or picks a
  max or uses branch-order `D_prod`, the precise deficient block is the issue.
- **Not a wall.** The correct matched allocation always exists (the deep data has `Σ m_i+1 = dim ≫ minAdm`,
  and each direction's slice `≥` its charge geometrically); the audit is to confirm `(b2)` USES it, not a
  shortcut. This is the conceptual-slop gate (bedrock): a sound abstract theorem applied to the right
  geometry.
