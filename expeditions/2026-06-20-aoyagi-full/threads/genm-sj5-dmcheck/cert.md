# D/m ≥ n₀ general-width collapse hunt — OBSTRUCTION catalogue (no collapse) + the forcing reason + 3 misread traps

**Seat:** pen-and-paper (WITNESS seat, adversarial — genm-sj5-dmcheck, task #146). **Date:** 2026-07-11.
**NO Lean.** **Charge (team-lead):** hunt for a nondegenerate DLN deeper-chain + a binding rank-drop
branch of its decorated (S,J) resolution where `D/m < n₀` — a genuine collapse making `λ < ½·minAdm`
(⟹ (□) false / decomposition unfaithful). Sweep beyond the anchor `(3,3,3,4)`: the bottlenecked chains
`(3,5,2,5),(2,4,2,5),(2,4,4,5),(2,5,2,2,5)`, corank-2/3 cuts, `L=3,4,5`, adversarial branches.

**Exact algebra (mine):** `/tmp/dmcheck/{master,binding_diag,vanishing_order,jac_codim,jac_codim2,
verify_codex,final_checks}.py` (linchpin sweep; binding-cut db2 diagnostic; symbolic vanishing order on a
bottleneck; Jacobian-rank tube codim on single/double/triple bottlenecks; q=3 corner-ADD; view
reconciliation). **Consumed (banked):** `stephyp-intersection-cert`, `corank2-cert`, `prodD-general`
(#127), `transversality-recursion` (§1 the corank-block full-row-rank lemma, §8 back-peel). **Decorrelated:**
own xhigh `local-codex-consult`, conclusion WITHHELD, told to HUNT the collapse (`codex/dmcheck-{prompt,
answer}.md`). **Codex EARNED its keep** — it reached NO-COLLAPSE independently, reversed the prompt's
inequality direction, and exposed a genuine `m`-misread trap I then verified.

---

## ★ HEADLINE VERDICT — NO COLLAPSE across the sweep; the no-go is FORCED, and the `D/m ≥ n₀` framing is fragile

**No collapsing branch exists.** For every chain tested (anchor + all four flagged bottlenecks + corank-2/3
cuts + `L=3,4,5` + a 23-chain sweep), the box-integral RLCT `= ½·minAdm`, with **no cell undershooting**.
The certified reason is a three-pillar structure, decorrelated-confirmed:

> **(P1) geometric tube codim `= cCodim`** (product-pushforward, `≪` free-determinantal — bottlenecks make it
> *smaller*, never make the pushforward power drop below it); **(P2) `m = 1`** transverse to a generic
> binding tube (via the product's *reduced full-rank first-order normal slice*); **(P3) binding forces
> `D_q ≤ M₀q`**, so the coupled corner's `min(M₀q, D_q)` retains the FULL tube codim, and the charges ADD to
> `½(D_q + d_q) = ½·minAdm`.

**Three named misread traps** would each FAKE a collapse without one existing (the "diagnose which object is
misread" the brief asked for): (T-a) using `U₀ = det(PPᵀ)` (order `2q`) as `σ_min²` (order `2`) → spurious
`m = q`; (T-b) reading the tube as the corank block `A₁,cor·A₂⋯A_L` (which prepends the FREE front layer) →
spurious low codim (anchor: `2 < 4`); (T-c) claiming `½(D_q+d_q)` as the cell VALUE on a narrow-front chain
where the front charge `M₀q` caps it (`(1,5,3,3)` q=3: `9/2` claimed vs `3/2` true). **None is a real
sub-`½minAdm` region; each is an unfaithfulness artifact of the resolution reading the wrong object.**

**Framing correction (important, fold into the StepHyp).** The prompt's "`full value ½minAdm ⟺ D/m ≥ n₀`,
`n₀ = ab`" is VIEW-DEPENDENT and the inequality direction INVERTS between the top-level and decorated views
(worked below on the anchor). The robust, view-free invariant is the QIP identity
`min_ρ(cCodim(deeper; ρ) + M₀·ρ) = minAdm(M)` with the geometric `cCodim` and `m = 1`.

---

## 1. The linchpin sweep — `min_ρ(D_ρ + d_ρ) = minAdm` with GEOMETRIC cCodim (no QIP-level collapse)

Top-level corank decomposition: front `A₀ = M₀×M₁`, deeper product `P = A₁⋯A_{L−1}` (`M₁×M_L`, generic rank
`r = min(M₁,…,M_L)`). Cell by corank `q` (`ρ = r−q` survive): `d_q = M₀ρ` (front charge), `D_q =
cCodim(deeper; ρ) = codim{rank P ≤ ρ}` (product tube). [`master.py`] **All 23 chains: `min_q(D_q+d_q) =
minAdm`, 0 violations** — anchor, `(3,5,2,5)`,`(2,4,2,5)`,`(2,4,4,5)`,`(2,5,2,2,5)`,`(5,2,5)`,`(6,2,6)`,
`(7,2,2,2,7)`,`(4,4,4,4)`,`(5,5,5,5)`,`(3,3,3,3,4)`,`(4,4,4,4,4)`,`(3,4,5,4,3)`, … The identity is the
banked front-peel/QIP (`prodD-general` §3: 0/28420); re-verified here on the bottleneck-heavy set.

## 2. (P1) The geometric tube codim `= cCodim`, even for double/triple bottlenecks (Jacobian rank)

`cCodim` is the parameter-space (factor Lebesgue) codim; a bottleneck makes it `≪` the free-determinantal
target codim, but the pushforward power never drops below it. Independent check = rank of the Jacobian of the
`(ρ+1)`-minors at a generic rank-`ρ` point [`jac_codim.py`, `jac_codim2.py`]:

| chain | ρ | cCodim | Jacobian codim | free-det |
|---|---|---|---|---|
| `(4,2,4)` | 1 | 3 | 3 | 9 |
| `(5,2,5)` | 1 | 4 | 4 | 16 |
| `(3,3,4)` | 1 / 2 | 4 / 1 | 4 / 1 | 6 / 2 |
| `(4,2,2,4)` (double) | 1 | 1 | 1 (drop interior A₁) | 9 |
| `(4,2,4,2,4)` (double) | 1 | 1 | 1 (drop interior A₁ or A₂) | 9 |
| `(2,5,2,2,5)`,`(7,2,2,2,7)`,`(5,2,2,5)` | 1 | 1 | 1 (drop an interior bottleneck factor) | ≥4 |

The `{rank P ≤ ρ}` variety is a UNION of components (which factor drops), of different codims; `cCodim = MIN`
over them, and the pushforward tube measure is dominated by the cheapest = an INTERIOR bottleneck factor's
rank-1 drop (codim `= cCodim`). [Codex Q3: "scheme multiplicity or a singular pushforward density cannot
lower this parameter-space Lebesgue codim."] (A first draft that forced the FIRST factor to drop landed on a
deeper, non-generic component — the cheapest interior drop is the measure-carrying one.)

## 3. (P2) `m = 1` on a generic binding tube — and the `det(PPᵀ)` misread trap (T-a)

For the corank-1 drop of a bottleneck product `P = A·B` (`A: 4×2, B: 2×4`, rank ≤ 2 structural), a symbolic
transverse ray gives `σ₂²(P) ≍ t²` (order 2) and an individual `2×2` minor `≍ t` (order 1)
[`vanishing_order.py`]. So `U₀ = σ_min² ≍ dist²`, i.e. `2m = 2`, **`m = 1`**.

**The reason is not mere radicality** (Codex Q1, adopted): a radical determinantal ideal can acquire
multiplicity under an arbitrary pullback. What forces `m=1` for a matrix PRODUCT is that at a generic point of
a maximal rank-profile component, the transverse **first-order normal slice is reduced and contains a
full-rank-`q` matrix** — the compression directions genuinely de-rank at first order. Higher order occurs only
on nested angular loci (descendant rank-profile tubes, higher codim — the recursion's job), not the generic
tube.

> **TRAP (T-a), verified [`verify_codex.py` V3].** For a corank-`q` drop, `det(PPᵀ) ≍ t^{2q}` (it is the
> product of ALL `q` collapsing `σ²`), and a full `r`-minor `≍ t^{q}`. Reading either as the single tube
> `U₀ ≍ |z|^{2m}` gives a spurious `m = q`. `σ_min²` (the SMALLEST, order `2`) is the right per-direction
> object; the faithful treatment is the per-direction iterated corner (the `corank2-cert` joint two-scale
> density), each direction `m=1` — NOT a single aggregate `U₀`.

## 4. (P3) Binding forces `D_q ≤ M₀q`; the corner ADDS, retaining the full tube codim

The exact per-cell RLCT threshold is **`½(M₀ρ + min(M₀q, D_q))`**, NOT the sector-cert's `½(D_q + d_q)` in
general [Codex Q2, verified `verify_codex.py` V1]. The two agree **iff `D_q ≤ M₀q`** (tube no fatter than the
collapsing front charge). At a **binding** `ρ`: `E(ρ) = D(ρ)+M₀ρ ≤ E(r) = M₀r ⟹ D(ρ) ≤ M₀(r−ρ) = M₀q`, so
`min(M₀q, D_q) = D_q` and the cell gives `½(M₀ρ + D_q) = ½(d_q+D_q) = ½minAdm`. The charges ADD (coupled
corner blow-up, verified symbolically for **q=3**: `u₁=u₀τ₁, u₂=u₀τ₂ ⟹ ∫u₀^{Σaᵢ+2−2c} ⟹ c < ½Σ(aᵢ+1)`,
`final_checks.py` (A); MIN would need a shared divisor, the ruled-out `radialAttach`).

> **TRAP (T-c), verified [V1].** On a NARROW-FRONT chain the front charge `M₀q` caps the cell BELOW
> `½(D_q+d_q)`: `(1,5,3,3)` q=3 has `D_3 = minAdm(5,3,3) = 9`, `d_3 = 0`, so `½(D_3+d_3)=9/2` — but `M₀q = 3`,
> the map is a submersion onto 3 coords, true local RLCT `= ½min(3,9) = 3/2`. **Not a collapse:**
> `minAdm(1,5,3,3) = 3`, so `3/2` IS the global RLCT (this cell is the binding one). The min over cells still
> `= minAdm` [V1: `(1,5,3,3)`,`(1,4,4,4)` corrected-min `= minAdm`]. The lesson: the descent must not assert
> `½(D_q+d_q)` as the cell VALUE for narrow fronts — it is an over-claim (still `≥ ½minAdm`, so (□) survives).

## 5. TRAP (T-b) — the tube is the DEEPER PRODUCT, not the corank block with the free front layer

The binding-cut db2 diagnostic [`binding_diag.py`] exposes the sharpest artifact. At the anchor decorated cut
`t*=1` (`a=b=2`, `n₀=ab=4`, `n₁=minAdm(1,3,4)=3`), two readings of "the tube":

- **deeper product `A₂` (3×4), `{rank A₂ ≤ 1}`:** `cCodim((3,4);1) = 6`. `D/m = 6 ≥ n₀ = 4` ⟹ corner ADDS ⟹
  `n₁/2 + ½·n₀ = 7/2`. ✓ (the `stephyp-cert` reading).
- **corank block `W = A₁,cor·A₂` (chain `(2,3,4)`), `{rank W ≤ 1}`:** `cCodim((2,3,4);1) = 2` (dominated by
  the FREE `A₁,cor: 2×3` dropping to rank 1, codim 2). `D/m = 2 < n₀ = 4` ⟹ `n₁/2 + ½·2 = 2.5 < 7/2` — a
  **spurious collapse.**

The corank-block reading double-counts the FREE front layer `A₁,cor`'s own rank drop as if it were a deep
tube; that degeneration is already inside the front peel's `½·ab` charge, not the deep tube.
**`transversality-recursion` §1 is exactly the certificate that the deeper-product reading is the correct
one:** at a binding cut `rank_{gen}(Zdeep) ≥ a+b−1 ≥ b`, so the corank block `A₁,cor·Zdeep` has FULL ROW RANK
`b` (a unit, `p=0`) on the top-dim components — the corank block does NOT independently drop rank there; the
only binding deep tube is `Zdeep`'s own rank drop. (Neither the deeper-product nor the corank-block reading
is universal: for `L=2` chains `(5,2,5),(6,2,6)` the "deeper product" degenerates and the corank block IS the
terminal layer — `binding_diag.py` shows exactly one reading is correct per arity, and it always gives `½minAdm`.)

## 6. The `D/m ≥ n₀` framing is VIEW-DEPENDENT (anchor, both views → 7/2) [`final_checks.py` (C)]

| view | `n₀` | `D/m` | comparison | corner | value |
|---|---|---|---|---|---|
| top-level (front `A₀=3×3`, deeper `A₁A₂`, binding q=2) | `M₀q = 6` | `D_2 = 4` | `D/m < n₀` | MIN picks tube `4` | `½(3+4)=7/2` |
| decorated cut `t*=1` (Γ-block `2×2`, deeper `A₂`) | `ab = 4` | `6` | `D/m > n₀` | ADD | `½(4+3)=7/2` |

Same chain, same RLCT, **opposite inequality**. The scalar `n₀` and the direction of `D/m ⋛ n₀` are
bookkeeping that depends on where you draw the front/deep cut. **The invariant that is not view-dependent is
`min_ρ(cCodim(deeper;ρ) + M₀ρ) = minAdm`** (P1–P3). State the StepHyp soundness in those terms, not as a bare
`D/m ≥ n₀`.

---

## Firmest / most-likely-to-break / next

- **Firmest (obstruction, decorrelated-confirmed).** No collapsing branch exists on the sweep; the RLCT is
  `½minAdm` because (P1) the geometric tube codim `= cCodim` (Jacobian-verified incl. double/triple
  bottlenecks), (P2) `m=1` on generic binding tubes (reduced full-rank normal slice — verified `σ₂²≍t²`), and
  (P3) binding forces `D_q ≤ M₀q` so the coupled corner keeps the full tube codim and the charges ADD to
  `½minAdm` (q=3 checked). The QIP linchpin holds with the geometric `cCodim` (0 violations / sweep). Codex
  independently hunted and returned "NO COLLAPSE," and its `(4,3,3,3)` `E=(7,7,9,12)`, `(1,5,3,3)→3/2` were
  re-verified here.
- **Most likely to (falsely) break it — the 3 misread traps.** (T-a) `U₀ = det(PPᵀ) ≍ t^{2q}` read as
  `σ_min²` → spurious `m=q`; use `σ_min²` per direction. (T-b) tube read as the corank block (prepends free
  `A₁,cor`) → spurious low codim; use the genuine deeper product `Zdeep` (`transversality` §1 licenses it).
  (T-c) `½(D_q+d_q)` asserted as the cell VALUE for a narrow front (`M₀q < D_q`) → over-claim; the true cell
  is `½(M₀ρ + min(M₀q,D_q))`, still `≥ ½minAdm`, so (□) survives but the descent must not over-assert.
- **Next.** The StepHyp formalisation should (i) carry the tube as `Zdeep`'s rank drop (not the corank block),
  (ii) use `σ_min²`/per-direction coupling (not `det(PPᵀ)`), (iii) prove the per-cell bound as
  `½(M₀ρ + min(M₀q, D_q)) ≥ ½minAdm` via the binding inequality `D(ρ) ≤ M₀q` (banked back-peel convexity),
  NOT the unqualified `½(D_q+d_q)`. The one genuinely geometric input still owed to Lean is (P2) the reduced
  full-rank first-order normal slice of the product (`m=1`) — banked-adjacent to `normalSlice_transfer`
  (#109); everything else is the QIP arithmetic already banked.
