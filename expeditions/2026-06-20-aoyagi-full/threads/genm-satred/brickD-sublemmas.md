# brickD-sublemmas — the a<u / a≥u sub-lemma instantiations for `headSplit_domination` (Brick D)

**Seat:** pen-and-paper (design), `genm-satred`. **Date:** 2026-07-16. **NO Lean edits.** Pins the two
C-integral arms of Brick D's `C_hle < ⊤` (§3 of `brickD-pin.md`) as exact sub-lemma statements for `brickf`
to build against, now that **Brick F is UP** (`exists_headSplitFrame_impl`, clean-three). Uses F's exact
frame contract. Companion to `brickD-pin.md` (the 6-step decomposition) and `hBackbone-edge-pin.md` (the
edge sibling). Verified: `scripts/brickD_scope.py`, decorrelated Codex (`codex/brickD-answer.md`).

---

## Frame contract consumed (Brick F, brickf-confirmed)

For Brick D at `u = t+j`, `M₂ = M 2`, `n = M_last`, `m = min(M₁,M_last) − j`, `ε' = ε/√(M₁M₂)`,
`Zdeep = deeperFlagZdeep M u`, Brick F gives `(Zf, U_sf)` with (all `∀z`, unconditional): `Measurable`;
`(U_sf z)ᵀ·U_sf z = 1` (⇒ `P_z := U_sf z·(U_sf z)ᵀ` a rank-m projection); `m ≤ (Zf z).rank`;
**hfloor** `Zf z·(Zf z)ᵀ ⪰ ε'²·P_z` (UNIFORM, z-free `ε'²`); agreement `weakEigCount ε' (Zdeep z) ≤ M₂−m
→ Zf z = Zdeep z` (shell ⊆ G via Ky-Fan). **hfloor is the uniform conditioning of `Q_b = A_cor·Zf z`**
(Codex Q1's requirement) — NOT of the pivot `Q̃ₚ` (see the caveat).

## Arm A<U (`a < u`) — `corner_C_shift_disposal` (the clean R2 leaf)

Statement to build (schematic; `a = M₀−u`, `b = M₁−u`, `Q̃ₚ` the u×n pivot-shifted matrix, `c' > ab/2`):

    (a < u) → (Q̃ₚ full row rank u, generic) →
      ∫_{C ∈ Cbox} (W + frobSq(C·Q̃ₚ + Γ·Q_b))^{−c'} dC
        ≤ |v'_{j₀}|^{−a} · scaledRadialEuclid a (c') · W^{−(c' − a·b/2)}     [pointwise in the freed vars]
    ∧  ∫_{ω ∈ sphere} ‖Q̃ₚ ω‖^{−a} dω < ⊤   (⟺ a < u)                       [the disposal]

Build kit (banked): `edge_C_shift_bound` / `RouteMSJGammaAtom` (β-invariant R2 bound); `scaledRadialEuclid`
(the a-dim radial, CLEAN power for `c' > ab/2` — no log, log only at the critical `c'=ab/2`);
`corner_block_lintegral_lt_top` (the sphere integral finite ⟺ a<u; `ker Q̃ₚ` codim u). `C_hle` = (sphere
const)·(`scaledRadialEuclid`'s `Cresid`). The `|v'_{j₀}|` per-z index is a measurable argmax (Brick-F-adjacent).

## Arm A≥U (`a ≥ u`) — `corner_C_shift_gammaAtom` (the fuller lemma)

The drop-transverse majorant diverges (`∫‖v‖^{−a}dω` diverges for a≥u), so keep the FULL C-integral:

    (a ≥ u) → (Q̃ₚ Q̃ₚᵀ PosDef, from hpiv-genericity) → (c' > a·u/2) →
      ∫_{C ∈ Cbox} (W + frobSq(C·Q̃ₚ + Γ·Q_b))^{−c'} dC
        = det(Q̃ₚ Q̃ₚᵀ)^{−a/2} · Cresid (a·u) c' · (W + ‖(Γ·Q_b)·(I − P_{Q̃ₚ})‖²)^{−(c' − a·u/2)}

verbatim `RouteMSJGammaAtom.gammaAtom_aniso_shifted_eq` (`R=Q̃ₚ, q=u, S=Γ·Q_b, p=a`). The reduced
pivot-Gram `∫ det(Q̃ₚ Q̃ₚᵀ)^{−a/2}` is disposed by `RouteMSJQBoxCore.qbox_lintegral_lt_top`
(`< ⊤` iff `b ≤ q ∧ a < q − b + 1`) applied at the **PIVOT** Gram (full-rank, safe) — **NEVER the corank
`Q_b` Gram** (`a = q−b+1` trap). Dim-matching (`Q̃ₚ` row/col ↔ qbox `b,q`) FOLDS into the reduced-chain
recursive IH (single-level qbox strict for 209/283; marginal cells recurse one level — the arity recursion,
`brickD-pin` / `D-cert §3bis`). `C_hle` = the `Cresid`/box constants; the `det(Q̃ₚ Q̃ₚᵀ)^{−a/2}` is carried
to the reduced chain (the IH).

## The conditionality caveat (Codex Q1/Q4 — brickf-confirmed against hfloor)

`hfloor` conditions the DEEP frame `Q_b = A_cor·Zf` uniformly (z-free `ε'²`) — that answers Codex's
uniform-conditioning requirement for the corank side. But `hfloor` does **NOT** condition the PIVOT `Q̃ₚ`
(which `→0` as `z→0` in the box): so `det(Q̃ₚ Q̃ₚᵀ)^{−a/2}` (a≥u arm) is NOT foldable into a uniform `C_hle`
— it is CARRIED to the reduced chain via qbox/IH (per `brickD-pin §3` caveat). Two sharp Codex-Q4 sub-caveats
the reduced chain must carry: (1) the projected Gram `Q_b(I−P_{Q̃ₚ})Q_bᵀ` (the `gammaAtom` `‖S(I−P_R)‖²`)
can degenerate when `Row Q_b → Row Q̃ₚ` even with `Q_b` full-rank; (2) `Z_deep` singular values `→0` scale
`det(·)^{−a/2}` as `t^{−ab}`. Both ride the IH, not `C_hle`.

## Scope guards (bake into `headSplit_domination` before the tide — `brickD-pin §4`)

1. **`hcvg` as-is** (`a+b ≤ m`, the strictly-convergent interior — 0/20874 log-fails, so both arms are
   log-free in scope). The corank-one tie (`a+b=m+1`) is OUT — delegate to the edge descent
   (`hBackbone-edge-pin.md`), NOT this brick.
2. **Add `1 ≤ M 0 − (t+j)` (`a ≥ 1`)** to exclude `a=0` saturation (delegate to `deeperFlag_waist`). At
   `a=0` the C-block + second `freedSchurLoss` term vanish; both arms are vacuous (the C-integral is over a
   0-row block), so the guard just routes cleanly.

## Close

- **Firmest.** Brick D's `C_hle < ⊤` splits: **a<u** = `edge_C_shift` + `scaledRadialEuclid` (clean power,
  c'>ab/2) + sphere-disposal (`corner_block_lintegral_lt_top`, finite ⟺ a<u); **a≥u** = `gammaAtom_aniso_shifted_eq`
  (verbatim) + `qbox_lintegral_lt_top` on the PIVOT Gram (folds into the reduced-chain IH). Brick F's `hfloor`
  supplies the corank-side uniform conditioning; the pivot `Q̃ₚ` non-uniformity rides the IH.
- **Most likely to break.** qbox on the corank `Q_b` (the `a=q−b+1` trap) instead of the pivot Gram;
  attempting one route for both a<u and a≥u; folding `det(Q̃ₚ Q̃ₚᵀ)^{−a/2}` into `C_hle` instead of the IH;
  omitting the `a≥1` / `hcvg` guards.
- **Next.** brickf builds Brick D against these two sub-lemmas + the 6-step decomposition (`brickD-pin`);
  I pin any further sub-detail (the qbox dim-matching per arm) on request.

Files (absolute): `…/threads/genm-satred/brickD-sublemmas.md` (this); `brickD-pin.md`, `hBackbone-edge-pin.md`,
`D-cert.md`, `satred-cert.md`; `codex/brickD-answer.md`.
