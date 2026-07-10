import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeelCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDescNat` — the B5-desc-ℕ contract (min-tail-width → `minAdm`)

**Thread `genm-b5desc-nat` (aoyagi-full).** The `ℕ`-arithmetic side of the `(S,J)` recursion's
descent spine (carrier-skeleton brick **B5-desc-ℕ**). Recon verdict: **the arithmetic is BANKED**;
the one genuinely-new piece is the *front-peel binding cut* (`frontPeel_binding_cut` below), the
min-tail-width analogue of the banked layer-peel `exists_binding_cut`.

## What the descent needs, and where it lives

`subred`'s descent (`expeditions/2026-06-20-aoyagi-full/threads/genm-subred/verdict.md`) reduces the
corank-Gram integral of a chain to that of the SHORTER chain `(b, M₂, …, M_last)`, with per-level
integrability threshold `a < min(M₂,…,M_last) − b + 1` (min tail width minus corank). The `ℕ`
book-keeping that turns those per-level thresholds into the global `½·minAdm(M)` budget is the
**front-peel identity**: `minAdm M` as a min over the tail-rank `q ≤ tailMin M` (`tailMin M =
min(M₁,…,M_last)`, the min tail width) of `frontCharge M q = M₀·q + minAdm((M₁,…,M_last) − q)`.

- **min-tail-width → `minAdm` (the identity).** `minAdm_eq_frontPeel` (`RouteMFrontPeelCharge`) —
  BANKED, clean-three. This IS the "analogue of `minAdm_eq_frontPeel`" the carrier skeleton names.
- **each per-level charge is ≥ the budget.** `frontCharge_ge_minAdm` (`RouteMFrontPeelCharge`) —
  BANKED: every stratum's charge `M₀·q + minAdm(reduced)` dominates `minAdm M`, so no per-level
  threshold under-shoots `½·minAdm`.
- **the binding cut is achieved (here).** `frontPeel_binding_cut` — a tail-rank `q★ ≤ tailMin M`
  attaining the min, `minAdm M = frontCharge M q★`. The front-peel analogue of the banked
  layer-peel binding cut `exists_binding_cut` (`RouteMSJDecoratedCharge`, the `0/1344` saturation
  `minAdm M = peelCharge M t★ + minAdm (redChain t★ M)`). This is the tail-rank the descent's
  additive charge accounting (brick B5b) selects.

## Level separation — the ruled-out reading (anti-trap)

The corank-Gram threshold `tailMin M − b + 1` is the integrability threshold of the emitted Gram
weight at a FIXED stratum; it is **NOT** `minAdm` of that chain. `tailMin − b + 1 ≠ minAdm`
already at two widths: chain `(b, m)` has corank-Gram threshold `m − b + 1` but `minAdm (b,m) = b·m`
(e.g. `b = m = 2`: threshold `1`, `minAdm 4`). Do NOT formalise `tailMin M − b + 1 = minAdm M`; the
arithmetic that composes to `minAdm` is the front-peel above, not the raw per-level threshold.

S2-FREE: pure `ℕ` order algebra on the banked `minAdm`/`tailMin`/`frontCharge`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. No measure theory, no new combinatorics.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **B5-desc-ℕ — the front-peel binding cut (min-tail-width form).** For a `≥ 3`-width chain `M`
there is a tail-rank `q★ ≤ tailMin M` (`tailMin M = min(M₁,…,M_last)`, the min tail width) achieving
the front-peel min: `minAdm M = frontCharge M q★ = M₀·q★ + minAdm ((M₁,…,M_last) − q★)`. The
front-peel analogue of the banked layer-peel binding cut `exists_binding_cut`; the tail-rank the
descent's additive charge accounting selects. Immediate from the banked `minAdm_eq_frontPeel` (the
achiever of the `inf'`). The cut may be SUB-generic (`q★ < tailMin M`) — see the anchor below. -/
theorem frontPeel_binding_cut (M : Fin (L + 1 + 1 + 1) → ℕ) :
    ∃ q, q ≤ tailMin M ∧ minAdm M = frontCharge M q := by
  obtain ⟨q, hqmem, hqeq⟩ := Finset.exists_mem_eq_inf'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero (tailMin M))) (frontCharge M)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hqmem
  refine ⟨q, hqmem, ?_⟩
  rw [minAdm_eq_frontPeel M]
  exact hqeq

/-! ## Fidelity anchors (cert §C worked examples)

The binding cut can be generic (`q★ = tailMin M`) or SUB-generic (`q★ < tailMin M`). -/

-- `(3,3,3,4)`: `tailMin = 3`; binding cut generic at `q★ = 2` (`frontCharge 2 = 7 = minAdm`).
example : minAdm (![3, 3, 3, 4] : Fin 4 → ℕ)
    = frontCharge (![3, 3, 3, 4] : Fin 4 → ℕ) 2 := by decide

-- `(4,4,2)`: binding cut SUB-generic at `q★ = 1 < tailMin = 2` (`frontCharge 1 = 7 = minAdm`, while
-- `frontCharge 0 = frontCharge 2 = 8`) — the contracting-tail twist `subred` flags.
example : minAdm (![4, 4, 2] : Fin 3 → ℕ)
    = frontCharge (![4, 4, 2] : Fin 3 → ℕ) 1 := by decide
example : (1 : ℕ) < tailMin (![4, 4, 2] : Fin 3 → ℕ) := by decide

end DLNFibre.DLN.RLCT
