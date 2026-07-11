import DLNFibre.DLN.RLCT.Validate.RouteMSJTransversality
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeelCharge

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJBackPeel` — the α-unlock: co-minimizing deeper rank `ρ ≥ b`

**Thread `genm-sj5-desc2`, piece #1 of the §5 decorated-descent discharge
(`transversality-recursion.md §8`, the NATIVE route honoring #97).**

The cert names one "new lemma" `minAdm_eq_backPeel`:
`minAdm(t, M₂,…,M_L) = min_ρ [ cCodim(M₂,…,M_L ; ρ) + t·ρ ]`. This is **already banked** as the
FRONT-PEEL identity `minAdm_eq_frontPeel` (#117, `RouteMFrontPeelCharge`): applied to the reduced
chain `redChain t M = (t, M₂, …, M_L)` (leading width `t`), the front-peel reads

    minAdm (redChain t M) = min_{ρ ≤ tailMin (redChain t M)} [ t·ρ + minAdm ((M₂,…,M_L) − ρ) ]

and the geometric gloss `cCodim(M₂,…,M_L ; ρ) = minAdm((M₂,…,M_L)−ρ)` is the FrontPeelCharge
docstring's own reading (the shifted-tail `minAdm` IS the codim of `{rank(deeper product) ≤ ρ}`,
via the banked `cCodim_rankShift`). So the back-peel needs **no fresh Core.CTheta/QIP build** — it
is the front-peel with the leading width read as the surviving pivot `t`.

The genuinely-new arithmetic content is the **incidence + convexity** combination the transversality
consumes (cert §8): at a NONDEGENERATE binding cut (`a = M₀−t ≥ 1`, `b = M₁−t ≥ 1`), every
front-peel co-minimizing rank `ρ` of `redChain t M` satisfies `ρ ≥ a+b−1 ≥ b`.

Proof (pure ℕ, two banked lemmas):
- **Incidence** (from `minAdm_eq_frontPeel` / `frontCharge_ge_minAdm`): a co-minimizer `ρ` of
  `redChain t M` bounds the next cut, `minAdm (redChain (t+1) M) ≤ minAdm (redChain t M) + ρ`
  (same tail, leading width `t+1` vs `t` costs one extra `ρ`).
- **Convexity** (banked `minAdm_redChain_succ_ge` / `_corankWidth`, `RouteMSJTransversality`):
  `minAdm (redChain t M) + (a+b−1) ≤ minAdm (redChain (t+1) M)`.
- **Combine:** `a+b−1 ≤ ρ`.

This is the `p=0`-transversality's "deeper generic rank `r_X ≥ b`" (cert §8), stated
combinatorially via the co-minimizing rank — NO irreducible-component decomposition, NO
generic-rank-on-a-variety (the AG wall this route AVOIDS, #114 verdict α). Consumes only banked ℕ
lemmas; axiom-clean.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {K : ℕ}

/-! ## Tail invariance under a pivot bump

The reduced chains `redChain t M` and `redChain (t+1) M` differ only in the leading width; their
tail `(M₂,…,M_L)` is identical, so `tailMin` and the shifted-tail `minAdm` (the front-peel charge
minus its leading `t·ρ` term) are unchanged. -/

/-- **Tail-min is invariant under a pivot bump.** The reduced chains `redChain t M`,
`redChain (t+1) M` share the tail `(M₂,…,M_L)`, so their tail-mins agree (here the `≤` direction,
which the transport needs). -/
theorem tailMin_redChain_le_succ (M : Fin (K + 1 + 1 + 1 + 1) → ℕ) (t : ℕ) :
    tailMin (redChain t M) ≤ tailMin (redChain (t + 1) M) := by
  rw [le_tailMin_iff]
  intro i
  have h1 := (le_tailMin_iff (redChain t M) (tailMin (redChain t M))).mp le_rfl i
  rw [redChain_succ]
  rw [redChain_succ] at h1
  exact h1

/-- **The front-peel charge under a pivot bump.** With the tail fixed, bumping the leading width
from `t` to `t+1` adds exactly `ρ` to the charge at rank `ρ`:
`frontCharge (redChain (t+1) M) ρ = frontCharge (redChain t M) ρ + ρ`. The `minAdm` of the shifted
tail is the shared term; the block term `(leading)·ρ` rises by `ρ`. -/
theorem frontCharge_redChain_succ (M : Fin (K + 1 + 1 + 1 + 1) → ℕ) (t ρ : ℕ) :
    frontCharge (redChain (t + 1) M) ρ = frontCharge (redChain t M) ρ + ρ := by
  simp only [frontCharge, redChain_zero, redChain_succ]
  ring

/-! ## The α-unlock — the co-minimizing deeper rank `ρ ≥ a+b−1 ≥ b` -/

/-- **The back-peel co-minimizer bound (sharp, `a+b−1` form).** At a NONDEGENERATE binding cut `t`
of a `≥ 4`-width chain `M` (`t+1 ≤ min(M₀,M₁)`, i.e. `a = M₀−t ≥ 1`, `b = M₁−t ≥ 1`; the cut
binding, `minAdm M = peelCharge M t + minAdm (redChain t M)`), **every** front-peel co-minimizing
rank `ρ` of the reduced chain `redChain t M` — a rank with `ρ ≤ tailMin (redChain t M)` at which the
front-peel min is attained (`frontCharge (redChain t M) ρ = minAdm (redChain t M)`) — satisfies
`(M₀−t) + (M₁−t) − 1 ≤ ρ`.

This is cert §8's "every co-minimizer `ρ ≥ a+b−1`": the deeper product's generic rank on a top-dim
component of the reduced zero-product locus is at least `a+b−1`. Combinatorial (co-minimizing rank),
no component decomposition. -/
theorem minAdm_backPeel_cominimizer_ge (M : Fin (K + 1 + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (ρ : ℕ) (hρ : ρ ≤ tailMin (redChain t M))
    (hcomin : frontCharge (redChain t M) ρ = minAdm (redChain t M)) :
    (M 0 - t) + (M 1 - t) - 1 ≤ ρ := by
  -- Convexity (banked): C_t + (a+b−1) ≤ C_{t+1}.
  have hconv := minAdm_redChain_succ_ge M t ht1 hbind
  -- Incidence: C_{t+1} ≤ frontCharge (redChain (t+1) M) ρ = frontCharge (redChain t M) ρ + ρ.
  have hρ' : ρ ≤ tailMin (redChain (t + 1) M) :=
    le_trans hρ (tailMin_redChain_le_succ M t)
  have hinc : minAdm (redChain (t + 1) M) ≤ frontCharge (redChain (t + 1) M) ρ :=
    frontCharge_ge_minAdm (redChain (t + 1) M) ρ hρ'
  have hfc := frontCharge_redChain_succ M t ρ
  -- Chain: C_t + (a+b−1) ≤ C_{t+1} ≤ frontCharge(t+1) = frontCharge(t) + ρ = C_t + ρ.
  omega

/-- **The back-peel co-minimizer bound (corank-width `b` corollary).** At a nondegenerate binding
cut, every front-peel co-minimizing rank `ρ` of `redChain t M` dominates the corank width
`b = M₁−t`: `M₁ − t ≤ ρ`. (Since `a = M₀−t ≥ 1`, `a+b−1 ≥ b`.) This is the exact bound the
corank-survival step consumes — the `b` free corank rows pass through a rank-`≥ b` deeper product,
so they survive full-row-rank `b` (`p = 0`). -/
theorem minAdm_backPeel_cominimizer_ge_corankWidth (M : Fin (K + 1 + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M))
    (ρ : ℕ) (hρ : ρ ≤ tailMin (redChain t M))
    (hcomin : frontCharge (redChain t M) ρ = minAdm (redChain t M)) :
    M 1 - t ≤ ρ := by
  have h := minAdm_backPeel_cominimizer_ge M t ht1 hbind ρ hρ hcomin
  have ha : 1 ≤ M 0 - t := by omega
  omega

/-- **Existence of a co-minimizing deeper rank `ρ ≥ b`.** At a nondegenerate binding cut, the
front-peel min of `redChain t M` is attained at some rank `ρ` with `ρ ≤ tailMin (redChain t M)`,
`frontCharge (redChain t M) ρ = minAdm (redChain t M)`, and `M₁ − t ≤ ρ`. The form the
corank-survival step (piece #2) consumes: a deeper rank `≥ b` exists at which the reduced
zero-product locus's codim is achieved. -/
theorem exists_minAdm_backPeel_cominimizer_corankWidth (M : Fin (K + 1 + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M)) :
    ∃ ρ, ρ ≤ tailMin (redChain t M) ∧ frontCharge (redChain t M) ρ = minAdm (redChain t M)
      ∧ M 1 - t ≤ ρ := by
  obtain ⟨ρ, hρmem, hρeq⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.range (tailMin (redChain t M) + 1))
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _)) (frontCharge (redChain t M))
  rw [Finset.mem_range, Nat.lt_succ_iff] at hρmem
  have hcomin : frontCharge (redChain t M) ρ = minAdm (redChain t M) := by
    rw [minAdm_eq_frontPeel (redChain t M)]; exact hρeq.symm
  exact ⟨ρ, hρmem, hcomin,
    minAdm_backPeel_cominimizer_ge_corankWidth M t ht1 hbind ρ hρmem hcomin⟩

/-! ## Fidelity anchor — the delicate rank-drop cut `(3,3,2,2) →_{t=2} (2,2,2)`

The reduced `(2,2,2)` has its unique top-dim component at deeper rank `1 < 2` (a REAL rank drop;
cert §2's decorrelated counterexample to the naive "`Zdeep` full-rank" claim). Here `a = b = 1`, and
the co-minimizing rank is `ρ* = 1 = b`: the corank row survives (`min(b, ρ*) = 1`), so `p = 0`. This
is the regression test the encoding must pass (cert §6 test 1). -/

/-- `(3,3,2,2)` at the nondegenerate binding cut `t = 2` reduces to `(2,2,2)`; the front-peel of
`(2,2,2)` achieves its min `= 3` at rank `ρ = 1`, with `b = M₁ − t = 1`, so `ρ = b` (tight).
Concrete witness that the co-minimizing deeper rank meets — not exceeds — the corank width at a
genuine rank-drop cut. -/
example :
    frontCharge (redChain 2 (![3, 3, 2, 2] : Fin 4 → ℕ)) 1
      = minAdm (![2, 2, 2] : Fin 3 → ℕ) := by decide

example : redChain 2 (![3, 3, 2, 2] : Fin 4 → ℕ) = (![2, 2, 2] : Fin 3 → ℕ) := by decide

end DLNFibre.DLN.RLCT
