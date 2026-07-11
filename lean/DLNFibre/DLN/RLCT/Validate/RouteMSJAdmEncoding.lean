import DLNFibre.DLN.RLCT.Validate.RouteMSJLedger

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJAdmEncoding` — the A2 base-soundness (P)/(T) encoding + regression test

**Thread `genm-sj5-descent`, the A2 admissible-family base-soundness scaffolding (cover §6 base-audit
finding C1).** `#144-independent`: pins the exact quantifier the decorated leaf terminal needs, and bakes
in the base-audit's countertest so a wrong terminal-application fails immediately.

## The (P)/(T) quantifier distinction (cover C1)

`sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger`) requires a **simultaneous** dehomogenised generator:

  (T)  `∃ i₀, ∀ ℓ, e i₀ ℓ = sharedDivisorExp e ℓ`   — ONE generator attains the shared min at EVERY divisor.

The `p=0` transversality (cover #144) supplies only the **divisorwise** form:

  (P)  `∀ ℓ, ∃ i, e i ℓ = sharedDivisorExp e ℓ`     — at EACH divisor SOME generator is a unit.

`(T) ⟹ (P)` trivially, but **`(P) ⇏ (T)`** — the quantifier swap is invalid. The base is sound only when
the terminal is applied with `(T)`, and divisorwise `p=0` alone does NOT supply it: the intersection/combined
exceptional divisors + the chart refinements that resolve them (the `{v=0}` recursion, `cov-ledger-design`
§10.3) are REQUIRED to supply `(T)` on the refined charts. This module states `(P)`, `(T)`, `(T)⟹(P)`, and
the **base-audit regression test**: the fresh-disjoint support `{(1,0),(0,1)}` (the `x²+y²`, RLCT `1`,
divergent-for-`c'≥1` countertest) satisfies `(P)` but NOT `(T)` — so it must be REJECTED as a terminal
instance until its intersection `{x=y=0}` is refined.

Pure support-combinatorics on the banked `sharedDivisorExp` (`RouteMSJLedger`); no measure theory. Untracked
(A2 co-audited with cover before wiring). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ}

/-- **(P) divisorwise `p=0`.** At EACH exceptional divisor `ℓ`, SOME generator `i` attains the shared
min `sharedDivisorExp e ℓ` (is a unit there). What the `p=0` transversality (cover #144) supplies
per critical divisor. -/
def pDivisorwise (e : SJSupport ι d) : Prop :=
  ∀ ℓ : Fin d, ∃ i : ι, e i ℓ = sharedDivisorExp e ℓ

/-- **(T) simultaneous dehomogenised generator.** ONE generator `i₀` attains the shared min at EVERY
divisor — this is EXACTLY the hypothesis of `sjLoss_terminal_lintegral_lt_top` (its `h0`). The base is
sound only when the terminal is applied with this. -/
def pSimultaneous (e : SJSupport ι d) : Prop :=
  ∃ i₀ : ι, ∀ ℓ : Fin d, e i₀ ℓ = sharedDivisorExp e ℓ

/-- **`(T) ⟹ (P)`** (trivial direction). -/
theorem pDivisorwise_of_pSimultaneous (e : SJSupport ι d) (h : pSimultaneous e) :
    pDivisorwise e := by
  obtain ⟨i₀, hi₀⟩ := h
  exact fun ℓ => ⟨i₀, hi₀ ℓ⟩

/-! ## The base-audit regression test — `(P) ⇏ (T)` on the fresh-disjoint countertest -/

/-- The **fresh-disjoint** support `{(1,0),(0,1)}` — two generators `x`, `y` over `Fin 2` exceptional
divisors, disjoint (each divides its own coordinate). The `x²+y²` countertest (RLCT `1`, divergent for
`c' ≥ 1`); its `{x=y=0}` intersection carries `p_E = 1`. -/
def suppFreshTwo : SJSupport (Fin 2) 2 := ![![1, 0], ![0, 1]]

/-- The fresh-disjoint support has trivial shared divisor everywhere (`min` of the disjoint columns). -/
theorem sharedDivisorExp_suppFreshTwo (ℓ : Fin 2) : sharedDivisorExp suppFreshTwo ℓ = 0 := by
  rw [sharedDivisorExp_fin_two]
  fin_cases ℓ <;> rfl

/-- **(P) HOLDS on the fresh-disjoint support.** At each divisor SOME generator is a unit
(`x` is a unit at `y`'s divisor and vice versa). -/
theorem suppFreshTwo_pDivisorwise : pDivisorwise suppFreshTwo := by
  intro ℓ
  rw [sharedDivisorExp_suppFreshTwo ℓ]
  fin_cases ℓ
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- **★ REGRESSION TEST (base-soundness, cover C1): `(T)` FAILS on the fresh-disjoint support.** No
single generator is a unit at BOTH divisors — so `sjLoss_terminal`'s hypothesis is NOT met, and the
support must be REJECTED as a terminal instance until its intersection is refined. Together with
`suppFreshTwo_pDivisorwise` this witnesses `(P) ⇏ (T)`: a base lemma that applied the terminal on
divisorwise `p=0` alone would (wrongly) accept the divergent `x²+y²`. -/
theorem suppFreshTwo_not_pSimultaneous : ¬ pSimultaneous suppFreshTwo := by
  rintro ⟨i₀, hi₀⟩
  have h0 := hi₀ 0
  have h1 := hi₀ 1
  rw [sharedDivisorExp_suppFreshTwo] at h0 h1
  fin_cases i₀
  · exact absurd h0 (by decide)
  · exact absurd h1 (by decide)

/-- **`(P) ⇏ (T)` — the invalid quantifier swap, exhibited.** The fresh-disjoint support satisfies the
divisorwise `p=0` but not the simultaneous one. This is the exact gap cover's C1 flags: the base is
sound only via `(T)` (supplied by the intersection refinement), never divisorwise `(P)` alone. -/
theorem pDivisorwise_not_imp_pSimultaneous :
    ∃ (e : SJSupport (Fin 2) 2), pDivisorwise e ∧ ¬ pSimultaneous e :=
  ⟨suppFreshTwo, suppFreshTwo_pDivisorwise, suppFreshTwo_not_pSimultaneous⟩

end DLNFibre.DLN.RLCT
