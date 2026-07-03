import DLNFibre.Core.Analysis.RLCT.Cited

/-!
# `RLCT.Pair` — the zeta-pole RLCT pair `(λ, m)` and Link 1 (`λ = integrabilityThreshold`)

The **zeta-pole definition of the RLCT** (operator decision A; certificate §1.2): the RLCT of a germ
`K` at `x₀` is the pair `(λ, m)` extracted from the largest pole `s₀` of the local zeta function
`ζ_{K,φ}` (`RLCT.Zeta`), whose existence and pole structure are the ONE bundled monument
(`RLCT.Cited`):

* **`λ := −s₀`** — the **positive** real (`= rlct_x(K)`), *minus* the (negative) largest pole
  location. The sign flip is the load-bearing item (certificate §6.1): `λ` is `−s₀`, **not** the
  pole `s₀` itself;
* **`m := poleOrder`** — the **order of that largest pole**, the honest RLCT multiplicity `rlcm`.
  Named `poleOrder`, **never** a count: `m` is the *analytic* pole order, and is **provably not**
  `θ` = the geometric top-component count (`DLNFibre.DLN.Aoyagi.ThetaOrderDistinction`; the paper
  itself, `main.tex` L1933, says "no simple relationship"). `m` is off the payoff's critical path.

**Link 1 (certificate §3.1).** `λ = RLCT.integrabilityThreshold K U`: the zeta-pole `λ` equals
R2a's cite-free integrability-threshold *value*. This is the hybrid tie — the value half
(`integrabilityThreshold`, `RLCT.Integrability`, cite-free) *equals* the zeta-pole `λ` **by the
bundled cite** (the identity `s₀ = −threshold` is inside the monument, not a free consequence of
bare meromorphy — certificate §6.5). The eventual `½·codim` payoff rides this value (bracketed by
the separate Watanabe/Aoyagi cites); the continuation cite buys `m` and the pole reading.

All extraction here is `Classical.choose` on the one cite (`RLCT.Cited`): `#print axioms` on `λ`,
`rlctPair`, `poleOrder` shows the continuation axiom (plus the foundational three), nothing else.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Complex

namespace RLCT

variable {n : ℕ}

/-! ## The germ+cutoff data with the cite's hypotheses bundled

`ZetaSetup` packages a germ `K`, cutoff `φ`, base point `x₀`, neighbourhood `U`, and the analytic /
smoothness / nonnegativity / zero-at-`x₀` hypotheses the cited monument needs. Bundling lets the
extraction (`Classical.choose` on the cite) take a single argument. -/

/-- The data + hypotheses feeding the zeta-pole cite: a real-analytic nonnegative germ `K` with a
zero at `x₀`, a smooth cutoff `φ` (`≥ 0`, `≠ 0` at `x₀`) supported inside a relatively compact open
neighbourhood `U ∋ x₀` on which `K` is in the pole regime. Exactly the hypotheses of
`cited_zeta_meromorphic_continuation` (locality + pole-regime included). -/
structure ZetaSetup (n : ℕ) where
  /-- The nonnegative real-analytic loss germ. -/
  K : (Fin n → ℝ) → ℝ
  /-- The smooth compactly-supported cutoff. -/
  φ : (Fin n → ℝ) → ℝ
  /-- The base point (a zero of the germ). -/
  x₀ : Fin n → ℝ
  /-- The neighbourhood on which the integrability threshold is taken. -/
  U : Set (Fin n → ℝ)
  /-- `K` is real-analytic. -/
  hK : AnalyticOnNhd ℝ K Set.univ
  /-- `K` is nonnegative. -/
  hKnn : ∀ x, 0 ≤ K x
  /-- `x₀` is a zero of `K` (the singularity is present). -/
  hKx₀ : K x₀ = 0
  /-- `φ` is smooth (`C^∞`). -/
  hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
  /-- `φ` has compact support. -/
  hφc : HasCompactSupport φ
  /-- `φ` is nonnegative. -/
  hφnn : ∀ x, 0 ≤ φ x
  /-- `φ` does not vanish at `x₀`. -/
  hφx₀ : φ x₀ ≠ 0
  /-- `x₀` lies in the neighbourhood `U`. -/
  hx₀U : x₀ ∈ U
  /-- `U` is open. -/
  hUopen : IsOpen U
  /-- `U` is relatively compact (its closure is compact). -/
  hUcpt : IsCompact (closure U)
  /-- `φ` is supported inside `U` (ties the cutoff to the neighbourhood). -/
  hφU : tsupport φ ⊆ U
  /-- The germ is in the pole regime on `U`: the admissible set is bounded above, so the threshold
  is the honest `sSup`, not the `sSup ∅ = 0` junk. -/
  hpole : BddAbove (admissibleExponents K U)

/-- The bundled cite applied to a `ZetaSetup` — the existence statement whose witness the extraction
chooses. -/
theorem ZetaSetup.cite (S : ZetaSetup n) :
    ∃ (Z : ℂ → ℂ) (s₀ : ℝ) (m₀ : ℕ),
      (∀ s : ℂ, 0 < s.re → Z s = zeta S.K S.φ s) ∧
      MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re < 0) ∧
      (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re ≤ s₀) ∧
      s₀ < 0 ∧ (∃ q : ℚ, s₀ = q) ∧ 1 ≤ m₀ ∧
      meromorphicOrderAt Z (s₀ : ℂ) = ((-(m₀ : ℤ) : ℤ) : WithTop ℤ) ∧
      s₀ = -(integrabilityThreshold S.K S.U) :=
  cited_zeta_meromorphic_continuation S.K S.φ S.x₀ S.U S.hK S.hKnn S.hKx₀ S.hφ S.hφc S.hφnn S.hφx₀
    S.hx₀U S.hUopen S.hUcpt S.hφU S.hpole

/-! ## The extracted invariants (on the cite) -/

/-- The **largest pole `s₀`** of the local zeta, extracted from the cite (`Classical.choose`). A
negative real (`largestPole_neg`); the RLCT is its negative. -/
noncomputable def largestPole (S : ZetaSetup n) : ℝ :=
  S.cite.choose_spec.choose

/-- The **pole order `m₀`** of the largest pole, extracted from the cite. The honest RLCT
multiplicity `rlcm` — the *order* of the pole, **never** a component count. -/
noncomputable def poleOrder (S : ZetaSetup n) : ℕ :=
  S.cite.choose_spec.choose_spec.choose

/-- The **meromorphic continuation `Z`** of the local zeta, extracted from the cite: agrees with the
built `zeta` on `{Re s > 0}` (`continuation_agrees`), meromorphic on `ℂ`, with largest pole
`largestPole S`. -/
noncomputable def continuation (S : ZetaSetup n) : ℂ → ℂ :=
  S.cite.choose

/-- The defining properties of the extracted `continuation` / `largestPole` / `poleOrder` (the
`choose_spec` of the cite), stated against the extracted `continuation S` — including the
poles-are-negative and the *maximality* clauses. `continuation`, `largestPole`, `poleOrder` are the
`choose`s, so the big `choose_spec` conjunction is exactly this (definitionally). -/
theorem cite_spec (S : ZetaSetup n) :
    (∀ s : ℂ, 0 < s.re → continuation S s = zeta S.K S.φ s) ∧
    MeromorphicOn (continuation S) Set.univ ∧
    (∀ s : ℂ, meromorphicOrderAt (continuation S) s < 0 → s.re < 0) ∧
    (∀ s : ℂ, meromorphicOrderAt (continuation S) s < 0 → s.re ≤ largestPole S) ∧
    largestPole S < 0 ∧ (∃ q : ℚ, largestPole S = q) ∧ 1 ≤ poleOrder S ∧
    meromorphicOrderAt (continuation S) ((largestPole S : ℝ) : ℂ)
      = ((-(poleOrder S : ℤ) : ℤ) : WithTop ℤ) ∧
    largestPole S = -(integrabilityThreshold S.K S.U) :=
  S.cite.choose_spec.choose_spec.choose_spec

/-- **The continuation agrees with the built zeta on `{Re s > 0}`** (the half-plane where `zeta`
converges, `RLCT.Zeta`). -/
theorem continuation_agrees (S : ZetaSetup n) {s : ℂ} (hs : 0 < s.re) :
    continuation S s = zeta S.K S.φ s := cite_spec S |>.1 s hs

/-- **The continuation is meromorphic on all of `ℂ`.** -/
theorem meromorphicOn_continuation (S : ZetaSetup n) :
    MeromorphicOn (continuation S) Set.univ := cite_spec S |>.2.1

/-- **The poles lie in the open left half-plane** (`Re < 0`): every point of negative meromorphic
order has negative real part. -/
theorem poles_re_neg (S : ZetaSetup n) {s : ℂ}
    (hs : meromorphicOrderAt (continuation S) s < 0) : s.re < 0 :=
  cite_spec S |>.2.2.1 s hs

/-- **`s₀` is the largest pole (maximality).** Every pole of the continuation (negative meromorphic
order) has real part at most `s₀ = largestPole S`. This justifies the name `largestPole`. -/
theorem le_largestPole_of_pole (S : ZetaSetup n) {s : ℂ}
    (hs : meromorphicOrderAt (continuation S) s < 0) : s.re ≤ largestPole S :=
  cite_spec S |>.2.2.2.1 s hs

/-- **The largest pole is negative** (`s₀ < 0`) — the singularity is genuine (certificate §1.2). -/
theorem largestPole_neg (S : ZetaSetup n) : largestPole S < 0 :=
  cite_spec S |>.2.2.2.2.1

/-- **The pole order is at least one** (`1 ≤ m₀`): the largest pole is an actual pole. -/
theorem one_le_poleOrder (S : ZetaSetup n) : 1 ≤ poleOrder S :=
  cite_spec S |>.2.2.2.2.2.2.1

/-- **The order at the largest pole is `−m₀`** (`meromorphicOrderAt` is `−poleOrder`) — a pole of
order `poleOrder S`. -/
theorem meromorphicOrderAt_largestPole (S : ZetaSetup n) :
    meromorphicOrderAt (continuation S) ((largestPole S : ℝ) : ℂ)
      = ((-(poleOrder S : ℤ) : ℤ) : WithTop ℤ) :=
  cite_spec S |>.2.2.2.2.2.2.2.1

/-- **The bundled identity: `s₀ = −(integrabilityThreshold K U)`** — the largest pole equals minus
the RLCT integrability threshold (the load-bearing conjunct of the cite; certificate §3.1). -/
theorem largestPole_eq_neg_threshold (S : ZetaSetup n) :
    largestPole S = -(integrabilityThreshold S.K S.U) :=
  cite_spec S |>.2.2.2.2.2.2.2.2

/-! ## The RLCT pair `(λ, m)` -/

/-- The **RLCT pair** `(λ, m)` at a germ+cutoff setup: `λ` the positive real log-canonical
threshold (`= −s₀`), `m` the pole order (the multiplicity `rlcm`). The zeta-pole *definition* of the
RLCT (certificate §1.2). `lam` is a `ℝ`, `poleOrder` a `ℕ` — **separate types**, so the analytic
order `m` is never coerced to / unified with the geometric count `θ`. -/
structure RLCTPair where
  /-- The RLCT `λ` (a positive real; `= −s₀`, the *negative* of the largest pole). -/
  lam : ℝ
  /-- The RLCT multiplicity `m = rlcm` — the *order* of the largest pole, never a count. -/
  poleOrder : ℕ

/-- The zeta-pole RLCT pair of a germ+cutoff setup: `λ := −s₀` (**positive** — minus the negative
largest pole; certificate §6.1) and `m := poleOrder` (the pole order). Built on the ONE cite. -/
noncomputable def rlctPair (S : ZetaSetup n) : RLCTPair where
  lam := -(largestPole S)
  poleOrder := poleOrder S

@[simp] lemma rlctPair_lam (S : ZetaSetup n) : (rlctPair S).lam = -(largestPole S) := rfl

@[simp] lemma rlctPair_poleOrder (S : ZetaSetup n) : (rlctPair S).poleOrder = poleOrder S := rfl

/-! ## Link 1 — `λ = integrabilityThreshold` (the hybrid tie, from the cite) -/

/-- **Link 1 (certificate §3.1): `λ = integrabilityThreshold K U`.** The zeta-pole RLCT `λ = −s₀`
equals R2a's cite-free integrability-threshold *value* — because the bundled cite carries
`s₀ = −(integrabilityThreshold K U)`, so `λ = −s₀ = integrabilityThreshold K U`. The value half is
cite-free and *equals* the pole-defined `λ` **by the monument** (not free from bare meromorphy). -/
theorem rlctPair_lam_eq_integrabilityThreshold (S : ZetaSetup n) :
    (rlctPair S).lam = integrabilityThreshold S.K S.U := by
  rw [rlctPair_lam, largestPole_eq_neg_threshold, neg_neg]

/-- **`λ` is nonnegative.** From Link 1: `λ = integrabilityThreshold`, a supremum of the nonnegative
admissible exponents (whenever nonempty). Here it follows directly: `λ = −s₀` with `s₀ < 0`. -/
theorem rlctPair_lam_pos (S : ZetaSetup n) : 0 < (rlctPair S).lam := by
  rw [rlctPair_lam, neg_pos]
  exact largestPole_neg S

end RLCT
