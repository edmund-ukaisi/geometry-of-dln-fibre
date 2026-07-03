import DLNFibre.Core.Analysis.RLCT.Cited

/-!
# `RLCT.Pair` — the zeta-pole RLCT pair `(λ, m)` and the LOCAL Link 1 (`λ = rlctAt K x₀`)

The **zeta-pole definition of the RLCT** (operator decision A): the RLCT of a germ `K` at `x₀` is
the pair `(λ, m)` extracted from the largest pole `s₀` of the local zeta `ζ_{K,φ}` (`RLCT.Zeta`),
whose existence and pole structure are the ONE bundled **local** monument (`RLCT.Cited`):

* **`λ := −s₀`** — the **positive** real (`= rlctAt K x₀`), *minus* the (negative) largest pole
  location. The sign flip is load-bearing: `λ` is `−s₀`, **not** the pole `s₀` itself;
* **`m := poleOrder`** — the **order of that largest pole**, the honest RLCT multiplicity `rlcm`.
  Named `poleOrder`, **never** a count: `m` is the *analytic* pole order, and is **provably not**
  `θ` = the geometric top-component count (`DLNFibre.DLN.Aoyagi.ThetaOrderDistinction`; the paper
  itself, `main.tex` L1933, says "no simple relationship"). `m` is off the payoff's critical path.

**Link 1 — LOCAL (certificate §7.2/§7.5).** `λ = RLCT.rlctAt K x₀`: the zeta-pole `λ` equals the
cite-free **local** RLCT of the germ at `x₀` (`RLCT.Local`), directly from the bundled cite (whose
conclusion is `s₀ = −rlctAt K x₀`). This is the *local* identity — consistent (`s₀`, `rlctAt K x₀`
are both germ-at-`x₀` data) and DLN-admissible. The connection to R2a's *regional*
`integrabilityThreshold K U` is the separate, buildable **Bridge B**
(`RLCT.integrabilityThreshold_eq_localRlct_of_worst`), not this cite; and the DLN `½·codim` payoff
rides the *global* Watanabe/Aoyagi cites, not this axiom at `K_B`.

All extraction here is `Classical.choose` on the one cite (`RLCT.Cited`): `#print axioms` on `λ`,
`rlctPair`, `poleOrder` shows the local zeta-pole axiom (plus the foundational three), nothing else.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Complex

namespace RLCT

variable {n : ℕ}

/-! ## The germ+cutoff data with the cite's hypotheses bundled

`ZetaSetup` packages a germ `K`, cutoff `φ`, base point `x₀`, the localizing nbhd `U`, and the
analytic / smoothness / nonnegativity / zero-at-`x₀` hypotheses the *local* cited monument needs.
Bundling lets the extraction (`Classical.choose` on the cite) take a single argument. The `U` only
localizes `φ`'s support — it carries **no** regional threshold (the cite is local; cert §7). -/

/-- The data + hypotheses feeding the LOCAL zeta-pole cite: a real-analytic nonnegative germ `K`
with a zero at `x₀`, and a smooth cutoff `φ` (`≥ 0`, `≠ 0` at `x₀`) supported in a small open nbhd
`U ∋ x₀`. Exactly the hypotheses of `cited_local_zeta_pole` — purely local, **no** sole-zero /
pole-regime / regional-threshold hypothesis (so it is DLN-admissible at any fibre point). -/
structure ZetaSetup (n : ℕ) where
  /-- The nonnegative real-analytic loss germ. -/
  K : (Fin n → ℝ) → ℝ
  /-- The smooth compactly-supported cutoff. -/
  φ : (Fin n → ℝ) → ℝ
  /-- The base point (a zero of the germ). -/
  x₀ : Fin n → ℝ
  /-- The open nbhd localizing `φ`'s support (no threshold is read off it). -/
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
  /-- `x₀` lies in the localizing nbhd `U`. -/
  hx₀U : x₀ ∈ U
  /-- `U` is open. -/
  hUopen : IsOpen U
  /-- `φ` is supported inside `U` (localizes the cutoff near `x₀`). -/
  hφU : tsupport φ ⊆ U
  /-- `x₀` is a *worst singularity* on `supp φ`: the local RLCT is smallest at `x₀` over `supp φ`.
  Load-bearing for consistency — `s₀` is a `supp φ`-quantity, so a wide `φ` covering a sharper zero
  would break `s₀ = −rlctAt K x₀`; this pins it. Admits the DLN fibre (equal-threshold zeros OK). -/
  hWorst : ∀ x ∈ tsupport φ, rlctAt K x₀ ≤ rlctAt K x

/-- The bundled LOCAL cite applied to a `ZetaSetup` — the existence statement whose witness the
extraction chooses. Conclusion is purely local: `s₀ = −rlctAt K x₀`. -/
theorem ZetaSetup.cite (S : ZetaSetup n) :
    ∃ (Z : ℂ → ℂ) (s₀ : ℝ) (m₀ : ℕ),
      (∀ s : ℂ, 0 < s.re → Z s = zeta S.K S.φ s) ∧
      MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re < 0) ∧
      (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re ≤ s₀) ∧
      s₀ < 0 ∧ (∃ q : ℚ, s₀ = q) ∧ 1 ≤ m₀ ∧
      meromorphicOrderAt Z (s₀ : ℂ) = ((-(m₀ : ℤ) : ℤ) : WithTop ℤ) ∧
      s₀ = -(rlctAt S.K S.x₀) :=
  cited_local_zeta_pole S.K S.φ S.x₀ S.U S.hK S.hKnn S.hKx₀ S.hφ S.hφc S.hφnn S.hφx₀
    S.hx₀U S.hUopen S.hφU S.hWorst

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
    largestPole S = -(rlctAt S.K S.x₀) :=
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

/-- **The bundled LOCAL identity: `s₀ = −(rlctAt K x₀)`** — the largest pole equals minus the LOCAL
RLCT of the germ at `x₀` (the load-bearing conjunct of the cite; certificate §7.5). Local, hence
consistent and DLN-admissible. -/
theorem largestPole_eq_neg_rlctAt (S : ZetaSetup n) :
    largestPole S = -(rlctAt S.K S.x₀) :=
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

/-! ## Link 1 — LOCAL: `λ = rlctAt K x₀` (from the cite) -/

/-- **Link 1 (LOCAL; certificate §7.2/§7.5): `λ = rlctAt K x₀`.** The zeta-pole RLCT `λ = −s₀`
equals the cite-free **local** RLCT of the germ at `x₀` (`RLCT.Local`) — the bundled cite carries
`s₀ = −(rlctAt K x₀)`, so `λ = −s₀ = rlctAt K x₀`. This is the *local* tie: consistent (`s₀`,
`rlctAt K x₀` are both germ-at-`x₀` data) and DLN-admissible (defined for a non-isolated zero set).
The connection to R2a's *regional* `integrabilityThreshold K U` is the separate Bridge B
(`integrabilityThreshold_eq_localRlct_of_worst`), not this cite. -/
theorem rlctPair_lam_eq_rlctAt (S : ZetaSetup n) :
    (rlctPair S).lam = rlctAt S.K S.x₀ := by
  rw [rlctPair_lam, largestPole_eq_neg_rlctAt, neg_neg]

/-- **`λ` is positive.** `λ = −s₀` with `s₀ < 0` (the largest pole is negative). Equals the local
RLCT `rlctAt K x₀` by Link 1. -/
theorem rlctPair_lam_pos (S : ZetaSetup n) : 0 < (rlctPair S).lam := by
  rw [rlctPair_lam, neg_pos]
  exact largestPole_neg S

end RLCT
