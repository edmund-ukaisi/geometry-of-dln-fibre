# Statement cards — R2b zeta-pole RLCT: the LOCAL cite + local `(λ, m)` + Bridge B

The expedition's crux build: the operator's **zeta-pole definition** of the RLCT (decision A), as a
*constructed* `(λ, m)` object resting on ONE `@[cited]` monument — replacing the opaque `rlctReal`
scalar. Re-adjudicated to the **three-way split** (certificate §7, after the earlier regional cite was
found *inconsistent* and then *DLN-inapplicable*): a **local** cite (Axiom A), a buildable **regional
bridge** (Bridge B), and the **global** DLN payoff (Theorem C, the existing cites). Bare Mathlib-mirror
namespace `RLCT` (network-free).

Files (all `lean/DLNFibre/Core/Analysis/RLCT/`, @ `expedition/rlct-r2b`):
`Zeta.lean` (built, cite-free) · `Local.lean` (cite-free local `rlctAt`) · `Cited.lean` (the one LOCAL
cite) · `Pair.lean` (extraction + local Link 1) · `Bridge.lean` (Bridge B, buildable/roadmapped).

## The three-way split (certificate §7.2 — why LOCAL, not regional)

The earlier cite bundled the **regional** identity `s₀ = −integrabilityThreshold K U`. That was an
*altitude confusion* and was **inconsistent** (the pinned continuation `Z` is holomorphic where a
far-away sharper zero forces `−threshold` to be a pole ⟹ `False`; rev-r2b `K=x²(x−2)⁶`). A sole-zero
patch restored consistency but **excluded the DLN fibre** (a connected positive-dim zero set is never a
sole zero). Fix: split into

- **Axiom A (LOCAL cite)** — `s₀ = −rlctAt K x₀`, purely local, no regional/sole-zero hypothesis.
  Consistent (both sides germ-at-`x₀`) and **DLN-admissible** (`rlctAt` is defined for a non-isolated
  zero set). Card 2.
- **Bridge B (buildable, not a cite)** — regional `integrabilityThreshold K U = rlctAt K x₀` under a
  boundary-regular `U` + a *worst-point* inequality (admits a connected fibre; forbids only a strictly
  worse-threshold zero). Card 4.
- **Theorem C (GLOBAL payoff)** — `rlct(K_B) = ½·codim` from the existing global Watanabe/Aoyagi cites
  (`AoyagiCited.lean`, `rlct_lossDLN_eq_half_codimRealFibre`), **not** by instantiating Axiom A at a
  fibre point. So the DLN payoff never rides the paper's open local conjecture (L1937). *Not this
  thread's file — noted for the record.*

---

## Card 1 — the local zeta function + convergence (BUILT, cite-free)

> **Claim.** For a germ `K` and cutoff `φ`, the local archimedean zeta `ζ_{K,φ}(s) = ∫ (K x)^s·φ(x)`
> (complex power) has an integrable integrand for `Re s > 0`, when `K` is continuous, `φ` continuous
> with compact support. The half-plane of holomorphy — elementary, no continuation cited.
>
> - **Lean:** `RLCT.zeta`, `RLCT.zetaIntegrand`, `RLCT.zetaIntegrand_integrable`
>   (+ `continuous_cpow_germ`, `continuous_zetaIntegrand`, `hasCompactSupport_zetaIntegrand`).
> - **Gloss.** `zetaIntegrand K φ s x = (K x : ℂ)^s * (φ x : ℂ)`; `zeta K φ s = ∫ x, zetaIntegrand …`.
>   `zetaIntegrand_integrable (hK : Continuous K) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
>   (hs : 0 < s.re) : Integrable (zetaIntegrand K φ s)`.
> - **Proved.** For `Re s > 0`, `x ↦ (K x:ℂ)^s` is continuous (`Complex.continuous_ofReal_cpow_const`
>   — at zeros `0^s = 0`), so the integrand is continuous; support ⊆ supp φ (compact) ⟹
>   `Continuous.integrable_of_hasCompactSupport`.
> - **Cited.** none — `#print axioms zetaIntegrand_integrable = [propext, Classical.choice, Quot.sound]`.
> - **Status.** sorry-free.

---

## Card 1b — the cite-free LOCAL RLCT `rlctAt K x` (BUILT, cite-free)

> **Claim.** The **local** integrability threshold of a germ `K` at a point `x`:
> `rlctAt K x = sSup { c ≥ 0 | K^(-c) locally integrable at x }` — the paper's `rlct_x(K)` (Def 4.1),
> distinct from R2a's **regional** `integrabilityThreshold K U`.
>
> - **Lean:** `RLCT.rlctAt` (def), `RLCT.localAdmissibleExponents` (def), `mem_localAdmissibleExponents`,
>   `zero_mem_localAdmissibleExponents`.
> - **Gloss.** `localAdmissibleExponents K x = {c | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}`
>   ("locally integrable at `x`" = integrable on *some* nbhd, `IntegrableAtFilter … (𝓝 x)`);
>   `rlctAt K x = sSup (localAdmissibleExponents K x)`.
> - **Why it matters.** This is the object the LOCAL cite identifies with the pole (`s₀ = −rlctAt K x₀`).
>   Being *local*, it is defined for a **non-isolated zero set** — so the cite is DLN-admissible.
> - **Cited.** none — `#print axioms rlctAt = [propext, Classical.choice, Quot.sound]`.
> - **Status.** sorry-free.

---

## Card 2 — the ONE bundled LOCAL cite (CITED: Atiyah 1970 + Saito/SLT)

> **Claim (the monument, LOCAL).** For a real-analytic nonnegative germ `K` with `K x₀ = 0`, a smooth
> `φ` (`φ ≥ 0`, `φ x₀ ≠ 0`) supported in a small open nbhd `U ∋ x₀`: `ζ_{K,φ}` continues
> meromorphically to `ℂ`; poles in the left half-plane; a LARGEST pole `s₀ < 0` (maximal real part) of
> finite order `m₀ ≥ 1`, rational; **and `s₀ = −rlctAt K x₀`** — minus the *local* RLCT. **One
> worst-point hypothesis on `supp φ`** (`hWorst`; certificate §7.5, round-5) — no regional / sole-zero
> / worst-in-U condition.
>
> - **Lean (verbatim axiom):**
>
>       @[cited "Atiyah 1970 (CPAM 23:145-150) + Saito/SLT (paper propdefn L1804): local ∫K^s φ continues meromorphically, poles ℚ_{<0}, largest pole = -rlct_{x₀}"]
>       axiom cited_local_zeta_pole {n : ℕ} (K φ : (Fin n → ℝ) → ℝ)
>           (x₀ : Fin n → ℝ) (U : Set (Fin n → ℝ))
>           (hK : AnalyticOnNhd ℝ K Set.univ) (hKnn : ∀ x, 0 ≤ K x) (hKx₀ : K x₀ = 0)
>           (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
>           (hφnn : ∀ x, 0 ≤ φ x) (hφx₀ : φ x₀ ≠ 0)
>           (hx₀U : x₀ ∈ U) (hUopen : IsOpen U) (hφU : tsupport φ ⊆ U)
>           (hWorst : ∀ x ∈ tsupport φ, rlctAt K x₀ ≤ rlctAt K x) :
>           ∃ (Z : ℂ → ℂ) (s₀ : ℝ) (m₀ : ℕ),
>             (∀ s : ℂ, 0 < s.re → Z s = zeta K φ s) ∧
>             MeromorphicOn Z Set.univ ∧
>             (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re < 0) ∧
>             (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re ≤ s₀) ∧
>             s₀ < 0 ∧ (∃ q : ℚ, s₀ = q) ∧ 1 ≤ m₀ ∧
>             meromorphicOrderAt Z (s₀ : ℂ) = ((-(m₀ : ℤ) : ℤ) : WithTop ℤ) ∧
>             s₀ = -(rlctAt K x₀)
>
> - **`hWorst` (worst-point on `supp φ`) is soundness-critical — without it the cite is `False`.** `s₀`
>   is a `supp φ`-quantity (`Z` sees all of `supp φ`, so `s₀ = −inf_{x∈supp φ} rlct_x`); a wide `φ`
>   covering a *separate sharper* zero forces a pole `Z` does not have at `−rlctAt K x₀`
>   (`K = x²(x−1)⁸`, `φ` over both zeros ⟹ `s₀ = −1/8 ≠ −1/2`). `hWorst` makes that `inf = rlctAt K x₀`.
>   It is the paper's "`U` small enough" as a *threshold* condition — **not** a sole-zero condition, so
>   it **admits the DLN fibre**: at a smooth fibre point `rlct_x` is locally constant along the
>   connected fibre, so `hWorst` holds with equality and the cite fires at `K_B` (non-vacuity witness).
> - **The `U` carries NO threshold** — it only localizes `φ`'s support (`x₀ ∈ U`, `U` open,
>   `tsupport φ ⊆ U`). The conclusion is the germ-at-`x₀` datum `rlctAt K x₀`; `hWorst` is the only
>   family-constraint, and it is over `supp φ`, not a region.
> - **Cited — sources.** M. Atiyah, *Resolution of singularities and division of distributions*, CPAM
>   **23**(2) (1970) 145–150 (continuation of `∫|F|^s`, poles `ℚ_{<0}`, real-analytic resolution — the
>   paper's attribution L1811); "largest pole `= −rlct_x`" packaging: Saito arXiv:math/0702056;
>   Watanabe 2009, CUP. ONE `@[cited]` axiom.
> - **Location.** Module `…/RLCT/Cited.lean` (last component `Cited`) ⟹ cordon LOCATION passes; `RLCT`
>   bare namespace in the audit's first-party allowlist.
> - **Status.** the sole new axiom; `@[cited]`; sorry-free file.

---

## Card 3 — the RLCT pair `(λ, m)` + LOCAL Link 1 (BUILT on the cite)

> **Claim.** `λ := −s₀` (positive, `= rlctAt K x₀`) and `m := poleOrder` (the pole order = the
> multiplicity `rlcm`), extracted from the cite; and **Link 1 (LOCAL)**: `λ = RLCT.rlctAt K x₀`.
>
> - **Lean:** `RLCT.RLCTPair` (`lam : ℝ`, `poleOrder : ℕ`), `RLCT.rlctPair`, `RLCT.continuation` /
>   `RLCT.largestPole` / `RLCT.poleOrder` (the `Classical.choose` projections), `RLCT.largestPole_neg`,
>   `RLCT.one_le_poleOrder`, `RLCT.le_largestPole_of_pole`, `RLCT.poles_re_neg`,
>   `RLCT.meromorphicOrderAt_largestPole`, `RLCT.largestPole_eq_neg_rlctAt`,
>   `RLCT.rlctPair_lam_eq_rlctAt` (Link 1), `RLCT.rlctPair_lam_pos`. Setup: `RLCT.ZetaSetup`.
> - **Gloss.** `rlctPair S = ⟨-(largestPole S), poleOrder S⟩`. Link 1:
>   `(rlctPair S).lam = rlctAt S.K S.x₀`, proof `= −s₀ = −(−rlctAt) = rlctAt` (`largestPole_eq_neg_rlctAt`
>   + `neg_neg`). `rlctPair_lam_pos : 0 < (rlctPair S).lam` (from `s₀ < 0`).
> - **Proved.** All, modulo the ONE cite. `#print axioms rlctPair / rlctPair_lam_eq_rlctAt /
>   largestPole / poleOrder = [propext, Classical.choice, Quot.sound, cited_local_zeta_pole]`.
> - **Sign.** `λ = −s₀` positive — NOT the negative pole. `K^{+s}` zeta / `K^{−c}` threshold, `s = −c`.
> - **`m ≠ θ`.** `poleOrder : ℕ` the *analytic* order; geometric count `Core.cTheta`/`numTop`. Separate
>   names/types, never unified; `m` off the payoff's critical path (the payoff needs only `λ`).
> - **Status.** sorry-free.

---

## Card 4 — Bridge B: regional = local at a worst point (BUILT assembly + roadmapped analysis)

> **Claim.** If `x₀` is a *worst singularity* on `closure U` (`∀ x ∈ closure U, rlctAt K x₀ ≤
> rlctAt K x`), then the regional threshold equals the local one: `integrabilityThreshold K U =
> rlctAt K x₀`. Buildable analysis — **NOT a cite** (certificate §7.2/§7.5).
>
> - **Lean:** `RLCT.integrabilityThreshold_eq_localRlct_of_worst` (`Bridge.lean`).
> - **Gloss / hypotheses.** `hworst` (worst-point inequality — **admits a connected fibre**; forbids
>   only a strictly worse-threshold zero); `hSubThreshold` = (F1-easy: sub-threshold everywhere ⟹
>   regionally integrable, a finite-subcover fact); `hIntegrableCap` = (F1-converse: regionally
>   integrable ⟹ `c ≤ rlctAt K x₀`, needs boundary-regular `U`); `hbdd`, `h0mem` (pole regime + `0`
>   admissible). Concl: `integrabilityThreshold K U = rlctAt K x₀`.
> - **Proved.** The equality is a **sorry-free** `csSup` antisymmetry from the hypotheses (`csSup_le`
>   for `≤`; `le_of_forall_lt` + density + `le_csSup` for `≥`). **Axiom-clean**: `#print axioms = [propext,
>   Classical.choice, Quot.sound]` — no cite.
> - **Roadmapped (NOT sorry-ed).** The two analytic facts `hSubThreshold` / `hIntegrableCap` are taken
>   as **explicit named hypotheses** (the F1 lift, certificate §7.1). Discharging them for a concrete
>   ball/box `U` — from local integrability + compactness of `closure U` + boundary regularity — is a
>   focused real-analysis rung, tractable, deferred (flagged to the controller). The card does **not**
>   claim them proved; it proves the *assembly* and names the analytic core. The 1-D `|t|` witness
>   (`integrabilityThreshold_absGerm = 1`) already validates the value the bridge lands on.
> - **Not circular** (certificate §7.2, Codex-confirmed): `rlctAt` is *local* integrability,
>   `integrabilityThreshold K U` is *regional* — distinct objects; the hypothesis constrains the local
>   family, the conclusion is the regional value. (Assuming the *equality* as a black box would be
>   circular; the *worst-point inequality* + F1 facts are not.)
> - **Status.** sorry-free.

---

## Decorrelated review + the five-round hardening

The cite was hardened across FIVE rounds before landing the correct form (all pre-merge, via the
careful-checkpoint + decorrelated review — controller + rev-r2b + pp-zeta-cert + Codex):

1. **Codex (xhigh)** on the first form fixed 3 gaps — locality, maximality, pole-regime.
2. **rev-r2b + Codex** found the regional cite **inconsistent** (`s₀ = −integrabilityThreshold K U`
   proves `False`; `K=x²(x−2)⁶`). Patched with open-`U` sole-zero.
3. **rev-r2b** found open-`U` still leaks (a `∂U` zero satisfies it vacuously but blows the `U`-integral
   from inside; `K=x²(x−1)⁸`). Tightened to `closure U`.
4. **controller + pp-zeta-cert §7** found the sole-zero (any-U) fix, though consistent, **excludes the
   DLN fibre** — altitude confusion. **Restated the cite LOCALLY** (`s₀ = −rlctAt K x₀`, drop the
   regional conclusion), factored the regional tie into buildable Bridge B, routed the DLN payoff
   through the global Theorem C.
5. **controller + pp-zeta-cert §7.5 (CONFIRMED, this round)** found the local form still loose: `s₀` is
   a `supp φ`-quantity, so a wide `φ` covering a *separate sharper* zero breaks `s₀ = −rlctAt K x₀`
   (`K=x²(x−1)⁸`, φ over both ⟹ `s₀=−1/8`). **Final fix: `hWorst : ∀ x ∈ tsupport φ, rlctAt K x₀ ≤
   rlctAt K x`** — a worst-point condition on `supp φ` (the paper's "U small enough"), admitting the
   DLN fibre (equal-threshold zeros give `≤` with equality; not sole-zero). Consistent +
   DLN-admissible + no reliance on the open local conjecture. Root cause (supp φ is itself a region)
   now closed.

**Lesson (in-repo).** The cordon accounts axioms but does **not** check their consistency; a cited
`∃`-axiom needs a consistency review (hunt an instance satisfying every hypothesis where the conclusion
fails). Here the source of the contradiction was an *altitude* mismatch (regional conclusion, local
apparatus) — the split cures it at the root.

## Reviewer note (fidelity focus)

Independent fidelity check requested. Confirm: (a) `λ = −s₀` positive; (b) the cite is stated
**locally** (`s₀ = −rlctAt K x₀`) with the single worst-point-on-`supp φ` hypothesis `hWorst`
(no regional / sole-zero condition) — hence consistent (`hWorst` pins the `supp φ`-inf to `rlctAt K x₀`)
+ DLN-admissible (`hWorst` holds with equality on a connected fibre); (c) `m = poleOrder` the pole
ORDER, never a count, off the payoff path; (d) Bridge B is axiom-clean, its `closure U` worst-point
hypothesis admits a connected fibre, and its two F1 facts are honestly named hypotheses (not sorry-ed,
not baked as the equality); (e) `rlctAt` / `zetaIntegrand_integrable` cite-free.

**Gates (all green):** `scripts/lb DLNFibre` ✔; `scripts/cited` = `UNACCOUNTED=0 CITED=4 LOCATION=0`
(3 Aoyagi + the 1 LOCAL cite `cited_local_zeta_pole`); `scripts/sorries` = `0 sorry, 4 axiom` (all
`@[cited]`); `#print axioms` on `rlctPair`/Link-1/`largestPole`/`poleOrder` = std-3 + the one cite;
`rlctAt`, `zetaIntegrand_integrable`, Bridge B all axiom-clean (std-3).

**Careful-checkpoint (operator-gated):** the landed LOCAL `Cited.lean` axiom (Card 2, verbatim) is
surfaced to the operator before any merge into `rlct-foundation`.
