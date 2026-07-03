# Statement cards — R2b zeta-pole RLCT `(λ, m)` on ONE bundled continuation cite

The expedition's crux build: the operator's **zeta-pole definition** of the RLCT (decision A), as a
*constructed* `(λ, m)` object resting on ONE bundled `@[cited]` continuation monument — replacing the
opaque `rlctReal` scalar axiom with something honest. Bare Mathlib-mirror namespace `RLCT`
(network-free). Built against `pp-zeta-cert/certificate.md`.

Files (all `lean/DLNFibre/Core/Analysis/RLCT/`, @ `expedition/rlct-r2b`):
`Zeta.lean` (built, cite-free) · `Cited.lean` (the one cite) · `Pair.lean` (extraction + Link 1).

---

## Card 1 — the local zeta function + convergence (BUILT, cite-free)

> **Claim.** For a germ `K` and cutoff `φ`, the local archimedean zeta `ζ_{K,φ}(s) = ∫ (K x)^s·φ(x) dvol`
> (complex power) has an integrable integrand for `Re s > 0`, when `K` is continuous, `φ` continuous
> with compact support. This is the half-plane of holomorphy — elementary, no continuation cited.
>
> - **Lean:** `RLCT.zeta` (def), `RLCT.zetaIntegrand` (def), `RLCT.zetaIntegrand_integrable`
>   (+ `continuous_cpow_germ`, `continuous_zetaIntegrand`, `hasCompactSupport_zetaIntegrand`).
> - **Gloss.** `zetaIntegrand K φ s x = (K x : ℂ)^s * (φ x : ℂ)`; `zeta K φ s = ∫ x, zetaIntegrand …`.
>   `zetaIntegrand_integrable (hK : Continuous K) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
>   (hs : 0 < s.re) : Integrable (zetaIntegrand K φ s)`.
> - **Proved.** Route: for `Re s > 0`, `x ↦ (K x:ℂ)^s` is continuous (`Complex.continuous_ofReal_cpow_const`
>   — at the zeros `0^s = 0`), so the integrand is continuous; its support ⊆ supp φ (compact), so
>   `Continuous.integrable_of_hasCompactSupport` applies.
> - **Cited.** none — `#print axioms zetaIntegrand_integrable = [propext, Classical.choice, Quot.sound]`.
> - **Faithfulness.** Smooth `φ` cutoff, **not** a raw indicator `1_U` (certificate §6.4): matches the
>   standard cited continuation theorem; the maximal pole is a robust germ invariant under smooth `φ`.
> - **Status.** sorry-free.

---

## Card 2 — the ONE bundled continuation cite (CITED: Atiyah 1970 + Saito/SLT)

> **Claim (the monument, as an `@[cited]` axiom).** For a real-analytic nonnegative germ `K` with
> `K x₀ = 0`, a smooth `φ` (`φ ≥ 0`, `φ x₀ ≠ 0`) supported inside a relatively compact open nbhd
> `U ∋ x₀` on which `K` is in the pole regime: `ζ_{K,φ}` continues meromorphically to `ℂ`; its poles
> lie in the left half-plane; there is a LARGEST pole `s₀ < 0` (maximal real part) of finite order
> `m₀ ≥ 1`, rational; **and `s₀ = −(integrabilityThreshold K U)`** (the bundled largest-pole = −rlct
> identity).
>
> - **Lean (verbatim axiom, hardened per Codex — locality + maximality + pole-regime):**
>
>       @[cited "Atiyah 1970 (CPAM 23:145-150) + Saito/SLT: continuation of ∫|F|^s φ, poles ℚ_{<0}, largest pole = -rlct"]
>       axiom cited_zeta_meromorphic_continuation {n : ℕ} (K φ : (Fin n → ℝ) → ℝ)
>           (x₀ : Fin n → ℝ) (U : Set (Fin n → ℝ))
>           (hK : AnalyticOnNhd ℝ K Set.univ) (hKnn : ∀ x, 0 ≤ K x) (hKx₀ : K x₀ = 0)
>           (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
>           (hφnn : ∀ x, 0 ≤ φ x) (hφx₀ : φ x₀ ≠ 0)
>           (hx₀U : x₀ ∈ U) (hUopen : IsOpen U) (hUcpt : IsCompact (closure U)) (hφU : tsupport φ ⊆ U)
>           (hpole : BddAbove (admissibleExponents K U)) :
>           ∃ (Z : ℂ → ℂ) (s₀ : ℝ) (m₀ : ℕ),
>             (∀ s : ℂ, 0 < s.re → Z s = zeta K φ s) ∧
>             MeromorphicOn Z Set.univ ∧
>             (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re < 0) ∧
>             (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re ≤ s₀) ∧
>             s₀ < 0 ∧ (∃ q : ℚ, s₀ = q) ∧ 1 ≤ m₀ ∧
>             meromorphicOrderAt Z (s₀ : ℂ) = ((-(m₀ : ℤ) : ℤ) : WithTop ℤ) ∧
>             s₀ = -(integrabilityThreshold K U)
>
> - **Cited — sources.** M. Atiyah, *Resolution of singularities and division of distributions*, Comm.
>   Pure Appl. Math. **23**(2) (1970) 145–150 (continuation of `∫|F|^s`, poles on `ℚ_{<0}`, via
>   real-analytic resolution — the paper's attribution, `main.tex` L1811). The "largest pole = −rlct"
>   packaging: SLT-facing (Saito arXiv:math/0702056; Watanabe 2009, CUP, zeta-function chapter). Bundled
>   as ONE cite = what the `(λ,m)` definition consumes.
> - **Why bundled (load-bearing, certificate §6.5).** A *bare* meromorphic-continuation axiom does NOT
>   give `s₀ = −rlct` — that identification needs the resolution/normal-crossing computation, so it is
>   IN the cited conclusion (as the paper's `propdefn` bundles it), not derived free from meromorphy.
> - **Location.** Module `…/RLCT/Cited.lean` (last name-component `Cited`) ⟹ the cordon LOCATION check
>   passes; the `RLCT` bare namespace is in the audit's first-party allowlist.
> - **Status.** the sole new axiom; `@[cited]`; sorry-free file.

---

## Card 3 — the RLCT pair `(λ, m)` + Link 1 (BUILT on the cite)

> **Claim.** `λ := −s₀` (positive, `= rlct_x`) and `m := poleOrder` (the pole order = the multiplicity
> `rlcm`) are extracted from the cite; and **Link 1**: `λ = RLCT.integrabilityThreshold K U`.
>
> - **Lean:** `RLCT.RLCTPair` (structure: `lam : ℝ`, `poleOrder : ℕ`), `RLCT.rlctPair` (def),
>   `RLCT.largestPole` / `RLCT.poleOrder` (the `Classical.choose` projections), `RLCT.largestPole_neg`,
>   `RLCT.one_le_poleOrder`, `RLCT.largestPole_eq_neg_threshold`,
>   `RLCT.rlctPair_lam_eq_integrabilityThreshold` (Link 1), `RLCT.rlctPair_lam_pos`.
>   Setup bundle: `RLCT.ZetaSetup` (germ + cutoff + the cite's hypotheses).
> - **Gloss.** `rlctPair S = ⟨-(largestPole S), poleOrder S⟩`. Link 1:
>   `(rlctPair S).lam = integrabilityThreshold S.K S.U`, proof `= −s₀ = −(−threshold) = threshold`
>   (`largestPole_eq_neg_threshold` + `neg_neg`). `rlctPair_lam_pos : 0 < (rlctPair S).lam` (from `s₀<0`).
> - **Proved.** All, modulo the ONE cite. `#print axioms rlctPair / largestPole / poleOrder /
>   rlctPair_lam_eq_integrabilityThreshold = [propext, Classical.choice, Quot.sound,
>   cited_zeta_meromorphic_continuation]` — the foundational three + the ONE cite, nothing else.
> - **Sign (certificate §6.1).** `λ = −s₀` positive — NOT the negative pole `s₀`. The zeta integrand is
>   `K^{+s}` (poles at negative `s`); R2a's threshold is `K^{−c}` (positive `c`); `s = −c`, `λ = c > 0`.
> - **`m ≠ θ` (certificate §6.7).** `poleOrder : ℕ` is the *analytic* pole order; the geometric count is
>   `Core.cTheta`/`numTop`. Separate names, separate types — never `def`-unified or coerced. `m` is off
>   the `½·codim` payoff's critical path (the payoff needs only `λ`).
> - **Hybrid tie (certificate §3.4).** `integrabilityThreshold` (R2a, cite-free) is the value the payoff
>   rides; Link 1 says it *equals* the zeta-pole `λ` **by the cite**. The continuation cite buys `m` +
>   the pole reading, not the `½·codim` (that is the separate Watanabe/Aoyagi bracket, `AoyagiCited`).
> - **Status.** sorry-free.

---

## Decorrelated Codex consult — findings ADOPTED (hardened the cite)

Fired `local-codex-consult` (gpt-5.x, xhigh) on the cited statement + sign/normalization, conclusion
withheld. Full answer: `codex/cite-answer.md`. Codex **confirmed** all 7 of my points (sign `λ=−s₀`
positive, `meromorphicOrderAt = −m₀` pole encoding, bundling `s₀=−rlct` is necessary/not free from bare
meromorphy, no second `½`, `m ≠ θ` safe, smooth-`φ` rationale) — and surfaced **three genuine fidelity
gaps in the axiom-as-first-written**, all now **fixed**:

1. **Locality.** `U`/`φ`/`x₀` were unrelated ⟹ `s₀ = −threshold` could fail both ways. FIXED: added
   `x₀ ∈ U`, `IsOpen U`, `IsCompact (closure U)` (relatively compact), `tsupport φ ⊆ U` — matching the
   paper's `propdefn` relatively-compact-open-nbhd (`main.tex` L1804).
2. **Maximality.** The conclusion asserted *a* pole `s₀`, not the *largest* ⟹ `largestPole` over-named.
   FIXED: added `∀ s, meromorphicOrderAt Z s < 0 → s.re ≤ s₀` (+ poles-in-left-half-plane
   `→ s.re < 0`). `RLCT.le_largestPole_of_pole` / `poles_re_neg` extract them; `largestPole` now earns
   its name.
3. **Pole-regime guard.** `integrabilityThreshold` is junk `0` off the pole regime. FIXED: added
   `BddAbove (admissibleExponents K U)` (R2a's own `name = content` guard).

These made the cite a *faithful* statement of the monument rather than an under-specified one — the
bedrock discipline: a cite must state the real theorem. Post-fix, all gates still green (below).

## Reviewer note (fidelity focus)

Independent fidelity check requested (controller-spawned reviewer): does the hardened Lean cite +
`RLCTPair` match the paper's `propdefn` + the certificate? Confirm: (a) `λ = −s₀` positive, not the
pole; (b) bundled `s₀ = −threshold` IN the cite; (c) `m = poleOrder` is the pole ORDER
(`meromorphicOrderAt = −m₀`), never a count, off the payoff path; (d) the hardened hypotheses
(analytic `K ≥ 0`, `K x₀=0`, locality `x₀∈U`/`IsOpen U`/rel.-compact/`tsupport φ⊆U`, smooth `φ≥0`,
`φ x₀≠0`, pole-regime `BddAbove`) + the maximality/left-half-plane conclusion faithfully scope the
monument; (e) no second `½`.

**Gates (post-hardening, all green):** `scripts/lb DLNFibre` ✔ (3854 jobs); `scripts/cited` =
`UNACCOUNTED=0 CITED=4 LOCATION=0` (3 Aoyagi + 1 continuation, all located); `scripts/sorries` =
`0 sorry, 0 #exit, 0 native_decide, 4 axiom` (all `@[cited]`); `#print axioms rlctPair /
rlctPair_lam_eq_integrabilityThreshold / largestPole / poleOrder = [propext, Classical.choice,
Quot.sound, cited_zeta_meromorphic_continuation]`; `zetaIntegrand_integrable` cite-free.

**Careful-checkpoint (operator-gated):** the landed `Cited.lean` axiom is surfaced to the operator
verbatim (Card 2, updated to the hardened form) before any merge into `rlct-foundation`.
