# The owed-math audit — worked reproduction vs paper vs build

**Charge (operator, 2026-07-21):** comb `aoyagi-2023-worked.tex` against the paper and the
expedition's build; list everything still OWED — paper claims leaned on that are neither
Lean-proven nor battery-verified nor consciously deferred; transcription-only sites;
silent scope-narrowings; needed-but-out-of-scope material.

**Auditor:** elder (comprehension seat). **Tree state audited:** expedition tip `7d7d7a266`
(A/C/D/E-interface + corollary-reduction landed sorry-free; remaining engine sorries =
`rlctAt_sumSqFam_eq_iInf_charts` + `exists_coreResolution`).

**Method.** (1) Full read of the reproduction (907 lines) against the Lean tree; (2) full
page-image verification of the paper pp.14–22 THIS PASS (poppler now installed at root; the
seats lacked it — the F5 image-residual class is herewith closed for every load-bearing
site); (3) cross-check against the thread-27/28/31 certificates and the battery
(`g-monument-mval-instances.py`, re-run green).

---

## A. Page-image verification ledger (audit item ii — the F5 class)

| Site | Paper page | Status |
|---|---|---|
| Def 3 sign (T-D) | p.08 | image-verified (earlier arc) |
| Thm 4 statement | p.14 | **image-verified THIS PASS** (matches worked.tex incl. φ-hypotheses, ≤ direction) |
| Inductive statement: ideal identity, `b_i` recursion, Jacobian ledger `u^{M_{s,k}-1}`, t̃ definition | p.15 | **image-verified THIS PASS** |
| T-profile totality display (the (T-F) defect claim site) | p.15 (re-derived pp.16/17/20) | **image-verified THIS PASS** — the claim is EXPLICIT, not implicit |
| Case-1(1)/(2) exponents `M' = M + J₁(M^{(S+1)}−J)`; Case-1(2) label INHERITANCE | pp.16–17 | **image-verified THIS PASS** |
| Case-2 exponent `(M(S)−J)(M^{(S+1)}−J)` (T-C) + RAW-width head-reset label (T-E) | pp.19–20 | **image-verified THIS PASS** — T-C pinned; the raw-vs-inherited asymmetry confirmed on the page |
| Terminal `M_{s,k}` formula + t̃=0 read-off + the (H_j, S_j) reparametrisation | p.22 | **image-verified THIS PASS** (matches worked.tex §candidates exactly) |
| Lemma 3 quadratic (N-1) | p.24 | image-verified (earlier arc; false-typo retracted) |
| Lemmas 4–5 envelopes/count | pp.25–26 | red-team-verified from images (`verify-repro-s4s5.md`) |
| ρ-side Case-1(2) increment fine-bookkeeping | pp.16–17, 25–26 | image-referenced only — **consciously deferred with E** (off the rlct critical path) |

**Conclusion (ii):** no load-bearing transcription-only site remains. The single
image-referenced remainder (ρ bookkeeping) is deferred with Object E by charter §1-E.

---

## B. The ranked OWED list

Ranking: O1 highest (the destination cannot be reached without it) → O8 lowest
(interpretive/documentation). Each item: claim → paper site → what leans on it → status →
recommendation.

### O1. The min-over-charts change-of-variables (the boxed rule's atlas half) — BUILD (in strike)
- **Claim:** `rlct(∑F²) at x₀ = min over covering charts of the weighted per-chart threshold at the chart origin.`
- **Paper:** the boxed S2 display, "min over charts U" (worked.tex §1.3; paper §3 method).
- **Leans on it:** the entire engine value; the corollary; the kill-target.
- **Status:** the sorried frontier leaf `rlctAt_sumSqFam_eq_iInf_charts`. Statement
  elder-ratified at v4.1/v4.2 (dom-wide certificates + a.e.-injectivity + compact-dom
  a.e.-cover); both directions have complete proof sketches (≥: per-point subset-divisor
  min + compact finite subcover + area-formula subadditivity; ≤: injective CoV divergence
  transport). Heavy proof-engineering, NOT new mathematics.
- **Recommendation:** BUILD (scheduled; B strike lane). Nothing to re-scope.

### O2. The monument: the coupled-atlas existence for the DLN core — BUILD (in progress, seat-B)
- **Claim:** Aoyagi's Cases-1&2 recursion, at coupled corank ≥ 2, inhabits the certified
  `Resolution` atlas record for the concrete flattened core, with qipMin min-attainment.
- **Paper:** pp.14–22 (the mountain).
- **Leans on it:** `exists_coreResolution`; the corollary; the kill-target.
- **Status:** sorried. Combinatorial half (Mval-attainment across leaves) salvaged
  kernel-checked from the retired Engine tree (elder-ratified route, conditions C1
  import-boundary / C2 kill-set incl. (2,2,3,2) + (2,2,1,1)); mechanism battery-verified at
  (3,3,4)/(4,4,4)/(3,3,3,2,2) (threads 27/28, Gröbner-level); the GEOMETRIC fields (analytic
  g, dom-wide two-sided RegionRepresents, hjac, hg_inj, atlas hcover) are the true remaining
  frontier. hcover build-vs-cite is deferred-as-sequencing (elder C3): it remains a
  build-target; any cite decision is operator-gated.
- **Recommendation:** BUILD (in progress). The thread-31 certificate is the playbook; the
  (T-F) totality defect must not be transcribed.

### O3. General-rank Theorem 3 + Theorem 4 (the r > 0 payoff) — DEFER, named
- **Claim:** the paper's Thm 1/2 hold at arbitrary true rank r (the regular-block shift
  `(−r²+r(H¹+Hᴸ⁺¹))/2` + core), via Thm 3 (gauge-slice normal form) and general Thm 4.
- **Paper:** Thm 3 (pp.10–12), Thm 4 (p.13–14), Thms 1–2.
- **Leans on it:** NOT the charter corollary (which is the zero-product fibre, r = 0, where
  the reduction is landed sorry-free via GlobalHomog + flatten). Only the full-generality
  paper reproduction leans on it.
- **Status:** tracked-open sorries on the older Skeleton carrier (`product_reduction` /
  gauge-slice #44; D1 ≥-leg `rlctAt_deepest_le_of_optimal`). Consciously deprioritised.
- **Recommendation:** DEFER, keep named in ROADMAP. If the operator wants the paper's full
  Thm 2 formalised, this is the single largest additional build (Morse-with-parameters
  constant-rank charts); it shares no dependency with the kill-path.

### O4. Monotone-d scope on the corollary — BUILD-LATER (cheap-to-moderate), named
- **Claim:** the paper's theorem has no width-ordering hypothesis; permutation-invariance
  of (C, θ) is a headline surprise.
- **Paper:** Thm 2 (any widths); L&R §perm-invariance.
- **Leans on it:** the corollary carries `hd : Monotone d` (visible, from the banked
  `cCodim_eq_qipMin`).
- **Status:** named future leaf (LearningCoefficient module docstring). The cCodim-side
  perm-invariance is banked; the LOSS-side transport `rlctGlobal(lossDLN d) =
  rlctGlobal(lossDLN (d∘σ))` needs a measure-preserving relabelling of `Rep_d` — the same
  class as the landed flatten, plus transposition (the product reverses under reordering —
  the honest route is the transpose anti-isomorphism, `‖M‖_F = ‖Mᵀ‖_F`).
- **Recommendation:** BUILD after the monument lands (independent, parallelisable; a good
  first-strike for a new seat). Until then the hypothesis is visible — honest, not silent.

### O5. cCodim ↔ the printed Thm-2 / clean q²−m² form, ∀(L,M) — DEFER with a documented boundary
- **Claim:** `½·Mval_min` equals the paper's printed Thm-2 expression (equivalently the
  clean form `½(∑q² − ∑m²)`) for all widths.
- **Paper:** Thm 2 + Lemma 3 + Def 3 (modulo T-D/F-1 defects).
- **Leans on it:** NOTHING on the kill-path (the destination names C = the codimension,
  which IS `cCodim`; `cCodim = qipMin = minAdm` is proven). Only the "expose the paper's
  printed formula as a Lean corollary" ambition leans on it.
- **Status:** exact-enumeration-verified (L ≤ 6, bounded widths; `verify-def3-underspec.md`
  Check 4); the reproduction's own (F-1) qmark names it the "still-owed theorem".
- **Recommendation:** DEFER consciously; it is a self-contained integer-program identity
  (balanced-split optimality of the QIP) — a clean future pen-and-paper + formalise unit if
  the operator wants the printed form on the record. Annotated at the claim site.

### O6. Object E content: the order ρ — DEFERRED per charter §1-E (already ruled)
- **Claim:** ρ = a(ℓ−a)+1, and ρ = the zeta pole multiplicity.
- **Paper:** Lemmas 4–5, pp.25–26.
- **Leans on it:** nothing on the rlct kill-path.
- **Status:** `boxedOrder`/`one_le_boxedOrder`/`aoyagiPoleOrder`/distinction built; the
  combinatorial aggregate identity and the analytic pole-order identification are the two
  named seams (the latter blocked by Mathlib-absent meromorphic continuation).
- **Recommendation:** keep deferred; the interface stays reachable (compliant).

### O7. The zeta/free-energy interpretation layer — CITE, permanently (scope note)
- **Claim (two-part):** (a) Def 1's φ-form threshold is φ-independent when φ(w*) ≠ 0, and
  equals the φ-free Lebesgue-local threshold the Lean `rlctAt` defines; (b) the RLCT so
  defined IS Watanabe's learning coefficient (free-energy asymptotics), and the Kullback
  function's RLCT equals the polynomial loss's RLCT (same ideal, Lemma 1 — the *statistical*
  step from `K(w)` to `‖∏A−B‖²`).
- **Paper:** Def 1 + §1 (worked.tex:126–150).
- **Leans on it:** the READING of the final theorem as "the learning coefficient of the DLN"
  — not the theorem's own truth (the Lean statement is self-contained about `rlctGlobal`).
- **Status:** (a) is standard-material and buildable (a bump-function comparison — two-sided
  bounds by sup/inf of φ on a small ball); (b) is the analytic SLT monument (cited by
  design, `RLCT.Cited` / zeta interface).
- **Recommendation:** (a) BUILD-CHEAP if the operator wants the φ-form fidelity closed —
  else note it; (b) CITE permanently (charter destination already words it this way).
  Neither is silent: both now annotated.

### O8. Thread-28's residual kill-instance (deeper mixed coupled shapes) — PROBE-ON-DEMAND
- **Claim:** the single divisibility chain survives ALL coupled shapes (not just the
  verified (3,3,4)/(4,4,4)/(3,3,3,2,2) classes).
- **Paper:** implicit in the inductive statement (per-chart principality at S = L+1).
- **Leans on it:** the monument's `hchain` field at full generality.
- **Status:** the ∀-general chain IS forced by the b_i closed form (b_i = ∏_{t̃<i} u —
  thread-31 structural induction), so the general survival is derived, not instance-bound;
  the thread-28 flag was about the *mechanism* reproducing it at deeper mixes.
- **Recommendation:** no pre-emptive build; the monument's own construction discharges it,
  and the C2 kill-set instances guard the adapter. Keep the thread-28 boundary note in the
  certificate (done).

---

## C. Silent scope-narrowing check (audit item iii) — VERDICT: none silent

Every narrowing found is now VISIBLE at its site: B = 0 / r = 0 (annotated at Thm 3/Thm 4 +
hero fnote; general r = O3); `Monotone d` (hypothesis in the signature + hero fnote; O4);
monomial-chain hypothesis on the boxed rule (the DivChain guard — this is a *faithful*
restriction, it is the paper's own b-chain invariant, and the coupled counterexample shows
it cannot be dropped); the junk-0/measurability guards on Lemma 1 (Lean-convention honesty,
dischargeable at every use; annotated); single-terminal-chart → atlas (the v3→v4 fix — the
record is now MORE faithful than the first blueprint, not less). The paper's φ-form vs the
Lean φ-free threshold is O7(a) — now annotated, the one previously-unannotated narrowing
this audit surfaced.

## D. Out-of-scope-but-needed check (audit item iv) — VERDICT: nothing missing

The destination (CLAUDE.md) needs: Rep/mult/fibres (banked), the (C,θ) quiver forms +
permutation invariance (banked, dev's determinantal geometry), rlct = C/2 (the engine, O1+O2),
and the Aoyagi-equality cite-kill (the engine's purpose). No paper section outside the
reproduction's scope is load-bearing for that destination. The L&R paper's Poincaré-series
form of C and θ is banked on the Core side; Aoyagi's ρ is O6. The free-energy layer is O7(b),
cited by design.

---

## E. Summary for the operator

After this pass the reproduction carries its verification state on its face: every
theorem/lemma has a Lean-status note; every known paper defect (T-A/T-C/T-D/T-E/T-F, F-1,
N-1) is ledgered at its claim site with its witness; the page-image residual class is
closed. The genuinely owed mathematics is TWO Lean leaves (O1, O2 — both scheduled, both
elder-ratified statements) and FOUR conscious deferrals (O3 general-r, O4 non-monotone,
O5 printed-form identity, O6 order ρ) plus the permanent cite O7(b). Nothing was found
that the build leans on silently.
