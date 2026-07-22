# Paper-fidelity review — Aoyagi + Lehalleur–Rimányi vs the codebase

**Commission:** operator, 2026-07-23 — "a very thorough paper fidelity review: list all the objects,
intermediate objects, results, caveats, calculations the paper has, cross-check against the codebase
(covered / not), then judge whether the uncovered ones should be covered." **Author:** elder (synthesis
+ judgment). **Enumeration + cross-check:** three read-only scout lanes (raw outputs in
`threads/fidelity-review/`). **Method:** verify-not-recall — the scouts grepped/read the Lean, checked
`sorry`/`axiom`/`@[cited]` and the AxCheck registry; the elder made the final judgments and independently
weighed the load-bearing ones. Where a full `#print axioms` was not run (read-only + build cost), STATUS is
from the bare-sorry census + attributes + AxCheck's per-root comments; noted where it matters.

Judgment codes: **DONE** (proven, covered) · **IN-FLIGHT** (the active re-bake owns it) ·
**SHOULD-COVER-LATER** (post-summit | next-expedition runway) · **RIGHTLY-SKIPPED** (out of scope — why) ·
**CITED-BY-DESIGN** (monument-class cite the destination sanctions).

---

## SUMMARY VERDICT

**1. The destination's mathematical content is largely PROVEN, and often more than the paper.** The whole
quiver translation (§§2–4: Gabriel, Kostant partitions, rank patterns, the Voight/Ext codimension, the
orbit hierarchy + closures, the multiplication map + loci + fibre codimension + θ-component count) and all
three forms of `(C,θ)` (§§5–7: the Poincaré series `thm:Pseries`, the QIP `thm:QIP`, the explicit
closest-lattice-point formula) **plus the surprising permutation invariance** are sorry-free in
`DLNFibre.Core`. In several places the repo **proves what the paper cites**: the Poincaré identity via a
Durfee/pentagon peel (paper cites Reineke + a spectral sequence), the orbit closures via a determinantal
identity (paper cites Abeasis–del Fra), the closest-point count via `sumSqValues` (paper cites
Conway–Sloane). This is a strong coverage result and the destination's "new content" (the geometric
codimension) is genuinely in hand.

**2. The RLCT payoff `rlct = C/2` (§8) is CITED at full generality — by design — with the codimension side
fully proven.** The rlct is the **built** `rlctGlobal (lossDLN d B)` (Def 8.1(i), cite-free); the analytic
equality `rlctGlobal = ½·codim_ℝ` is `le_antisymm` of exactly two located `@[cited]` axioms
(`cited_watanabe_upper_ax`, `cited_aoyagi_lower_ax`). Everything on the codimension side — the real↔complex
transfer, `codim mult⁻¹(B) = C + r(d₀+d_N−r)`, `codim = cCodim = C` — is proven, zero-cite. This matches
the destination (`CLAUDE.md`: the Aoyagi `rlct = ½·codim` equality is Cited). The **current expedition**
additionally builds the from-scratch resolution engine to *kill* `cited_aoyagi_lower_ax`: proven clean at
L≤2, general-L conditional, and open (`sorryAx`) at the summit — which is the monument.

**3. The single genuine open frontier in the staked boundary is the MONUMENT (Object B — the coupled
corank≥2 resolution), and it is IN-FLIGHT (the faithful `N_p` re-bake).** Every "SHOULD-COVER-NOW" the
scouts flagged on the RLCT side resolves to this one object (the inductive invariant, the Jacobian ledger,
Case 1/2, the coupled diag(b), `exists_coreResolution`). It is charter §1.B, owned by the active
`canonNormalizationOf`/`N_p` re-bake (arch-C render + seat-L4C + pnp-transport). Nothing *else* in the
current staked boundary is an unowned open hole.

**4. The honest fidelity caveats are three modeled-vs-categorical gaps and one analytic seam — all named,
none overclaiming.** (a) `Ext` is a concrete cochain model (`deformationExt1`); the codimension *numbers*
are proven unconditionally, but "this model *is* the quiver `Ext¹`" is DEFERRED in-docstring. (b) The
locally-trivial *bundle* of `lem:rank_vs_fibers` is NOT built — `FibreBundleLocallyTrivial` self-disclaims
the name (per-pivot local product + flatness only); its two used consequences (fibre codim, θ-count) are
independently proven. (c) The type-A quiver is a `Fin`-index model, not a `Quiver` instance (the needed
forms landed). (d) The analytic θ / rlcm pole-multiplicity value + meromorphic continuation are ABSENT — the
Mathlib-gap ρ-seam, deferred by design (monument-class). The precision discipline is holding: the modeled
names self-disclaim rather than overclaim. The one to keep honest is the `Ext` identification.

**Bottom line:** coverage of the destination is high and honest; the codimension geometry (the paper's new
content) is proven; the RLCT equality is cited exactly as the destination sanctions; the one open frontier
is the monument, in-flight; the remaining gaps are named runway (general-r, real geometry, the analytic
seam, printed-form/categorical niceties) with no silent overclaim.

---

## A. Aoyagi RLCT-resolution side (worked.tex + preprint)

Three lanes coexist for `rlct = C/2`: **engine** (`aoyagi_learning_coefficient_via_engine`, monument sorry),
**cited** (`AoyagiCited`, 2 axioms, codim proven), **skeleton** (general-r, dirty root).

| item | worked.tex | STATUS + Lean | mismatch | JUDGMENT (elder) |
|---|---|---|---|---|
| Lemma 1 — RLCT depends only on the ideal (Object A) | 163–199 | PROVEN sorry-free `rlctAt_sumSqFam_*` (IdealInvariance) | +junk-0 `LocallyNullZeros` + measurability guards (sound, Lean-rpow) | **DONE** |
| boxed S2 monomial rule `λ=min(h+1)/2k` (Object C) | 213–248 | PROVEN sorry-free `monomialSumSq_wrlctAt_eq` (MonomialRLCT) | needs `DivChain` (Aoyagi's own b-chain invariant) | **DONE** (stale docstring calling it a frontier — nit) |
| Lemma 2 block-elimination (Q₁/Q₂) | 402–421 | PROVEN sorry-free `block_elimination` (Skeleton) | — | **DONE** |
| deepest-point homogeneity domination (Thm 4 / D1) | 511–553 | PROVEN instance `deepest_le_of_homogeneous_core`, `rlctGlobal_eq_rlctAt_zero_of_homogeneous` | all-vars homogeneity instance; paper's sub-block form not reproduced (not needed) | **DONE** (own instance suffices) |
| `M_{s,k}=Mval(t)=codim S(t)`; `divisorMin=cCodim` (Object D bridge) | 668–684 | PROVEN sorry-free chain `divisorMin_eq_cCodim`/`minAdm_eq_cCodim`/`cCodim_eq_qipMin` | — | **DONE** |
| flatten `exists_flatten`/`canonFlatten` (block-respecting reindexing) | 484–498 | PROVEN sorry-free (LearningCoefficient) | canonFlatten PIN (the e-fix this round — the ∀-e/he_lin form was false) | **DONE** (fidelity-corrected this round) |
| min-over-charts CoV `rlctAt=iInf charts` (Object O1) | 686–698 | PROVEN sorry-free rel. structure `rlctAt_sumSqFam_eq_iInf_charts` (ProductResolution) | worked.tex lists it as still-open — stale (folded into Chart field obligations) | **DONE** (rel. the monument's chart certs) |
| Thm 3 peel regular part, general r (L2) | 425–479 | STATED-sorried general-r `product_reduction`/`deepest_regular_core_normal_form` (Skeleton); r=0 PROVEN `coreReduction` | general-r open; only r=0/B=0 landed | **SHOULD-COVER-LATER** (next-exp; off the r=0 kill-path) |
| **inductive invariant diag(b)·[E_J|D_J] + b-chain + Jacobian ledger + Case 1/2 + coupled diag(b) + Object B existence** | 562–698 | STATED-sorried — the monument (`exists_coreResolution`; MonumentAtlas 11 sorries; `N_p` re-bake in `canonNormalizationOf`/`CanonShear`/`Case1Wire`/`Case2Wire`) | the coupled corank≥2 frontier, charter §1.B | **IN-FLIGHT** (owner: the N_p re-bake — arch-C + seat-L4C + pnp-transport) |
| θ order = a(ℓ−a)+1 — combinatorial half | 912–957 | PROVEN combinatorial `aoyagiPoleOrder`/`chainHeight` chain (clean-three) | analytic pole-multiplicity ABSENT (Mathlib-gap) | **DONE** (combinatorial) / analytic → below |
| Def 1 order θ as zeta pole-multiplicity (analytic) | 150–152 | ABSENT — no pole-order operation | Mathlib lacks meromorphic continuation | **SHOULD-COVER-LATER** (next-exp; the ρ-seam, P7, monument-class) |
| Watanabe upper `λ≤½codim` | (payoff) | CITED `cited_watanabe_upper_ax` | — | **CITED-BY-DESIGN** (universal SLT, permanent) |
| Aoyagi lower `½codim≤λ` (DLN-specific) | (payoff) | CITED `cited_aoyagi_lower_ax` | — | **CITED-BY-DESIGN now, TARGETED** (the engine monument aims to delete it; removable if Object B lands) |
| paper defects surfaced (Def-3 (T-D) sign typo; T-profile totality (T-F) false; Case-2 raw-width (T-E)) | various | MODELED-only (batteries + image-verified); Lean records carry no field the false claims could corrupt | — | **RIGHTLY-SKIPPED** (defects documented; fix = `lambdaCore`/running-min; immune by construction) |

## B. Lehalleur–Rimányi §§1–4 (quiver translation + mult map + loci)

| item | main.tex | STATUS + Lean | mismatch | JUDGMENT (elder) |
|---|---|---|---|---|
| Rep_d, mult, Σ^r, fibre (the setting) | 125–142 | PROVEN `Core/Setup.lean` | over any CommRing (wider than paper) | **DONE** |
| Gabriel: iso ↔ G-orbit; orbits ↔ Kostant partitions (Cor 2.9) | 299–380 | PROVEN `rankPattern_eq_iff_orbit`, `orbitKostantEquiv` | — | **DONE** |
| indecomposables / Krull–Schmidt / lace diagrams | 311–536 | MODELED — interval modules + barcode; `realizerD` for lace; no categorical classification / lace object | needed forms landed; classification not named | **RIGHTLY-SKIPPED** (concrete realizer suffices) / name the classification → later |
| rank patterns ↔ orbits; Prop 3.1 cumul↔diff inversion | 551–575 | PROVEN `diff_cumul`/`cumul_diff`, `rankFn_eq_iff_orbit`, `RealizableRank` | — | **DONE** |
| Voight lemma: normal slice ≅ Ext(M,M) | 631 | MODELED — codim consequence proven (`VoigtDischarge`); slice≅Ext iso not stated; **categorical-Ext identification DEFERRED** | `deformationExt1` is a cochain MODEL of Ext | **SHOULD-COVER-LATER** (post-summit/upstreaming — the modeled-vs-categorical `Ext` gap; numbers proven) |
| Cor 3.5 codim formula `Σ m·m`; Ext-indicator `1[i<u≤j+1≤v]` | 641–658 | PROVEN unconditional `codimRepCanonical_orbitRankLocus_eq_multSum_unconditional`; `finrank_deformationExt1_interval` | CharZero+Infinite | **DONE** (numbers); Ext-identity is the modeled Ext (above) |
| orbit hierarchy + closures `O_s⊆Ō_r ⟺ s≤r` (Thm 3.x) | 706–717 | PROVEN `image_orbitRankLocus_eq_repClosure_orbitSet` + monotone | paper CITES Abeasis–del Fra; **Lean proves it** | **DONE** (better than the paper) |
| effect of additional longest roots (Thm 3.4) | 686 | PROVEN consequence `codimForm_update_corner` corner-blind + `cCodim_rankShift` | slice-iso only via modeled Ext | **DONE** (needed consequence) |
| Σ^r stratification; Cor irred components (a) closure (b) ↔ min elts | 787–806 | PROVEN `productRankLocusLE_eq_iUnion_orbitRankLocus`, `minimalPrimes_sigmaIdeal_eq` | Infinite k | **DONE** |
| lem:sigma_non_empty (Σ^r≠∅ ⟺ 0≤r≤min d) | 762 | PROVEN in pieces (⟸ needs N≥1); not one packaged iff | — | **SHOULD-COVER-LATER** (post-summit; bundle the iff — cheap) |
| lem:rank_0 (Σ⁰_{d−r}↪Σ̂^r; dim/codim shift) | 816 | PARTIAL — codim/count shift PROVEN; explicit dim closed-form + scheme injection not named | — | **SHOULD-COVER-LATER** (post-summit; name the dim closed form) |
| **lem:rank_vs_fibers — locally-trivial bundle; comps bij; fibre codim** | 844 | fibre codim + θ-count PROVEN; **locally-trivial bundle NOT** (`FibreBundleLocallyTrivial` self-disclaims: per-pivot local product + flatness) | the paper's bundle claim is weaker in Lean; consequences recovered | **SHOULD-COVER-LATER** (post-summit; the used consequences are DONE, the full bundle is a fidelity-completeness item) — keep the disclaiming name |
| thm:base_field (ℝ↔ℂ transfer; claim 3 real-analytic-mfld dim) | 607 | PARTIAL — dim-invariance present; the 3-claim package (esp. claim 3) not formalized | works via CharZero/Infinite/AlgClosed hyps | **SHOULD-COVER-LATER** (next-exp; claim 3 is real geometry) |
| rmk:real_points (θ over ℝ, disconnected real comps); cor:min_ud (smooth AND connected) | 860–867 | ABSENT (real-analytic components; connectedness not formalized) | — | **SHOULD-COVER-LATER** (next-exp; genuinely new real-geometry content) |
| ex:222324, ex:first_example (worked examples) | 581–771 | PARTIAL — (2,2,2) is a running witness; the rest not enumerated | — | **RIGHTLY-SKIPPED** (illustrative; (2,2,2) covered) |

## C. Lehalleur–Rimányi §§5–9 ((C,θ) three forms + perm invariance + payoff)

| item | main.tex | STATUS + Lean | mismatch | JUDGMENT (elder) |
|---|---|---|---|---|
| Pochhammer `𝒫`; `Q^r_ud`; lem:Qs_codim (extract C,θ) | 878–923 | PROVEN `Core/QSeries*` | power-series `ℤ⟦X⟧` model (faithful) | **DONE** |
| **thm:Pseries** (Poincaré-series form of (C,θ)) | 929 | PROVEN `thm55` (general r) | — | **DONE** |
| the spectral-sequence route; `𝒫=P(H*BGL)` interpretation | 962–992 | ABSENT — reached ALGEBRAICALLY instead (Durfee/pentagon `QSeriesFivegon`/`QSeriesDurfee`) | proof-route only | **RIGHTLY-SKIPPED** (result proven a different way — better) |
| **cor:PermutationInvariance** of (C,θ) | 1114 | PROVEN `cCodim_comp_perm`, `numTop_comp_perm` | — | **DONE** (the headline "surprise", fully covered) |
| **thm:QIP** (codim=min QIP; θ=#minimisers) | 1155 | PROVEN `cCodim_eq_qipMin` + `numTop_zero_card_eq_qipNumMinimisers` | Monotone d (lifted to arbitrary d in CThetaArbitrary) | **DONE** |
| lem:horiz_rep (weakly-incr ⇒ horizontal-lace rep) | 1230 | PROVEN narrowed (minimiser only) `minimiser_isHL` | paper: EVERY partition; Lean: only the minimiser (the direction QIP needs) | **SHOULD-COVER-LATER** (post-summit; narrowed form suffices) |
| **thm:main-codim** explicit codim + fibre codim + count (§7) | 1735 | PROVEN 3 parts (`cCodim_eq_cValue_comp_sort`, `codimRepCanonical_fibre_eq_cCodim_add_shift`, `numTop_eq_cTheta_comp_sort`) | `cValue`=rounding closed form, proven `=cCodim` but not syntactically the paper's fractional expression | **DONE** (value); form-identity → later |
| closest-point count `k=binom(m,δ)` (Conway–Sloane) | 1659 | PROVEN `cTheta = choose(qipM,δ)` via `sumSqValues` | paper CITES Conway–Sloane; Lean proves | **DONE** (better than the paper) |
| the paper's fractional-form codim expression (thm:main-codim / lem:delta / prop:Dhat) | 1694–1735 | value-equivalent (`cValue`), NOT form-identical; fractional parts recast as Int rounding residues | — | **SHOULD-COVER-LATER** (post-summit; a cosmetic `cValue = paper-fractional-form` bridge) |
| Def 8.1 rlct (built object) + `K^DLN_B` + `rlct≤½codim` | 1787–1876 | PROVEN `rlctGlobal` (cite-free) + connectors; `≤` = `cited_watanabe_upper_ax` | — | **DONE** (def/connectors) / upper = CITED-BY-DESIGN |
| **thm:aoyagi-rlct `rlct=C/2`** (the payoff) | 1889 | CITED general (`AoyagiCited`, 2 axioms, codim proven) + from-scratch L≤2 clean, general-L conditional (`hbox`), summit `sorryAx` (the monument) | — | **CITED-BY-DESIGN** (general) + **IN-FLIGHT** (from-scratch general-L = the monument) |
| rlcm pole-order value formula `m²{S̃/m}(1−{S̃/m})…` | 1895 | ABSENT/DEFERRED (`poleOrder` defined; value not proven) | the analytic ρ-seam | **SHOULD-COVER-LATER** (next-exp; monument-class seam, P7) |
| Appendix A: avoiding-ideal characterization of (C,θ) | 1946–1982 | ABSENT (avoiding ideal not built); a DIFFERENT chain-height characterization of θ IS built (`chainHeight_boxPart`) | — | **RIGHTLY-SKIPPED** (paper's "added bonus", least-efficient route; a different faithful characterization exists) |
| absent worked examples (ex:N8, ex:closestpoint, ex:q-series full, constant-d) | various | ABSENT (`#eval`s not run) | — | **SHOULD-COVER-LATER** (post-summit hygiene; cheap `decide`/`#eval` non-vacuity checks) |

---

## JUDGMENTS, grouped (with owners)

**IN-FLIGHT — the one open frontier in the staked boundary (owner: the active N_p re-bake).**
Object B / the monument: the coupled corank≥2 resolution — the inductive `diag(b)` invariant, the Jacobian
ledger, Case 1/2, `exists_coreResolution`, the faithful `N_p` normalization. This is charter §1.B and the
`sorryAx` under `aoyagi_learning_coefficient_via_engine`. Owner: arch-C (render) + seat-L4C (build) +
pnp-transport (certificate). No new commissioning needed — it is the current work.

**SHOULD-COVER-LATER — named runway (nothing here is a hole in the *current* staked boundary).**
- *Next-expedition (new math / new content):* the general-r lane (Thm 3 product reduction; the r>0
  transport) [P3]; the analytic ρ-seam (θ pole-multiplicity + rlcm value + meromorphic continuation) [P7,
  Mathlib-gap]; real geometry (thm:base_field claim 3; cor:min_ud connectedness; rmk:real_points real-θ).
- *Post-summit (proven-in-value, owed in form/packaging):* the printed-form equivalences (Thm 2 clean form,
  `cValue = paper-fractional-form`, the O5 closed-form bridge); the categorical-`Ext` identification
  (numbers proven; `deformationExt1` = quiver `Ext¹` deferred); the full locally-trivial bundle (consequences
  proven); lem:horiz_rep full generality; the bundled `lem:sigma_non_empty` iff + `lem:rank_0` dim closed
  form; the absent worked examples as `#eval` non-vacuity checks; the Gabriel classification naming.

**RIGHTLY-SKIPPED (out of scope, with reason).** Definitional objects; motivational identities
(`𝒫`=cohomology); the paper's *proof routes* the repo replaces with algebraic proofs (spectral sequence,
Reineke, Abeasis–del Fra, Conway–Sloane — the *results* are DONE, the routes skipped); figures + prose
remarks; the documented paper defects (Def-3 sign typo, T-profile totality, Case-2 raw-width — surfaced,
and the Lean is immune by carrying no corruptible field); Appendix A's avoiding ideal (least-efficient
route; a different faithful θ-characterization is built); the `Fin`-index quiver model (encoded directly).

**CITED-BY-DESIGN (monument-class, the destination sanctions).** `cited_watanabe_upper_ax` (universal SLT
upper bound — permanent); `cited_local_zeta_pole` (meromorphic continuation — Mathlib-gap, off-path);
`cited_aoyagi_lower_ax` (the DLN lower bound — cited-NOW but **targeted** by the engine monument; removable
if Object B lands). Hironaka resolution existence is not a standing cite — the engine *builds* the specific
resolution (that build is the monument).

---

## CROSS-CUTTING FIDELITY FINDINGS (the name=content watch)

1. **The modeled-vs-categorical gaps are honestly named — keep them so.** `Ext` (`deformationExt1`, cochain
   model), the fibre bundle (`FibreBundleLocallyTrivial`, self-disclaimed), the quiver (`Fin`-index). In each
   the *numbers/consequences the destination needs* are proven; the *categorical/structural identification*
   is deferred in-docstring. This is the precision discipline working. The one to keep honest: `Ext` — the
   codimension formula is unconditional, but do not let `deformationExt1` ever be *named* as `Ext¹` without
   the identification lemma. (No live overclaim found.)

2. **The RLCT payoff has three coexisting lanes; the destination's definition-of-done picks the cite lane
   with the engine as the stretch.** Cited (general, 2 axioms, codim proven) · engine (kills the Aoyagi
   cite; L≤2 clean, summit-open) · skeleton (general-r, dirty). The `rlct = C/2` headline is honest only
   read as: codimension side proven zero-cite; the analytic equality cited (Watanabe + Aoyagi), with the
   Aoyagi half under active from-scratch attack. Any exposition of the payoff must carry that caveat
   co-located (charter §3, "the cite is not the proof").

3. **The analytic seam is the real Mathlib-gap.** θ-as-pole-multiplicity and the rlcm value formula need
   meromorphic continuation Mathlib lacks; correctly deferred (monument-class). The combinatorial θ
   (`a(ℓ−a)+1` = chain-height of the binding poset) IS built and faithful — but it is a *different* object
   from the analytic pole-order, and the two must not be conflated (the repo respects this via
   `ThetaOrderDistinction`).

4. **Staleness nits (docstring-level, low priority):** worked.tex lists the min-over-charts CoV as still-open
   (it is sorry-free); the Object-C `monomialSumSq_wrlctAt_eq` docstring calls itself a `@[blueprint]`
   frontier (it is proven sorry-free). Fix at next touch of those files.

---

## METHOD / PROVENANCE
Raw lane outputs (durable): `threads/fidelity-review/lane-A-aoyagi.md`, `lane-B-lr-quiver.md`,
`lane-C-lr-payoff.md`. Not `#print axioms`-forced (read-only); the load-bearing "PROVEN sorry-free" claims
were cross-read by the elder against the AxCheck registry + the bare-sorry census. SHOULD-COVER-NOW items
return to the controller for commissioning (per the commission's read-only rule); this review changes no
statements.
