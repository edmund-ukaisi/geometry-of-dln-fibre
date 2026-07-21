<!-- CHARTER — the fixed invariant core of this expedition.
     READ THIS FIRST, every wake / every convening / every brief. Elder owns it; controller commits.
     EDIT IN PLACE, NEVER APPEND. Hard cap ~1 page. If it grows, it decays like the logs did.
     History lives in journal.md / compass.md; TRUTH lives here. Compaction distills TO this, never away.
     Checkpoint: 2026-07-20 (fresh start after the second chart-route drift). New phase NOT yet started.
     dev-merge DONE (5f0700e27): dev's cite-free determinantal geometry in-tree; kill-target = cited_aoyagi_lower_ax.
     §1 FINAL — operator-confirmed 2026-07-21 ("detag permitted"); recorded in journal tick 43x+. -->

# Charter — aoyagi-engine

## §0  The frame (goal #0 — the thing that dissolves the drift)
We are building **Aoyagi's resolution-of-singularities machinery as reusable mathematics**, stated at
**full generality** — objects useful *outside* the headline. The learning-coefficient theorem
(`aoyagi_learning_coefficient`) is a **corollary and a test**, NOT the objective. Steering by the
headline is what produced the drift (twice): it makes *reaching the headline cheaply* the gradient,
which rewards re-derivation, MVP shortcuts, and category-wrong charts. Steer by the objects.

**"Done" for an object = the four-part blueprint bar (VERIFIED, never assumed):**
- **(i) GENERALITY.** Shown the object COLD (no headline), an independent mathematician agrees it is a
  natural/canonical object at the RIGHT generality — weakest hypotheses that suffice, in usable form.
  "The headline needs it" is not a reason; that motivation alone FAILS.
- **(ii) STRIKE-ABLE LEAVES.** Every proof leaf bottoms out at a statement we'd bet true and can sketch
  (hard proof-ENGINEERING, not new math); a leaf hiding open math is DECOMPOSED until the open part is
  ISOLATED and honestly NAMED a frontier leaf — never disguised as strike-able. The
  engineering-vs-new-math boundary is itself a deliverable.
- **(iii) COMPLETENESS / RISING SEA.** Blueprint the WHOLE object, not the headline's slice; a complete
  blueprint DISSOLVES critical-path guessing (leaves parallelize; you cannot mis-identify a critical path
  you are building all of). The structural antidote to MVP/headline-steering.
- **(iv) SOUNDNESS / NO SMELL.** Every statement is mathematically SOUND: true, correctly quantified (no
  missing hypothesis that makes it false, no spurious one that makes it vacuous), name = content — a
  mathematician reading the STATEMENT (not the proof) does not wince. DISTINCT from (ii): (ii) is about
  the remaining PROOF, (iv) about the STATEMENT — a leaf can be strike-able yet its statement subtly
  false (the worst case; "a sorry with a wrong statement misleads" — fix wrong statements first).

## §1  The objects (the goals). FINAL — operator-confirmed 2026-07-21.
- **A. RLCT ideal-invariance (Aoyagi Lemma 1), TWO-SIDED.** `rlct(Σfᵢ²)` depends only on the ideal `⟨fᵢ⟩`
  (both inclusions). Foundational — legalises every ideal-preserving step. STATUS: the ≤ direction banked
  (`rlctAt_mono`); the two-sided ideal-only dependence is OPEN and Mathlib-absent.
- **B. The product-ideal resolution** `⟨∏C⟩ = ⟨diag(b₁,…,b_M)⟩` (Aoyagi Cases 1&2, *regular* Q,P). The
  geometric heart. TWO regimes: **clean** (width ≤ 2 — telescopes; verified exact at (2,2,2,2), incl.
  depth-3) and **COUPLED corank ≥ 2** (width ≥ 3 — the b_i share divisors; **the frontier this project
  has dodged for multiple expeditions**). STATUS: clean verified; coupled UNBUILT. **NOT OPTIONAL — the
  case fidelity to Aoyagi's mechanism requires; never scoped out, never a footnote.**
- **C. Monomial-ideal RLCT** `= ½·min (h+1)/(2k)` (Newton polyhedron), in full generality. STATUS: largely
  built (clean); the coupled/general computation owed alongside B.
- **D. Codimension geometry** `codim{∏C=0} = minAdm = cCodim`, θ (top-component count),
  permutation-invariance (type-A quiver / Ext). STATUS: banked in `Core` (`minAdm_eq_cCodim` axiom-clean;
  θ unconditional) — reinforced by dev's cite-free determinantal geometry.
- **E. Analytic order ρ** (Aoyagi Lemmas 4–5): the RLCT / zeta-pole MULTIPLICITY — **NOT** the quiver
  (C,θ)-count. STATUS: unbuilt seam. **DEPRIORITISED but KEPT IN REACH** (operator, 2026-07-20): her
  order falls out of the SAME A–D machinery, so E stays a named reachable node (interface sketched,
  completeness holds); its content build is deferred, never boxed out.
- Reductions R0/R1 (deepest point; product reduction → core): BUILT (bookkeeping).
- **Corollary/test:** `aoyagi_learning_coefficient = C/2`; `hbox` is its analytic shadow, never a
  separate goal — it falls out of A+B (or is decided false by them).

## §2  The progress bar (what may be *called* progress)
A progress claim is valid ONLY if it names **(a)** the §1 object it discharges AND **(b)** the legal
construction-category (§3). A green build, a closed leaf, a passed gate, or a re-derivation that
discharges **no** §1 object is **NOT progress** — it is motion. The controller re-states the object +
category before reporting progress; the elder gates every route and every progress-claim against §0–§3.

## §3  Standing math-warnings (the drift, named — the highest-suspicion classes)
- **The recurring category error (killed us twice — the PROOF the ideal route is forced):** no
  det-1 / a.e.-injective chart diagonalises the loss on an open set (each `(∏C)ᵢⱼ` is a nonzero poly,
  ≢0 on a dense open; exact diagonalisation forces ≡0, a non-open det-0 projection). The value LOWER
  bound is therefore **not** a chart change-of-variables — it is IDEAL-level. A value-computing chart
  passes det/cover/measure gates and fails only at the value consumer, late.
- **Reuse RESULTS; the ideal route replaces the chart route.** The retired α-atlas chart Engine
  (`Engine/`, RETIRED.md, un-wired/un-built) has category-false holes — **DO NOT FILL THEM**. Salvage
  correct kernel-checked tree/det pieces into Object B by re-importing the specific module, never by
  closing a chart hole.
- **The cite is not the proof.** The one in-library kill-target is `cited_aoyagi_lower_ax`
  (½·codim ≤ rlctGlobal(lossDLN) — the DLN lower/finiteness half). GOAL: PROVE it via A+B+C and DELETE it
  (`rlctGlobal` is built cite-free; `codim_ℝ=codim_K` proved). Citing it — or reporting any payoff that
  rests on it — discharges NO §1 object; it is motion. `cited_watanabe_upper_ax` = the origin DIVERGENCE
  (banked) + R0 — a PROOF-TARGET candidate, not settled-external. `cited_local_zeta_pole`: off-path.
  Endpoint: `aoyagi_learning_coefficient` with NO Aoyagi axiom.
- **Reuse dev's determinantal-geometry RESULTS for D (proved, cite-free); do NOT adopt L&R's
  quiver-representation THEORY** (Gabriel / orbit-closures / Ext-codim / the (C,θ) fibre-geometry) as a
  subject to build — the paper's OTHER programme, outside the RLCT-value scope.
- **The gnote antidote** (worked.tex:191): the *per-layer recursion is the drift*; the reading is
  IDEAL-level (`rlct = ½·min_t codim S(t)`; regular Q,P preserve the ideal), never a diffeomorphism of
  the loss. Route D2 (mild-singularity dissolve) is DROPPED; D1 (the codimension object) stays.
- **NO minimum-viable-ing a named hard part** (esp. coupled-B). "Toric-trivial / no extra blow-ups /
  elementary" clean headlines about an unbuilt object are UNVERIFIED until probed with decorrelated
  exact-algebra at the KNOWN failure cases (coupled corank≥2). The tractability probe is a CHECK on a
  committed build, never a gate that scopes the object down.

## §4  Durability
Read first, every cycle, by every role. Elder is sole author (holds the abstract-object frame; gates
against §0–§3); controller commits. `CLAUDE.md` points here. This file is what survives log growth.
