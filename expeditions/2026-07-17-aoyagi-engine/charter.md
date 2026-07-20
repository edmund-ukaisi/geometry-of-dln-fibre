<!-- CHARTER — the fixed invariant core of this expedition.
     READ THIS FIRST, every wake / every convening / every brief. Elder owns it; controller commits.
     EDIT IN PLACE, NEVER APPEND. Hard cap ~1 page. If it grows, it decays like the logs did.
     History lives in journal.md / compass.md; TRUTH lives here. Compaction distills TO this, never away.
     Checkpoint: 2026-07-20 (fresh start after the second chart-route drift). New phase NOT yet started. -->

# Charter — aoyagi-engine

## §0  The frame (goal #0 — the thing that dissolves the drift)
We are building **Aoyagi's resolution-of-singularities machinery as reusable mathematics**, stated at
**full generality** — objects useful *outside* the headline. The learning-coefficient theorem
(`aoyagi_learning_coefficient`) is a **corollary and a test**, NOT the objective. Steering by the
headline is what produced the drift (twice): it makes *reaching the headline cheaply* the gradient,
which rewards re-derivation, MVP shortcuts, and category-wrong charts. Steer by the objects.

**"Done" for an object** = stated at full generality + proven + witness shown in-file. Not "it lets a
downstream headline close."

## §1  The objects (the goals). PROVISIONAL — full-generality statements being finalised with the operator.
- **A. RLCT ideal-invariance (Aoyagi Lemma 1), two-sided.** `rlct(Σfᵢ²)` depends only on `⟨fᵢ⟩`.
  Foundational — legalises every ideal-preserving step. STATUS: one direction banked; two-sided open.
- **B. The product-ideal resolution** `⟨∏C⟩ = ⟨diag(b₁,…,b_M)⟩` (Aoyagi Cases 1&2, *regular* Q,P).
  The geometric heart. Two regimes: clean (width ≤ 2 — telescopes, cert'd) and **coupled corank ≥ 2**
  (width ≥ 3 — the frontier). STATUS: clean L≤3 on paper; coupled UNBUILT. **Not optional.**
- **C. Monomial-ideal RLCT** `= ½·min (h+1)/(2k)` (Newton). STATUS: largely built.
- **D. Codimension geometry** `codim{∏C=0} = minAdm = cCodim`, θ (top-component count),
  permutation-invariance (type-A quiver / Ext). STATUS: largely built in `Core`.
- **E. Analytic order ρ** (Aoyagi Lemmas 4–5, pole multiplicity). STATUS: unbuilt seam.
- Reductions R0/R1 (deepest point; product reduction → core): BUILT (bookkeeping).
- **Corollary/test:** `aoyagi_learning_coefficient = C/2`; `hbox` is its analytic shadow, never a
  separate goal — it falls out of A+B (or is decided false by them).

## §2  The progress bar (what may be *called* progress)
A progress claim is valid ONLY if it names **(a)** the §1 object it discharges AND **(b)** the legal
construction-category (§3). A green build, a closed leaf, a passed gate, or a re-derivation that
discharges **no** §1 object is **NOT progress** — it is motion. The controller re-states the object +
category before reporting progress; the elder gates every route and every progress-claim against §1–§3.

## §3  Standing math-warnings (the drift, named — the highest-suspicion classes)
- **The recurring category error (killed us twice):** a *diffeomorphism chart with a value/diagonalising
  map* (the α-atlas `LeafPullback`) is **category-FALSE** — no det-1 chart bounds the residual core
  (diagonalising a generic product needs a det-0 projection). Building one is not hard progress; it is a
  wrong-category object that passes det/cover/measure gates and only fails at the value consumer, late.
- **The four legal step-types** (the ONLY categories a construction may be; standing rule 1):
  (i) an ideal identity, (ii) a unit-Jacobian / measure-preserving change of variable, (iii) a blow-up
  substitution with tracked monomial Jacobian. Anything else — a value-computing chart, a lossy
  factorisation — is **STOP** at design time.
- **The gnote antidote** (worked.tex:191): the *per-layer recursion is the drift*; the reading is
  geometric — `rlct = ½·min_t codim S(t)`. Aoyagi's method is IDEAL-level (regular Q,P preserve the
  ideal), never a diffeomorphism of the loss.
- **Route D2 (mild-singularity dissolve) is DROPPED** — a shortcut that skips Aoyagi's machinery (the
  actually-useful thing). D1 (the codimension object) stays; D2 does not.
- **Retired: the α-atlas chart Engine** (`Engine/GeoAlphaGauge`, `ChartBridgeFaithful`, `GeoAtlasTransfer`).
  Its `sorry`s (`LeafPullback`, `leafDiagFrob_geoAtlasNorm`, `geoAtlasNorm_imageCover`) are category-false
  or off-path. **DO NOT FILL THEM.** Object B (ideal-level) is the replacement; reusable tree/det pieces
  are salvaged into B deliberately, never by closing a chart hole.

## §4  Durability
Read first, every cycle, by every role. Elder is sole author (holds the abstract-object frame; gates
against §1–§3); controller commits. `CLAUDE.md` points here. This file is what survives log growth.
