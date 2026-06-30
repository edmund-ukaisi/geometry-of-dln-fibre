# P0 recon — determinantal-atlas: current-state map, Mathlib coverage, build-vs-cite verdict, refined ladder

**Scout thread P0.** Worktree `…/.claude/worktrees/det-atlas`, branch `expedition/det-atlas-p1` (off post-FL-III `dev`). Blind to `expedition/aoyagi-full`.
Mathlib pin `v4.29.0` (rev `8a178386…`), store at `/home/ubuntu/.lake-shared/8a178386…/packages/mathlib/Mathlib`. Whole Lean tree is **sorry-free / axiom-free / native_decide-free** (`python3 scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom`).

This recon gates the rung ladder. **Headline findings:**
- **The expedition is overwhelmingly a re-home + de-DLN-ify job, not a fresh build.** The overlap API (P1.a) and the minor↔rank cover (P1.b/c) already exist in-repo, DLN-free, sorry-free, over arbitrary `CommRing`/field. The residue-field-rank bridge (the recon-gated P2.d crux) is **already fully proved** for the DLN instance.
- **The build-vs-cite verdict (P2.d):** the residue-field-rank bridge is **detail-at-scale, BUILD it** (already done; de-DLN-ify is mechanical). But the *literal* "bare Mathlib `FiberBundle`" capstone is **not the right target** — Mathlib's only `FiberBundle` is topological. The honest capstone is a **bespoke affine/Zariski local-triviality predicate** (`IsZariskiLocallyTrivialAffineProduct`), which `FibreBundleHeadline` already nearly instantiates. Decorrelated Codex (xhigh) confirms.

---

## 1. Current-state map — what exists, and how DLN-fused

Classification key: **(i)** already-general / reusable-as-is · **(ii)** mechanically de-DLN-able (plain matrices/rings, wrapped in DLN naming) · **(iii)** genuinely DLN-specific (stays).

### 1a. The overlap / localization API — (i) ALREADY BUILT, DLN-free, over arbitrary `R`

**`Core/FibreBundleTransition.lean` § `Abstract` + `TripleOverlap` is P1.a, already done** (`variable {R : Type*} [CommRing R]`, no DLN object anywhere in the section):

| decl | statement | status |
|---|---|---|
| `awayOverlap f g` | `Localization.Away (algebraMap R (Away f) g)` = the overlap ring `O(D(f)∩D(g))` (= `Away (f*g)` by Mathlib `IsLocalization.Away.mul'`) | (i) |
| `awayOverlapTransition f g` | canonical `awayOverlap f g ≃ₐ[R] awayOverlap g f` via `IsLocalization.algEquiv` at `powers (f*g)` | (i) |
| `awayOverlapTransition_commutes` / `_symm` / `_trans_symm` | the three pairwise cocycle laws (normalization, symmetry, round-trip = id) | (i) |
| `chartToSwappedOverlap` + `awayOverlapTransition_restrict_left` | overlap-LOCAL restriction: the transition is the canonical chart-`f` map on the overlap (the genuine overlap-local content, not merely common-target) | (i) |
| `awayTriple f g h`, `isLocalization_awayTriple` | triple overlap ring `O(D(f)∩D(g)∩D(h))` = `Away (f*g*h)` | (i) |
| **`awayTriple_cocycle`** | **the triple-overlap cocycle `g_{fg}∘g_{gh}∘g_{hf} = id`, PROVED** (localization initiality, `IsLocalization.algHom_subsingleton`) | (i) |

All cocycle laws ride on **localization initiality** (only `R`-algebra endo of a localization is `id`) — no extensionality on heavy types. **This is P1.a in finished form; the rung is an L7 re-home to `Core/RingTheory/Localization/Overlap.lean`, not a build.** Only 2 in-repo consumers (`FibreBundleLocallyTrivial[Full]`), so re-home is low-risk.

The same file also has the **plain-matrix instantiation** (`§ MinorChart`, `variable {k} [Field k]`): `detMinorPoly s t` = det of the `(s,t)` minor of Mathlib's generic matrix `Matrix.mvPolynomialX`; `eval_detMinorPoly` (evaluates to `(M.submatrix s t).det`); `minorChartTransition`. DLN-free — this is part of P1.b/c.

### 1b. The minor↔rank API + cover — (i) ALREADY GENERAL, field-level

- `Core/Matrix/RankMinors.lean` (namespace `Matrix`, mirrors `Mathlib.LinearAlgebra.Matrix.Rank`): `rank_le_iff_forall_submatrix_det_eq_zero` (over any field, `A.rank ≤ r ↔` all `(r+1)`-minors vanish), `submatrix_det_eq_zero_of_rank_le`, `exists_submatrix_det_ne_zero_of_le_rank`, `rank_map_eq_of_injective` (rank under injective field hom). **No DLN; no sorry; Mathlib-grade.**
- `Core/RankMinorCover.lean`: `exists_invertible_minor_of_rank` (rank-`r` matrix has an invertible `r×r` minor — the cover keystone), `minorChart s t := {M | IsUnit (M.submatrix s t).det}`, `rankEqLocus r := {M | M.rank = r}`, `rankEqLocus_subset_iUnion_minorChart` (set-level cover of `Mat^{=r}` by pivot charts). **Plain matrices over a field; (i).** (Lives in namespace `DLNFibre.Core` but is network-free — its own docstring calls it "a spin-out candidate".)
- `Core/RankLocusClosed.lean`, `Core/RankNormalFormDim.lean`, `Core/DeterminantalChart.lean` (block-rank additivity `rank_fromBlocks_zero` — **absent in Mathlib**; pivot Schur rank criterion `rank_fromBlocks_eq_card_iff_schur`; chart parametrization), `Core/SchurChartIff.lean` (`rank_le_iff_schur_eq` / `rank_eq_iff_schur_eq`, field-level Schur chart-membership iff), `Core/SchurGauge.lean` (`schurComplement_normal_form` over any `CommRing`): all **(i) or (ii)**, the matrix/Schur content general, the DLN flavour only in which ring the coords sit.

### 1c. The DLN rank-stratum + base presentation — (ii)/(iii)

- `productRankLocusLE d r` (`Core/Setup.lean`) = `{A : Tuple d | (mult d A).rank ≤ r}` · `sigmaIdeal d r` (`Core/SigmaComponents.lean`) = vanishing ideal of `canonicalCoord '' productRankLocusLE` · `dStratum n m` (`Core/DeterminantalStratumDim.lean`) = `![n,m]` (the N=1 single-arrow vector) · `RepCoord d` (`Core/OrbitCodim.lean`) = `Σ i, Fin (d i.succ) × Fin (d i.castSucc)`. These are the de-DLN-ify *targets*. **Consumer counts:** `RepCoord` 79 files (pervasive — do NOT attempt to remove), `productRankLocusLE` 22, `sweepSigmaRing` 24, `sigmaIdeal` 18, `dStratum` 8, `chartDsigAt` 9.
- `DeterminantalChartRing.lean` (bordered Schur identity over any CommRing — (ii); height = `(n−r)(m−r)` via cited Brick A — (iii)), `DeterminantalStratumDim.lean` (det-variety dim `r(n+m−r)` at N=1 — (iii), rides cited Brick A), `DeterminantalBaseElimination.lean` / `DeterminantalBasePresentation.lean` (block reindex + height-squeeze ideal presentation — (iii)).

### 1d. The fibre-bundle layer — (iii) bespoke ring-level; NO Mathlib `FiberBundle` used

The bundle layer is entirely **bespoke ring-level** (localization isos + tensor trivializations). Mathlib's `FiberBundle`/`Trivialization`/`FiberBundleCore` appear **nowhere** in the tree (they are topological — see §2). State:

- **Per-pivot local triviality — PROVED.** Every rank-`=r` prime sits in a chart with `Away (chartDsigAt s t) ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing` (S4, `FibreBundleLocallyTrivial`), upgraded to over-base `≃ₐ[SchurLoc] …` + chartwise flatness (S4b, `FibreOverBaseTriv`).
- **Base-side overlap cocycle — PROVED** (`FibreBundleLocallyTrivialFull`, instantiating §1a at `R = sweepSigmaRing`, `f = chartDsigAt s t`), with the **C1 scheme bridge**: a prime in `basicOpen (chartDsigAt s t)` has injective selectors *for free* (`injective_of_mem_basicOpen_chartDsigAt`, since a non-injective minor det is `0`), so `pivotDatumOfMemBasicOpen` needs no external hypothesis.
- **Projection compatibility (R5) — CLOSED** (`FibreProjectionCompat`: `schurToDsigAt` factors through `mult`'s comorphism).
- **Residue-field-rank bridge (S1) — PROVED** (`FibreRankBridge`, see §3).
- **Target-side cocycle round-trip — the ONE residual** (`FibreTargetOverlap`): the transition *object* `targetProductOverlapTransition` is built; the round-trip law `(I,J)∘(J,I)=id` is deferred. Mathematically it is the LANDED base-side `chartOverlapTransitionK_trans_symm` transported; the blocker is **`AlgEquiv.trans_assoc`/`trans_refl`/`refl_trans` absent in v4.29** (only `self_trans_symm`/`symm_trans_self`), and the pointwise `ext` route hits a kernel timeout on the `@[reducible]` double-localized type. **Not a sorry** — an unstated theorem documented as a roadmap residual.

---

## 2. Mathlib v4.29 coverage map

| library piece the expedition needs | Mathlib v4.29? | exact API | gap → in-repo / new |
|---|---|---|---|
| **Determinantal ideal** (ideal of `(r+1)`-minors) | **ABSENT** | — (only generic matrix below) | new object; (no Mathlib `determinantalIdeal`/`idealOfMinors`) |
| **Generic matrix** `mvPolynomialX` + `eval₂` | **present** | `Matrix.mvPolynomialX`, `mvPolynomialX_map_eval₂`, `…mapMatrix_eval` (`LinearAlgebra/Matrix/MvPolynomial.lean`) | reuse; in-repo `detMinorPoly` builds on it |
| **`Matrix.rank` minor characterization** | **ABSENT** | only the *cardinal* submatrix bound `cRank_submatrix_le`; `rank_of_isUnit` | filled by `Core/Matrix/RankMinors.lean` (i) |
| **Block-rank additivity** `rank_fromBlocks` | **ABSENT** | (Schur *det* present, rank not) | filled by `DeterminantalChart.rank_fromBlocks_zero` (i) |
| **Schur complement (det)** | **present** | `det_fromBlocks₁₁`/`₂₂`, `fromBlocks₁₁Invertible`/`₂₂Invertible` (`Matrix/SchurComplement.lean`) | reuse; rank-via-Schur is in-repo (`SchurChartIff`) |
| **`Localization.Away` + iterated isos** | **present (structural)** | `IsLocalization.Away.mul`/`mul'` (`Away x` then `Away y` = `Away (x*y)`), the two `Away (y*x)`/`(x*y)` **instances**, `commutes`, `IsLocalization.algEquiv` (same-submonoid `S ≃ₐ[R] Q`), `algEquivOfAlgEquiv`, `Away.mapₐ`/`awayMapₐ`, `liftAlgHom`. **No `awayMul`/`mulEquiv`/`awayAwayₐ` combinator** — but not needed. | **assembled** in-repo `FibreBundleTransition` §1a; P1.a = re-home |
| **`AlgEquiv` groupoid laws** | **PARTIAL** | has `self_trans_symm`, `symm_trans_self`, `trans_apply`, `symm_trans_apply`, `coe_ringEquiv`; **MISSING `trans_assoc`, `trans_refl`, `refl_trans`** (these exist only at bare `Equiv`, `Equiv.trans_assoc`) | **NEW**: a 3-lemma `ext x; rfl` spin-out (Codex-vetted, §3) — unblocks the target cocycle |
| **`FiberBundle` / local-triviality** | **topological only** | `Topology/FiberBundle/{Basic,Trivialization}.lean` need `[TopologicalSpace B]`; **NO `AlgebraicGeometry` `FiberBundle` / Zariski-local-triviality / `IsLocallyTrivial`** | **NEW bespoke predicate** for the capstone (§3) |
| **`ringKrullDim` of `MvPolynomial`** | **present** | `MvPolynomial.ringKrullDim_of_isNoetherianRing` = `ringKrullDim R + #ι` (`KrullDimension/Polynomial.lean`); `Polynomial` version; `height_map_C` | reuse (the #14 dim stack already does) |
| **Determinantal-variety dimension** `r(n+m−r)` / rank-stratum height | **ABSENT** | — | in-repo `DeterminantalStratumDim` (rides cited Brick A) |
| **rank over residue field `κ(p)`** | base API present | `Ideal.ResidueField`, `algebraMap_residueField_eq_zero`, `Matrix.map` + `RingHom.map_det` | assembled in-repo `FibreRankBridge` (§3) |

---

## 3. THE build-vs-cite verdict — the residue-field-rank bridge (gates P2.d)

### Claim card — RES-BRIDGE

- **Statement.** The residue-field-rank bridge — at every prime `P` of the rank-`=r` determinantal coordinate ring, [rank-over-`κ(P)` `= r`] `⟺` [`P` lies in a pivot principal open `D(detMinor_{s,t})`] (so the explicit Schur charts cover **every scheme point**, not only `k`-rational matrices) — is **detail-at-scale (BUILD), not a monument**.
- **Tier.** New (our framing of the build-vs-cite line), backed by an in-repo proof for the DLN instance.
- **Evidence (decisive).** `FibreRankBridge.mem_rankROpen_iff_rank_universalMatrixResidue_eq` (sorry-free) **already proves exactly this** for the DLN stratum: `P ∈ rankROpen ↔ (universalMatrixResidue d r P).rank = r`. The proof is the predicted detail-at-scale:
  - **`≤` (every prime):** the `(r+1)`-minors of the generic product are baked to vanish in the ring (`det_submatrix_multPoly_mem_vanishingIdeal_sweepSigma`); push to `κ(P)`; apply the field-level `rank_le_iff_forall_submatrix_det_eq_zero`.
  - **`≥` (in a chart):** a pivot minor `chartDsigAt s t ∉ P` ⟹ its `κ(P)`-image `≠ 0` ⟹ that `r×r` minor invertible over the field `κ(P)` ⟹ `rank ≥ r` (`Matrix.rank_of_isUnit` + `rank_submatrix_le_rank`).
  - The cover `iSup_pivot_basicOpen_eq_rankROpen` is **definitional** (`rankROpen := (zeroLocus {pivot minors})ᶜ`).
  All inputs are field-level minor↔rank (`Core/Matrix/RankMinors`) + residue-field algebra (`Ideal.ResidueField`) — both already general. De-DLN-ifying to a general determinantal ring is mechanical (set up the universal matrix, the `(r+1)`-minor quotient, the pivot minors; the field-level lemmas transfer verbatim).
- **Kill-condition (stated before the hunt; survived).** The bridge stops being detail-at-scale iff the generalization needs something beyond *residue fields + field-level rank/minor API*: e.g. rank over **local rings** (not residue fields), **Fitting-ideal** theory for arbitrary modules, a scheme **image/elimination** argument to prove the `≤` bound, or a **sheaf-level / non-affine gluing** theorem. None of these appears — the setting stays "affine quotient by minors, evaluate the universal matrix in `κ(P)`, principal opens from pivot minors." **Survived.**

### The verdict on the capstone (P2.d) — the framing correction

The recon-gated question was framed as "build the **bare Mathlib `FiberBundle`** capstone iff the residue bridge is detail-at-scale." The bridge **is** detail-at-scale — but the literal target is wrong, and the decorrelated Codex consult (xhigh, `codex/verdict-answer.md`) sharpened it:

- **Mathlib's only `FiberBundle` is topological** (needs `[TopologicalSpace B]`, local *homeomorphic* product trivializations). There is **no** scheme/affine-algebraic `FiberBundle` or Zariski-`IsLocallyTrivial` in `AlgebraicGeometry` at this pin. (My draft "putting topology on `Spec` is a category error" was too strong — `Spec` *does* carry a topology; the error is conflating that topological bundle class with *algebraic* local-triviality.)
- **A bare `locallyTrivial` over `Spec(sweepSigmaRing) = Σ̄^r` (the closure) is genuinely FALSE** (already recorded in `FibreBundleLocallyTrivialFull`'s docstring): the rank-`<r` boundary lies in `V({chartDsigAt})`, in no chart. Local triviality holds only over the **rank-`=r` open**.
- **Therefore the honest capstone is a bespoke affine/Zariski local-triviality predicate**, not a Mathlib `FiberBundle` instance. Shape (Codex):
  `IsZariskiLocallyTrivialAffineProduct` = (principal-open cover of the rank-`r` open) + (per-chart named base map) + (`≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre`) + (overlap transition + cocycle). `FibreBundleHeadline.reducedFibre_rankROpenOverBaseLocalProduct` (`RankROpenOverBaseLocalProduct`) **already packages all of this except the cocycle field**.

**VERDICT: BUILD the capstone — as a bespoke `IsZariskiLocallyTrivialAffineProduct` predicate over the rank-`r` open, with the cover-every-scheme-point content supplied by the (de-DLN-ified) residue bridge.** Do **not** roadmap it as out-of-reach: the only genuinely missing piece is the **target-side cocycle field**, whose blocker (`AlgEquiv.trans_assoc` &c.) is itself **detail-at-scale**:

- **`AlgEquiv.trans_assoc` / `trans_refl` / `refl_trans` are provable generically by `ext x; rfl`** (Codex-vetted) — proved at the abstract `AlgEquiv` level they avoid extensionality on the heavy double-localized target, dissolving the kernel-timeout blocker. This is a tiny network-free Mathlib-gap spin-out (rung P2.b′ below). If the target round-trip still times out after that, the next suspect is the `@[reducible] targetChartLoc` (de-reducible-ize + hand-bundle instances), **not** the mathematics.

So: **capstone = BUILD** (bespoke predicate over the rank-`r` open); the **fallback honest-ceiling** (atlas + cocycle without the bundled predicate) only triggers if the `AlgEquiv`-API + reducibility route both fail — judged unlikely. Either way nothing here is a monument.

---

## 4. Refined rung ladder + de-DLN-ify target list

Bare Mathlib-mirror namespaces (L7), dependency-ordered. **Most rungs are re-home/generalize, not fresh build** — flagged `[re-home]` / `[generalize]` / `[build]` / `[crux]`.

### Phase 1 — `det-atlas-p1` (overlap API + determinantal rank-stratum)

| rung | item | home | kind | note |
|---|---|---|---|---|
| **P1.a** | Localization-overlap API: `awayOverlap`, `awayOverlapTransition` + 3 cocycle laws, `chartToSwappedOverlap` + restriction, `awayTriple` + **`awayTriple_cocycle`** | `Core/RingTheory/Localization/Overlap.lean` | **[re-home]** | move `FibreBundleTransition` §`Abstract`+§`TripleOverlap` verbatim (general `R`); retarget its 2 consumers (L6). **Lowest-risk rung — already proved.** |
| **P1.b** | Matrix coord ring + determinantal ideal: generic matrix (reuse Mathlib `mvPolynomialX`), `detMinorPoly`, the **ideal of `(r+1)`-minors** (NEW object — absent in Mathlib), `eval_detMinorPoly` | `Core/RingTheory/Determinantal/Basic.lean` | **[generalize]** | `detMinorPoly` re-home from `FibreBundleTransition` §`MinorChart`; the minors *ideal* is the one genuinely new def |
| **P1.c** | Rank strata + cover: `rankLeLocus`(closed), `rankEqLocus`(open), `minorChart`, **cover theorem** `rankEqLocus_subset_iUnion_minorChart`; `exists_invertible_minor_of_rank`; the minor↔rank criterion `rank_le_iff_forall_submatrix_det_eq_zero` | `Core/RingTheory/Determinantal/Strata.lean` (+ `Matrix/RankMinors` re-home to `Mathlib.LinearAlgebra.Matrix.Rank` mirror) | **[re-home]** | all present in `RankMinorCover` + `Matrix/RankMinors` (i); rename namespace |
| **P1.d** | Schur coordinates: block-rank additivity `rank_fromBlocks_zero` (absent in Mathlib), `rank_eq_iff_schur_eq`, the chart parametrization `pivotRankChartEquiv`, the `CommRing` normal form `schurComplement_normal_form` | `Core/RingTheory/Determinantal/Schur.lean` | **[re-home]** | from `DeterminantalChart`/`SchurChartIff`/`SchurGauge` (i)/(ii) |
| **P1.e** | Dimension/height of rank strata: `r(n+m−r)`, `(n−r)(m−r)` codim | `Core/RingTheory/Determinantal/Dimension.lean` | **[generalize]** | from `DeterminantalStratumDim`; rides cited Brick A (codim) — keep the citation named, do not fold into the dim theorem name (precision) |

### Phase 2 — `det-atlas-p2` (off `-p1`): constructive atlas + capstone

| rung | item | home | kind | note |
|---|---|---|---|---|
| **P2.a** | Pivot-chart datum + standard fibre model (drop `s/t/σ/τ` threading; bundle base ring + fibre coord ring + tensor + structure map + flatness + localization transport) | `Core/RingTheory/Determinantal/Atlas.lean` | **[generalize]** | from `FibreOverBaseTriv` + `FibreBundleHeadline` (`PivotDatum`, `RankROpenOverBaseLocalProduct`) |
| **P2.b′** | **`AlgEquiv` groupoid spin-out** — `trans_assoc`, `trans_refl`, `refl_trans` by `ext x; rfl` | `Core/Algebra/AlgEquiv/Groupoid.lean` (Mathlib `Algebra/Algebra/Equiv` mirror) | **[build, small]** | the cocycle-unblocker; network-free; Codex-vetted |
| **P2.b** | Transition maps on overlaps (explicit rational change-of-coords via P1.a) | atlas home | **[re-home]** | from `FibreBundleTransition`/`FibreTargetOverlap` |
| **P2.c** | **Cocycle-compatibility [CRUX]** — base-side cocycle DONE; the residual is the **target-side round-trip** `(I,J)∘(J,I)=id`, now reachable via P2.b′ (+ de-`reducible` `targetChartLoc` if needed) | atlas home | **[crux]** | decorrelated review; the math (`chartOverlapTransitionK_trans_symm`) is LANDED, only the transport-through-trivialization is to finish |
| **P2.d** | **Bespoke Zariski local-triviality capstone [CRUX, recon-gated → BUILD]** — `IsZariskiLocallyTrivialAffineProduct` over the rank-`r` open; cover-every-scheme-point via the **de-DLN-ified residue bridge** | atlas home | **[crux, build]** | NOT a Mathlib `FiberBundle` (topological); residue bridge already proved (`FibreRankBridge`) |

### Woven — de-DLN-ify target list

Re-express as **instances** of the Core determinantal API (keep all DLN consumers green, signatures + payoff axioms unchanged; FL-III pattern = abstract Core + thin DLN adapter):

| DLN object | becomes an instance of | scope / caution |
|---|---|---|
| `productRankLocusLE d r` (22 files) | `rankLeLocus` at the product-of-arrows matrix | wrap, don't replace; 22 consumers |
| `sigmaIdeal d r` (18) | the determinantal `(r+1)`-minor ideal pulled back along `multComap` | the `multComap`-pullback is the DLN-specific glue (iii) |
| `dStratum n m` (8) | the single-arrow specialization `![n,m]` | thin |
| `chartDsigAt` / `sweepSigmaRing` (9 / 24) | pivot principal open + chart-closure ring | the bundle layer; (iii) ring, (i) overlap structure |
| **`RepCoord d` (79 files) — DO NOT remove** | leave as the DLN coordinate type | pervasive; de-DLN-ifying it is out of scope and not the point |

---

## Reflection

- **Most likely to advance the expedition:** **P1.a re-home** (the overlap API is finished, DLN-free, with the triple-cocycle proved) — it converts the "fragile ad-hoc double-localization" concern into a banked general library at near-zero risk, and unblocks P2.b/c. Closely behind: the **RES-BRIDGE verdict**, which de-risks the whole P2 capstone (the gating crux is already proved for the instance).
- **Most likely to break:** **P2.c target-side cocycle** — even with the `AlgEquiv.trans_assoc` spin-out (P2.b′), the `@[reducible] targetChartLoc` kernel-cost may resurface; the fallback (de-reducible-ize + hand-bundle instances) is untested. The capstone *predicate* (P2.d) is safe; its *cocycle field* is the fragile bit.
- **Next computation that would clarify:** a scratch `example` (sorry-OK, uncommitted) proving `AlgEquiv.trans_assoc` by `ext x; rfl` and using it to discharge the `FibreTargetOverlap` round-trip `(I,J)∘(J,I)=id` structurally — if that compiles in budget, P2.c/P2.d are confirmed buildable and the capstone verdict is locked as **build** with no fallback.

### Scratch confirmation (done — uncommitted, `/tmp/scratch_algequiv.lean`)
The three `AlgEquiv` groupoid lemmas **compile clean by `ext x; rfl`** at this v4.29 pin (elaborated via `lake env lean` against the shared store):

    example (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) (e₃ : C ≃ₐ[R] D) :
        (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := by ext x; rfl
    example (e : A ≃ₐ[R] B) : e.trans (AlgEquiv.refl) = e := by ext x; rfl
    example (e : A ≃ₐ[R] B) : (AlgEquiv.refl).trans e = e := by ext x; rfl

So P2.b′ is confirmed trivially buildable, and the **capstone verdict locks as BUILD** — the only open question for P2.c is whether the structural cocycle proof avoids the `@[reducible] targetChartLoc` kernel cost (the `ext;rfl` lemmas operate at the abstract `AlgEquiv` level, off the heavy type, so this is expected to clear). Nothing on the P2 path is a monument.

---

## Artefacts
- Decorrelated Codex consult (xhigh): prompt `codex/verdict-prompt.md`, answer `codex/verdict-answer.md`.
