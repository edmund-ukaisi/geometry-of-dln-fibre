# Lean conventions (DLNFibre)

## Build
- **Multi-worktree / multi-session: build via `scripts/lb`, NOT bare `lake build`.** `lb` symlinks this
  worktree's `.lake/packages` to the shared rev-keyed mathlib store (mmap-shared, no per-worktree clone)
  and throttles total Lean workers across all sessions via a global semaphore. Full rationale + box
  sizing: [`../docs/policies/lean-build-workflow.md`](../docs/policies/lean-build-workflow.md). **Do NOT
  `lake exe cache get` in a worktree** — it re-clones ~7 GB and defeats the sharing; the shared store is
  built once by `scripts/lake-store-setup <mathlib-rev>` (detached; exceeds the 10-min cap).
- Fresh shells: `source ~/.elan/env` before any `lake` command.
- Build from this `lean/` directory: `scripts/lb DLNFibre.<Module>`, or `scripts/lb` for the whole
  library. (Bare `lake build`/`lake env lean` still work for one-off elaboration, but bypass the shared
  store + the global concurrency cap — fine for a single `#eval`, not for parallel builds.)
- Toolchain: Lean `v4.29.0` (`lean-toolchain`), Mathlib `v4.29.0` (`lakefile.toml`). Matches the `ai-research-assistant` harness one level up, so its v4.29 Mathlib idioms transfer.

## Library shape — engine vs application
- **`DLNFibre.Core.*`** is the network-free **engine** (quiver orbits, Kostant partitions / rank patterns, `Ext` codimension, `(C, θ)`). It **must never import `DLNFibre.DLN`**. The dependency arrows point `DLN → Core → Mathlib`.
- **`DLNFibre.DLN.*`** is the **application** (multiplication-map fibres, the square-Frobenius loss, the RLCT payoff); it depends on `Core`.
- State each result at the specificity its claim needs; lift a piece into shared `Core` API on its **second** use, not in anticipation of one. Good API (characterizations over predicates, weakest hypotheses, name = content) is the `bedrock`/`precision` discipline, not a folder layout.

## Aggregator
- `DLNFibre.lean` is single-writer. Add new module imports at the end; do not reorder existing imports.
- New modules live at `DLNFibre/<Core|DLN>/<Topic>/<File>.lean`; one substantive theorem family per file.

## Sorry gate
- Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- **Expedition mode (goal-relative zero-sorry).** On a long expedition the flat zero-gate is
  unimplementable (composition skeletons carry named holes by design) and a flat token count cannot
  distinguish an open obligation from dead scaffolding — the aoyagi-full run had to invent the
  distinction informally ("0-sorry in the AxCheck-load-bearing sense; 21 tracked scaffold sorries").
  The implementable form: (i) a declared **roots registry** (the goal headline(s) + registered
  composition skeletons); (ii) every sorry is either **LIVE-frontier** (on a registered root's
  dependency cone — statement-locked, tracked, owned, count small and sawtoothing) or a **fossil**
  (off every root's cone — quarantined, pruned at close, never on the value path); (iii) the audit is
  cone-aware (classify via the env-walker dependency graph; `scripts/sorries` stays as the raw census;
  `AxCheck` stays the kernel truth for roots). The roots registry and the cone-aware audit are part of
  the **expedition-map** (see `docs/policies/expedition-map.md` — curated `claims.yaml` + computed
  survey + kernel-checked `MapAnchors.lean` pins; roots = `meta.roots`, LIVE frontier = the
  goal-relative sorry cone; fossils belong to retired nodes and are pruned, not carried).

- **Skeleton discipline (P6).** A settled fork lands as a driver + obligation-record structure
  (fields = the obligations; churn-robust: statement detail moves under a stable fork-level shape),
  sorried, wired toward the headline. Each skeleton hole names its map node (`-- map: <node-id>`);
  a refuted/superseded node retires its hole in the same commit — a stale hole misdirects the
  brick-closing gradient (the false-bridge lesson).
  *The map is not the territory*: the kernel is the territory; the map's contracts keep it honest.
- Zero `sorry` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- **`axiom` is allowed ONLY for a declared cite** — an `@[cited "<source>"]` axiom in a located
  `…Cited.lean` file (see the citation cordon below). Any other axiom is a violation.
- A `sorry` with a correct statement is a building block; a `sorry` with a wrong statement misleads. Fix wrong statements first.
- **`lake build` / `scripts/lb` exit-0 can MASK a `sorryAx` via a stale olean cache.** If an edit does not
  invalidate a `.olean` (a downstream-only change, an edit Lean's incremental compiler deems irrelevant), a
  prior `sorry` / type-error can persist in the cached olean and the build still reports success. **Confirm
  any "sorry-free" / axiom-footprint claim with `#print axioms` (which FORCES elaboration), never the build's
  exit status alone** — or force-recompile (delete the `.olean` / `touch` the source). The aggregator's
  `AxCheck.lean` does this for the load-bearing results on every build; add new load-bearing results there, or
  run a force-rebuilt `#print axioms` scratch (delete its olean first). (Caught a persisted diagonal-`sorry` +
  an unreported type-error in `RouteMSchurFrameDet`, 2026-06-26.)
- **`scripts/lb <Module>` builds a module's import-closure only — it does NOT catch NAME CLASHES with sibling
  modules the full aggregator imports.** A module that re-defines a constant another module already owns (e.g.
  two `(2,2,2)` anchor files both defining `t222`/`M222` in the same namespace) builds green in isolation but
  fails `lake build DLNFibre` with `environment already contains '…'`. **Before reporting a module as
  integration-ready, green-gate the FULL `lake build DLNFibre`** (or at least `rg` your new top-level names
  against the siblings you'll sit beside). Reuse shared anchor constants by `import`ing the module that owns
  them, don't re-declare. (Caught `RouteM222Det` re-defining `RouteM222StructAdm`'s `t222`, 2026-06-27.)
  **The clash-grep must cover ALL new top-level names in EVERY touched file, not just the new module's** —
  a helper added to an EXISTING file (e.g. a `Foundations/` lemma) clashes with a sibling's `private` copy
  of the same fact just as readily, and `private` on the sibling does NOT protect you (the public import
  wins the name and the sibling's declaration errors). Resolution preference: keep ONE public canonical
  form in the most foundational file and delete private duplicates (uses resolve to the import) — not
  privatize the new one (timid, keeps the duplication). (Caught `Lambda.admBound_le_Msucc` vs
  `Skeleton`'s private copy, 2026-07-20; two independent fixes reconciled to public-canonical.)

## Citation cordon (the Proved-vs-Cited gate)
- Cited external results are `@[cited "<source>"]` `axiom`s in located `…Cited.lean` files; the kernel
  tracks every axiom via `collectAxioms`, and the accounting is `collectAxioms − {propext,
  Classical.choice, Quot.sound} − @[cited] = ∅`. Full mechanism + declare-a-cite workflow:
  [`../docs/policies/citation-cordon.md`](../docs/policies/citation-cordon.md).
- **Two-part gate, per-root (no whole-env walk):**
  - **`#assert_banked_clean X`** — the SOUNDNESS gate, a `Meta.Cordon` command run over the roots in
    `DLNFibre/DLN/RLCT/AxCheck.lean`. Rides Lean's `collectAxioms` per root: asserts `UNACCOUNTED = ∅`
    and (unless `X` is a `@[blueprint]` forecast) no forecast leak. Does NOT check cite location.
    A root that legitimately carries a live-frontier `sorryAx` keeps `#print axioms X` + a
    `-- TRACKED-OPEN` comment instead (informational, not gated).
  - **`scripts/cordon`** — the SOURCE gate (python grep, sibling to `scripts/sorries`; nonzero exit on
    violation): cite LOCATION/TAG over `DLNFibre/**` + a `native_decide` ban + a blueprint census.
  - **`#audit_cited foo` / `#audit_blueprint foo`** — the in-file reports (mirror `#print axioms`), the
    inner loop. **`scripts/cordon-test`** — battle-tests BOTH gate halves against `tests/*`.
- Forget-proof: forgetting the tag doesn't hide a cite (the raw axiom still lands in UNACCOUNTED → red
  `#assert_banked_clean`). Green = "no unaccounted axiom, all cites located, no forecast leak", NOT a
  whole-TCB audit; a human still reviews the source string. (The whole-env `cordon-audit` executable +
  `Meta.CordonAudit` were deleted 2026-07-20 — the per-root gate replaces the slow Mathlib-wide walk.)

## Bedrock (the bar above the sorry gate)
A green, sorry-free build is the **floor**: it defeats *technical* slop, never *conceptual* slop —
"technically correct but subtly wrong, not The Way." Build each result as **bedrock**: something the next
theorem stands on without re-opening it. Where there's nothing to check against, **beauty is the guide** — a
vacuous, mis-scoped, or overclaiming theorem is *ugly*. In practice that recurrently means (not exhaustively):
name = content; non-vacuous, with the witness *shown* in-file; the weakest hypotheses that suffice, in usable
form; characterized (an `iff`) over asserted; every *cited*/*assumed* step named (never an `…rlct…`-style
theorem that secretly claims an unproved analytic interface — here the `rlct = ½·codim` reading rests on a
cited bound). The controller judges against this taste and holds precedence — full statement:
[`../docs/policies/bedrock.md`](../docs/policies/bedrock.md).

## Style
- `↦` not `=>` for lambda arrows.
- `decide +kernel`, not `native_decide`. Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO`.
- One-line docstrings.
- Name a lemma for what it proves: a kernel/ideal *membership* fact is `…_mem_ker`, not `…_gen` (which reads as an ideal-generation claim).
- Confirm a Mathlib lemma exists before building a proof around it: `scripts/lean-search "..."`, or `rg` over `.lake/packages/mathlib/Mathlib/`.
- Pre-stage uncertain API with `example` blocks that pin lemma names/types; keep them as durable contracts.

## Mathlib gotchas (v4.29 pin)
Toolchain-generic notes that transfer at this pin. Accumulate new, DLN-specific ones here as they are found
(the ReLU programme's proof-specific notes were intentionally not ported — they were about a different theory).

- **Reducing a nested dependent `match h : e with` to a chosen branch — the split-chain FAILS in a
  reduced context; use explicit `split` + `Option.some.inj (heq ▸ hyp)`.** For a `horacle`-style equation
  `theDef … = <branch>` where `theDef` unfolds to `match hmin : x.min? with | some t => match hf : g t with …`
  and the match binders (`hmin`/`hf`) SHADOW same-named local hypotheses, the banked chain
  `split <;> simp_all only [reduceCtorEq, Option.some.injEq]; all_goals (try subst_vars); all_goals (try (split <;> simp_all …))`
  (proven for `MvalBoundaryInv_conOracle_stepChildren`) does NOT close when the local context has FEWER
  hypotheses than that template — the inner `split` gets swallowed by `try` and `simp only [hmin]` can't
  rewrite the scrutinee under the shadowing binder. WORKING idiom (`NumDivInv_conOracle_stepChildren`,
  2026-07-19): drop the chain and do explicit nested `split`, naming the pattern var + the split equation
  with `rename_i target' heq`, then reconcile the shadowed scrutinee to the local hyp with
  `obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)`; recurse for the inner match; close the
  `none` branches with `exact absurd (heq ▸ hmin) (by simp)`.
- **Verify ABSENCE before declaring a lemma a phantom (and rebuilding it).** When a needed lemma seems
  missing, a `grep` for the exact name is NOT enough — check variant names (`integral_` vs `integrable_`,
  `_le_` vs `_lt_`, `norm` vs `nnorm`, argument order) AND check our own `Foundations/` before concluding
  Mathlib/we lack it. Real example (2026-07-16): a scout grep'd `integral_fun_norm_addHaar` (absent) and
  declared the polar/radial route a phantom — but `integrable_fun_norm_addHaar` (integral→**integrable**) is
  present in Mathlib (`MeasureTheory.Constructions.HaarToSphere`) AND already consumed in our foundation via
  `radial_ball_iff` (Foundations/S1SmoothBlock.lean:78) + `euclidND_ball_integrable` (S1RadialMorse.lean:46).
  Declaring a banked lemma absent risks a wasted rebuild. Verify-before-building cuts both ways: the same
  discipline that catches a genuine phantom (`Real.log_le_rpow`, truly absent at this pin → use `Real.log_rpow`
  + `Real.log_le_sub_one_of_pos`) must not mistake a REAL lemma for a phantom via a name typo.
- **Composed matrix expressions with an inverse hit a DecidableEq/Inv instance diamond that blocks `rw`/`linarith` matching.** E.g. the transverse projector `1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b` (`Ring.inverse`/`⁻¹` carries a `DecidableEq`/`Invertible` instance that doesn't defeq-match the one in your facts). `set … with h` + `clear_value` does NOT fix it. **Working pattern: `generalize` the composite to a fresh atomic variable across the goal AND all hypotheses at once** — then the matching fires on the atom. Found building the R1 Frobenius-split (RouteMSJInteriorR1) 2026-07-17; recurs in any proof manipulating a projector/Schur-complement built from `(·)⁻¹`.
- **`Basis` is `Module.Basis` at the v4.29 pin.** Bare `Basis` is unknown even with full Mathlib imports;
  ascribe `Module.Basis (Fin _) ℝ _` (e.g. from `Pi.basisFun`). Dot-notation (`b.tensorProduct b'`) is
  unaffected. Likely to recur in any `Matrix.rank` / column-span work.
- **`decide +kernel`, never `native_decide`.** Kernel `decide` is axiom-clean; `native_decide` trusts the
  compiler and breaks `#print axioms` hygiene. Kernel-reduction cost is **heartbeat-invisible** (a
  `maxHeartbeats` bump does not speed it), so a heartbeat timeout on a `decide` is not the symptom to chase.
- **Matrix-product identities over `ℤ` by `decide`, then cast.** An `ℝ` matrix-product identity is a
  `Matrix.ext` blow-up (per-entry `simp`, times out at scale). Write the matrices over `ℤ`
  (`DecidableEq` ⟹ `Matrix.mul` decides by kernel reduction, `by decide`), define the `ℝ` ones via
  `· .map (Int.castRingHom ℝ)`, and transfer products with `← Matrix.map_mul` (cast is a ring hom). No `ℝ`
  `Matrix.ext` at all.
- **`Fin`-vector `![…]` + `fin_cases` friction.** `fin_cases i` leaves the index as `⟨k, ⋯⟩` (a `Fin.mk`),
  so `Matrix.cons_val_one`/`_two`/… do not fire on the outer selection. Normalize first with
  `rw [show (⟨k, by omega⟩ : Fin n) = (k : Fin n) from rfl]`, then the `cons_val_*` simp set fires; or prove
  the components as separate `have`s and assemble with `funext i; fin_cases i`.
- **Matrix-apply `simp` fires in ISOLATION but "no progress" IN-CONTEXT when the index is typed at a
  DEPENDENT, non-syntactic-`succ` width** (e.g. `i : Fin (Wext M k)` / `Fin (Text M t k)`, defeq but not
  syntactic `Fin 2`/`Fin 1`). After `ext`/`fin_cases` the indices are `Fin.mk`s at the opaque width, so
  `Matrix.smul_apply`/`mul_apply`/`cons_val_*` don't fire, AND `Fin.zero_eta`/`Fin.mk_one` can't normalize
  (the width isn't a syntactic `n+1`), so `change`/`show` to a literal `Fin n` is unavailable. **Working
  pattern: prove each entry as a `have` at EXPLICIT `⟨_, by decide⟩` (or `by omega`) indices where the
  matrix-apply lemmas DO fire, then `exact` it into the `fin_cases` goal — `Fin` proof-irrelevance unifies
  the two index forms.** This is the recurring opaque-width cast quirk; it cost two tides on the (2,2,2)
  `chartParamsGen_eq_chartParams222` det bridge before the `have`+`exact` form landed it (2026-06-27,
  Codex-corroborated). Transfers to any entrywise identity over `chainA`/`GenBlk` dependent widths (the
  ∀M `φ_det_eq` lift).
- **`FactoredChain`/`Chain` projection mismatch (`c.Wwid` vs `c.toChain.Wwid`) breaks `HMul` instance
  synthesis** in products mixing the two structures' width fields — the dependent matrix-mul instance can't
  unify the two defeq-but-syntactically-distinct width projections. Resolve by **literal `Wext`/`Text`
  `let`-ascription** at the product (pin the widths to the concrete `Wext M k` / `Text M t k` form, cf.
  `Hmat_pivot`), or a generic `mul_three_reassoc'` whose abstract index types unify up to defeq. Side note:
  `omega` over `Text`/`Wext` arithmetic needs `k+1+1` normalized to `k+2` first. (Found in the ∀M interior
  witness build, 2026-06-27; recurs in any achiever-chart product mixing chain layers.)
- **`φ` (U+03C6) as a binder name can hit a lexer reject** (`unexpected token 'φ'; expected identifier`)
  when an editing tool inserts a confusable/variant codepoint. If a `∃ φ …` / `obtain ⟨φ, …⟩` line fails
  to parse despite looking right, rename the binder to ASCII (`phi`) or `ψ`; capital `Φ` (U+03A6) has not
  shown the problem. Cost two build cycles on `NoetherMonicPositioning.lean`.
- **A combining-tilde `Q̃` (base char + U+0303) is NOT a valid identifier** (`unexpected token`) — the
  same binder-codepoint hazard as `φ` above. Use an ASCII binder (`Qt`) for tilde'd matrices/variables.
  (`genm-sjcarrier6`, the Schur-shear coordinate.)
- **To put a banked `[Invertible]`-stated identity inside a `∫⁻`/pointwise-a.e. goal, convert the `⅟`
  (invOf) form to the `⁻¹` (`nonsing_inv`) form** via `invOf_eq_nonsing_inv` (after `IsUnit.invertible`
  to get the instance). A lemma stated with `⅟M` carries a typeclass `[Invertible M]` that a per-point
  integrand can't supply; the `M⁻¹` form is a plain function, integrand-usable. (`frobSq_schur_split_inv`,
  `genm-sjcarrier6`.)
  shown the problem. Cost two build cycles on the monic-positioning module (now
  `Core/Dimension/Catenary.lean`).
- **No off-the-shelf rank-normal-form / "equal rank ⟹ equivalent matrices" in v4.29.** Built at the
  linear-map level in `Core.FibreNormalForm` (`exists_conj`, `exists_baseChange_of_rank_eq`): for a
  rank-`r` `f : (Fin n → k) →ₗ (Fin m → k)`, restrict to `fU : U ≃ range f` (`U` a `ker`-complement,
  via `Submodule.quotientEquivOfIsCompl _.symm ≪≫ LinearMap.quotKerEquivRange`); two maps with equal
  ker+range finrank are conjugate (`prodEquivOfIsCompl` kernel/range decompositions glued by
  `LinearEquiv.ofFinrankEq`), transferred to matrices by `LinearMap.toMatrix'_comp` +
  `LinearMap.toMatrix'_toLin'`. Useful `rfl`s: `Matrix.rank A = finrank (range (toLin' A))` and
  `toLin' A = A.mulVecLin`. The `IsCompl` finrank lemma is `Submodule.finrank_add_eq_of_isCompl`.
- **`RingEquiv.height_comap` is the clean `Ideal.height` transport** (`(I.comap e).height = I.height`,
  any ideal, no `IsPrime`). For codim-invariance of a locus under a *linear* coordinate change, the
  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
  cleaner than re-deriving an `Ideal.map` identity. Used in `Core.FibreNormalForm.codimRep_baseChange_image`
  — this closes the linear-coordinate-invariance gap `Core.OrbitCodim`'s docstring flagged, for the
  base-change family of isos.
- **The end-factor (`GL_{d_N}×GL_{d_0}`) action is just `Core.BaseChange.baseChange` with inner units
  `= 1`.** No new action needed: mult-equivariance `mult (P•A) = P_N·(mult A)·(P_0)⁻¹` is
  `mult_eq_submult` + the LANDED `submult_smul` at the full interval `(0, last)`. Caveat: the
  same-rank ⟹ same-fibre-codim headline genuinely needs `N ≥ 1` (`hN : (0 : Fin (N+1)) ≠ Fin.last N`)
  — for `N = 0` `mult` is the constant `1`, the end vertices coincide, the action only conjugates, and
  the claim is false.
- **Matrix-space measure change-of-variables hits an instance DIAMOND: `Matrix.module` vs
  `NormedSpace.toModule`.** The Haar CoV lemma `map_linearMap_addHaar_eq_smul_addHaar` needs the
  `NormedSpace`-derived module instance, but a `LinearMap` built over `Matrix.module` (e.g.
  `RouteMSchurFrameDet.mulLeftMat`) sits on the *other* diamond branch, so the CoV lemma won't unify.
  **Workaround (recurs for any matrix-space measure CoV): transcribe the map over the RAW pi type**
  (`Fin c → Fin t → ℝ`), column-indexed. Left-multiplication `Y ↦ K.mulVec (Y ·)` is per-column
  block-diagonal, so `LinearMap.det` factors via `det_pi` to `(det K)^c` directly, and the Haar CoV
  fires on the pi instance with no diamond. (Pattern: `RouteMSJDecoratedPeelMeas.mulLeftₚ` /
  `lintegral_comp_mulLeftₚ`, transcribing `RouteMSJGammaAtom.rightMulₚ`; `genm-decbuild`, 2026-07-10.)
- **A `def` inlining a heavy spectral term (`(posSemidef_mul_transpose P).isHermitian.eigenvalues` /
  `.eigenvectorUnitary`) makes any lemma manipulating it hit a `(deterministic) timeout at isDefEq/whnf`
  (even @800k heartbeats)** — unification re-elaborates the spectral term each time. TWO-PART fix
  (confirmed, `RouteMSJFrontFirst`, `genm-sj5`, 2026-07-11): (1) for an EQUALITY matching the def against a
  banked lemma, use `rw [theDef]` (the auto equation lemma is a *syntactic* rewrite) NOT `unfold theDef`
  (which triggers the expensive isDefEq); (2) for a PROOF that manipulates the term, state the def over an
  ABSTRACT binding — a plain `(lam : Fin r → ℝ) (U : Matrix …) (c : Fin r)` triple (`…Aux`), prove the
  content there (no spectral term in sight), then `theDef := theDefAux (…eigenvalues) (…eigenvectorUnitary)
  …` and instantiate. The heavy terms become bound arguments, never re-elaborated. Any front-first
  spectral assembly (both DLN lanes' `twoBlock` consumption) needs the abstract-`Aux` form — do it once.
  Two finer points (confirmed, `RouteMSJFrontFirst` reshape, 2026-07-11): (1') the timeout hits even with
  the abstract binding when a proof step is a multi-step `calc` whose endpoint-matching is defeq-heavy (e.g.
  over `Set.indicator` of a big integrand) — a direct `rw` chain fixes it instantly; **prefer `rw` over
  `calc` when steps are defeq-heavy**, not just `rw` over `unfold`. (2') `set U := …eigenvectorUnitary`
  does NOT help — `set` inlines the heavy term into every downstream defeq; the `…Aux`-over-abstract-`U`
  factoring is NECESSARY (a thin instantiation lemma at the end), not merely tidy.
- **Heavy spectral terms (`IsHermitian.eigenvalues`/`eigenvectorBasis`) choke the CLOSING `rfl`/defeq even
  on a syntactically-`X = X` goal** (the same whnf-diamond as above, at the last step). Fix (confirmed,
  `RouteMSJKyFan`, `genm-sj5` D-C): keep the spectral term INSIDE the inner product and pull it out as a
  scalar with `real_inner_smul_right` — never let `λᵢ • bᵢ` appear as a bare vector `smul` that a later
  step must defeq-close. (Rayleigh-expansion / eigenbasis proofs are the usual trigger.)
- **`Module.finrank ℝ (EuclideanSpace ℝ (Fin k))` as an explicit `have`-type ANNOTATION fails instance
  synthesis** with a garbled `failed to synthesize Max Type` inside a nontrivial proof context (yet works
  in a bare `example`). Fix (`RouteMSJKyFan`): do NOT annotate the finrank; take `Submodule.finrank_le _`
  (RHS type inferred) and `rw [(WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).finrank_eq, Module.finrank_fin_fun]`
  at the inequality; supply `Module.Finite ℝ (EuclideanSpace ℝ (Fin k))` explicitly via
  `Module.Finite.equiv (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm`. Recurs in any `EuclideanSpace` finrank /
  subspace-dimension counting (the D-C dimension-counting family).
- **A `def : Fin (someDef …) → X` built by `unfold someDef; split_ifs` (dependent DIMENSION) wraps its
  body in an `Eq.mpr`/cast on the FUNCTION TYPE — so `Function.Injective`/property proofs about it hit the
  dependent-cast wall** (`convert` leaves a `HEq (Eq.mpr … f) g`; `simp [id_eq]`/`eqRec_heq` don't close
  it cleanly). FIX (confirmed, `QNodeCarrier.realCNode`, `t09`): redefine POINTWISE — `fun i => if h₁ …
  then absurd i.isLt (by have := dim_zero_lemma; omega) else … else body (finCongr (dim_eq …) i)`. Every
  branch outputs the codomain `X` (dim-0 branches discharge via `i.isLt` + `omega` from a `someDef = 0`
  reduction lemma; the non-trivial branch casts the INPUT index by `finCongr dim_eq`, not the whole
  function). Then injectivity is `(finCongr _).injective (bodyInjective …)` — no `Eq.mpr` in sight. The
  general move: push the dependent cast from the function type onto the `Fin` index via `finCongr`.
- **RLCT / measure-theory analysis gotchas (from `Core.Analysis.RLCT.SumSq`, sum-of-squares RLCT).**
  - **No ball-version polar reduction in v4.29.** Only the *global* `MeasureTheory.integrable_fun_norm_addHaar`
    (`Integrable (f ∘ ‖·‖) μ ↔ IntegrableOn (fun y ↦ y^(dim E - 1) • f y) (Ioi 0)`) exists. For a
    *local-at-0 / ball* threshold, cut off with a radial indicator `f := (Ioo 0 R).indicator (·^s)`;
    for `s < 0` this makes `f ∘ ‖·‖` **pointwise equal** (not just a.e.) to `(ball 0 R).indicator (‖·‖^s)`
    (the `x=0` point agrees via `Real.zero_rpow (s ≠ 0)`), sidestepping the sphere/`{0}` null-set bookkeeping.
    Then `integrable_indicator_iff` / `integrableOn_indicator_iff` (`indicator s f` on `t` ↔ `f` on `s ∩ t`)
    reduce to `intervalIntegral.integrableOn_Ioo_rpow_iff (ht : 0 < t)` (`x^s` on `Ioo 0 t` ↔ `-1 < s`).
    (Codex hallucinated a `radial_ball_iff` repo lemma and a ball-version `integrableOn_fun_norm_addHaar`
    — neither exists; verify before trusting.)
  - **`intervalIntegral.integrableOn_Ioo_rpow_iff`** lives in the `intervalIntegral` namespace (bare name unknown).
  - **`Set.indicator_of_notMem`** (v4.29 renamed `not_mem` → `notMem`); `Set.indicator_of_mem` unchanged.
  - **`EuclideanSpace.measurableEquiv` is deprecated → `MeasurableEquiv.toLp 2 (ι → ℝ)`** (Pi → Euclidean;
    `.symm` for Euclidean → Pi, coercion `= WithLp.ofLp`, `rfl`). Volume transport:
    `PiLp.volume_preserving_ofLp ι : MeasurePreserving ofLp volume volume` (`.map_eq` for `volume.map ofLp = volume`).
    Filter transport (`𝓝 0 ↦ 𝓝 0`): `(WithLp.linearEquiv 2 ℝ (ι→ℝ)).toContinuousLinearEquiv.toHomeomorph.map_nhds_eq 0`.
    `IntegrableAtFilter` transports through `ofLp` via `MeasurableEmbedding.integrableAtFilter_map_iff`.
    This carries a `rlctAt`/local-integrability question between the Pi type `Fin n → ℝ` (where `sumSq`/`rlctAt`
    live) and `EuclideanSpace ℝ (Fin n)` (where `‖·‖` = ℓ², so the polar lemma applies); volumes agree,
    only the norm instance differs.
  - **`Real.rpow` at `0`:** `0^neg = 0` (`Real.zero_rpow (h : s ≠ 0)`), so a negative-power germ is `0`
    *at* the zero, and any divergence must come from the punctured neighbourhood, never the value at `0`.

## θ-count discharge findings (`Core.CCodimCornerMono`, thread 06)
- **The θ-count headline reduces to ONE combinatorial inequality**: the dimension-monotonicity of
  `cCodim · 0` (`cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'`, + a strict all-vertex version). Both gating
  bricks (`hLowerBound`, `hRecover`) discharge from it via the LANDED rank-shift `cCodim d t = cCodim
  (d−t) 0` + the Gabriel→Kostant bridge `gabrielPartition` (a tuple's `kostantArrayOfRank (rankFn ·)`
  recast into the `CTheta` `Fin × Fin → ℕ` encoding via `finArrayOfSupp`).
- **The right construction for the dimension-monotonicity is the SHORTEST-interval split** (at an
  over-covered vertex `k`, split the shortest `[i,j] ∋ k` into `[i,k−1]+[k+1,j]`): verified to never
  increase `codimForm` (199/199), whereas splitting a non-shortest interval CAN increase it. The
  merge-up route (raise the corner per-partition) is DEAD — corner-`s` partitions often admit no
  corner-raise with non-increasing `codimForm` (71/252).
- **Strict SINGLE-vertex dimension-mono is FALSE** (e.g. `cCodim [1,1,0] 0 = cCodim [1,2,0] 0 = 0`);
  only the strict ALL-vertex version holds (`d−r < d−s` everywhere when `r > s`). Strict corner-
  monotonicity (needed for `hRecover`'s "corner = r") rides on the all-vertex strict version.
- **`codimForm` is the type-A `Ext`-pairing form**: reindexed, `= ∑_{A=[a,b],B=[c,e]: a<c≤b+1, b<e}
  m̄(A) m̄(B)`. The split delta is `∑_B coeff(B) m̄(B)` with the positive-coeff `B` being the shorter
  intervals covering `k` (absent when `I` is shortest). `codimForm` is also corner-blind
  (`codimForm_update_corner`, LANDED) — it never reads `m_{0N}`.

## `cCodim·0` weak monotonicity LANDED (`Core.CCodimZeroMono`, thread 07)
- **`cCodim_zero_mono` is PROVED sorry-free** (`e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`), discharging the
  weak gating hypothesis `hMono`. The θ-count headline is now `numTop_eq_ncard_topComponents_of_strict`
  — UNCONDITIONAL except for the strict `hMonoStrict`. Axiom-clean `[propext, Classical.choice,
  Quot.sound]`. `hLowerBound` is fully unconditional.
- **Reusable infrastructure** (all in `CCodimZeroMono`, built on `CThetaQIPConverse`'s `codimBil`):
  `codimBil_extendℤ_boxℤ_right`/`_left` (univ-sum collapse of `codimBil` vs a single box, via the
  clamped `rrInd`/`llInd` indicators), `codimBil_boxℤ_boxℤ` (the box-pairing value), `codimForm_add`
  (reused), `codimForm_congr_onbox` (codimForm reads only on-box values).
- **Four atomic shortest-split moves**, each with delta / sign / `_le` / `_cover` / `_mem`: interior
  `redMove` (`c = b+2` gap kills the self-term), `leftShrink` (omit left endpoint; handles `a=0` and
  singleton-via-empty-piece), `rightShrink` (omit right endpoint; handles `d'=N`), `removeMove`
  (singleton removal; coefficient ALWAYS `≤ 0`). Boundary lesson: there is NO `Fin` `b` with `b+1 = 0`,
  so `k=0` left-endpoint and `k=N` right-endpoint genuinely need the dedicated shrink moves (the
  interior `redMove`'s empty-piece guard `a≤b` can't be made false when `a=0`). `reduceStep` dispatches
  by `k`'s position; `exists_le_codimForm` is the recursion (strong induction on `∑ e'`).
## `cCodim·0` strict monotonicity LANDED → θ UNCONDITIONAL (`Core.CCodimZeroStrict`, thread 08)
- **`cCodim_zero_strict` is PROVED sorry-free** (`(∀ v, e v < e' v) → cCodim e 0 < cCodim e' 0`),
  discharging `hMonoStrict`. **`numTop_eq_ncard_topComponents` is now UNCONDITIONAL** (`θ =
  #top-dimensional irreducible components of Σ̄^r`, no open hypothesis); axiom-clean `[propext,
  Classical.choice, Quot.sound]`.
- **Route B (the landed route), reusing the four atomic moves + their `_le` sign lemmas:**
  - **Double sum** `codimForm_extendℤ_eq_sum_pairs`: `codimForm (extendℤ m) = ∑_{A,B} m(A) m(B) ·
    [pairBox A B]` (built from `codimBil_sum_right` + `codimBil_const_mul_right` + the existing
    right-rectangle collapse; `rrInd (B.1)(B.2) A ↔ pairBox A B` on the box). Gives `∃ active pair ⟺
    codimForm ≥ 1` (`codimForm_extendℤ_pos_of_exists_pair` / `exists_pair_of_codimForm_pos`).
  - **Lemma Y** `codimForm_extendℤ_pos_of_fullCover`: full coverage ⟹ `codimForm ≥ 1`, via the
    extremal longest-`[0,b]` argument (`b<N` from corner-`0`; maximality forces `c≥1` so `[0,b]→[c,d]`
    pairs).
  - **Lemma X** `reduceStep_strict`: select the active pair minimising `min(ilen A, ilen B)`; split the
    shorter member at the partner-adjacent vertex. **ClaimA** (`claimA_left`/`claimA_right`) — that
    member is shortest *active* covering that vertex — is the one non-mechanical step (the `y<d` vs
    `d≤y` / `a<x` vs `x≤a` interval-arithmetic case split; minimality MUST be over the shorter member,
    Codex-confirmed). The partner sits at split-coefficient EXACTLY `−1` (`splitCoeff_partner_le` &c.,
    `omega` on indicators), and `sum_coeff_le_neg_one` upgrades the `_le` ("≤0") to `_lt` ("≤ −1").
    8-way dispatch (left/right member × interior/leftShrink/rightShrink/removeMove); each move has TWO
    partner orientations (the partner can sit left or right of the split source).
  - **Wiring** (`cCodim_zero_strict`): a minimiser `m'` of `cCodim e' 0` is full-coverage (Lemma Y ⟹
    `codimForm ≥ 1`); `reduceStep_strict` drops it `≥ 1` to a partition of `e'` decremented at `k`,
    which still dominates `e` (`e ≤ e''` since `e < e'` everywhere), so LANDED `exists_le_codimForm`
    gives `cCodim e 0 ≤ cCodim e' 0 − 1`. (No `+1`-step vector needed — the minimiser-of-`e'` route is
    cleaner and uses only the two given nonemptiness hypotheses.)
  - RULED OUT (don't re-explore): Route A (simple `Φ` with `codimForm ≥ Φ ≥ cCodim+1`) — the gap is
    often exactly 1, no simple `Φ` carries it; every deterministic LOCAL step-selection rule fails —
    the strict step's location is config-dependent (the "involved-in-a-pair + extremal-by-length"
    refinement is load-bearing).
- **Dependent-dimension matrix reassociation / cast handling — the kernel that cracked the `prodAux`
  front-peel (deferred twice).** For products over `Fin (M k)`-style dependent dimensions:
  (i) `rw [Matrix.mul_assoc]` / `simp` / `conv` will NOT match `(a*b)*c = a*(b*c)` through the dependent
  `HMul` instance (higher-order matching fails). Close it with a **fully-applied term** instead:
  `set X := …; set Y := …; exact Matrix.mul_assoc a X Y` (or state a generic
  `mul_three_reassoc {p q r s : Type*} [Fintype …] (a b c) : a*b*c = a*(b*c) := Matrix.mul_assoc a b c`
  once and reuse — cf. `RouteMFrontPeel.mul_three_reassoc`, generalising `DeepestTelescoping.mul_four_reassoc`).
  (ii) Do cast bookkeeping at the **equiv level, never entrywise** (`ext` into a cast-wrapped `∑ if…` is the
  trap that stalled two tides): `finCongr_refl` collapses `finCongr (rfl-true width eq)` to `Equiv.refl`,
  then `Matrix.reindex_refl_refl` (via `erw` — plain `rw`/`simp` won't match the dependent `Matrix.reindex`)
  collapses `reindex refl refl` to identity; `RouteMAchieverBridge.reindex_finCongr_mul` distributes a
  width-reindex over a product. (iii) Peel layer-products by **prefix-length induction reusing
  `prodAux_succ`**, not entrywise. This kernel transfers to any `prod`/`prodAux` reassociation (e.g. the
  L2/D1 `endpoint_telescoping`).

## L2 D1 two-peel `hrank₂` — the core-geometry gate is TRUE+TIGHT, its OPEN part is reachability (thread `genm-d1gates`)
The gate `hrank₂ : extraCountRect (H0−r) (H2−r) a b ≤ rank(jacResid (q(0,·)) t0)` of
`d1ge_L2_rect_two_peel` (`D1RectHDomProducer.lean`) is the sole CORE-geometry content of LEAF 2.
Front-loaded verdict (numeric certificate `expeditions/2026-06-20-aoyagi-full/threads/genm-d1gates/`
+ decorrelated Codex xhigh):
- **The MATH does NOT wall.** `jacResid (q(0,·)) t0 = [Dg(v)=jointDiffL2 with the nReg selected er-rows
  zeroed] ∘ (DΦ(0))⁻¹ ∘ [complement injection]`, and its rank `= extraCountRect` EXACTLY — uniformly
  over all middle-strata (layer ranks `(rank v0, rank v1) = (r+b, r+a)`; `a`=row/output rise, `b`=col/input
  rise, matching the cross-pairing), INCLUDING adversarial minor choices, ZERO fails. **NO constant-rank /
  stratification DROP** (the #120/hRform failure mode does NOT recur here). The abstract identity
  `rank([T er-rows-zeroed] ∘ (DΦ0)⁻¹ ∘ [compl inj]) = rank T − nReg` for ANY `T`/invertible-`nReg`-minor
  is clean and provable (0/400 abstract fails).
- **The OPEN part is FORMALISATION-reachability (verdict B, genuine new-module wall — NOT bounded
  plumbing).** `dln_hchart_residual_c2` DISCARDS the chart derivative (outputs only the RLCT-transfer
  EQUATION, which is measure-theoretic and CANNOT recover the Jacobian). Discharging `hrank₂` needs THREE
  new pieces: (b1) a producer variant exposing `HasFDerivAt (q(0,·)) L t0` (re-thread the germ
  `q =ᶠ rawResidVec∘Ψsymm∘splitHomeo.symm` + the internal `hsymm_hfderiv : dΨsymm 0 = f'.symm`); (b2) a
  network-free `rank(L) = rank T − nReg` linear-algebra module (spirit of `nReg_le_finrank_range_jointDiffL2`,
  at the residual/complement level; `rank_mul_le_left/right`, `rank_of_isUnit`, `rank_submatrix` exist at
  the pin); (b3) the `(a,b)` extraction. `hInterface` + value-close finish once these land. Do NOT launder
  `hrank₂` into a sorry or reduce it to another hypothesis (four hands have held this).
- **A dependent `match h : e with` INSIDE a def resists reduction under a projection**
  (`split at`/`simp [theDef, h]`/`rw [theDef]; rcases` all fail to reach it — e.g.
  `(conOracle M s).stepChildren` over `match hmin : occ.min?`). Working idiom (Codex-corroborated,
  `OracleInv_conOracle_stepChildren`, 2026-07-18): prove per-branch REDUCTION EQUATIONS
  `theDef args = <branch-value>` (by `unfold; rw [dif_neg …]; split` — the match sits at the
  equation LHS's head, where `split` CAN reach it; mind proof-irrelevance on dependent args),
  then `rw` the equation into the hypothesis. Two empirical amendments: (1) the def must INLINE
  the match (no `let`/`have` wrapping it, else `split` can't reach); (2) discharge branches with
  `simp_all only [reduceCtorEq, Option.some.injEq]` + `subst_vars` in rounds — full `simp_all`
  mangles filterMap guard conditions and breaks metavariable reconciliation.
