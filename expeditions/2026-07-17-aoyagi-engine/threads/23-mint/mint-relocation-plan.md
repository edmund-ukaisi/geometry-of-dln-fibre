# Mint relocation plan (thread 23-mint, task #8, navigator-6 audit item [A])

**Author:** mint-t19 (formaliser). **Branch:** `expedition/aoyagi-engine--t19-mint`.
**Status of deliverable 1 (the arm rewrite):** landed on this branch — see § "Pre-staged now".
**Status of this plan:** execute-ready recipes for the DISCHARGE MOMENT (when the engine's single
hole at `GeoAlphaGauge:562` closes and `Engine.engine_box_threshold_finite` flips clean-three).

Line numbers are current as of this branch (`origin/expedition/aoyagi-engine` @ `b06bec0b4`);
**re-confirm each by name with the grep recipes below before editing — line numbers drift.**

---

## Why relocation (not in-place repoint)

`Skeleton.lean` imports only `BGEngine` — it sits BELOW the engine in the import DAG. So "re-prove
the canonical `aoyagi_learning_coefficient` in place (Skeleton) via the prestage / engine route" is an
import cycle (Skeleton would have to import `EngineDriver`, which transitively imports far above
Skeleton). The canonical name must therefore RELOCATE up to `HeadlineL1Mint` (which already sits above
the engine — it now imports `EngineDriver`). This plan is that relocation.

---

## Pre-staged NOW (deliverable 1, banked green on this branch)

File: `lean/DLNFibre/DLN/RLCT/Validate/HeadlineL1Mint.lean`.

- Added import `DLNFibre.DLN.RLCT.Engine.EngineDriver` (verified acyclic: `EngineDriver` imports
  `EngineObligations` + `HeadlineGenAssembly`; neither transitively imports `HeadlineL1Mint` — the
  ONLY importer of `HeadlineL1Mint` is `AxCheck.lean`).
- DROPPED the now-dead import `DLNFibre.DLN.RLCT.Validate.RouteMSJMint` (after the arm rewrite nothing
  in `HeadlineL1Mint` resolves to it — the L≥2 arm's `_gen` + `engine_box_threshold_finite` both come
  via `EngineDriver`, and the L=1 arm's deps come via `DeepestBaseL1`). Build-verified green without it.
  This SEVERS `HeadlineL1Mint`'s transitive dependence on the `DecoratedDescent` machinery entirely
  (the fork-6 tombstone spirit). Remaining imports: `DeepestBaseL1` + `EngineDriver`.
- `aoyagi_learning_coefficient_prestage`: DROPPED the `(hDescent : DecoratedDescent)` binder; the
  `L ≥ 2` arm is now the DIRECT engine composition (navigator-6's verified recipe, matching the
  `EngineDriver` fit-witness at `EngineDriver.lean:61-67`):

      exact aoyagi_learning_coefficient_gen H r B hB hr hL hge hpos
        (Engine.engine_box_threshold_finite (fun s => H s - r) hL
          (fun s => Nat.sub_pos_of_lt (hpos s)))

  where `hge : 2 ≤ L` (from the `rcases lt_or_ge L 2`) plays `_gen`'s `hL2`, and `hL : 1 ≤ L` (the
  binder) supplies both `_gen`'s `hL` and `engine_box_threshold_finite`'s `0 < L` (defeq).
- **`DecoratedDescent` is NEVER resurrected.** If the direct composition had hit a real wall the
  instruction was STOP-AND-SURFACE, not fall back to `hDescent` — it did not wall.

**Axiom footprint (sorry-tolerant, as designed).** `#print axioms aoyagi_learning_coefficient_prestage`
is EXPECTED `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` routes THROUGH
`Engine.engine_box_threshold_finite` (the engine's one open hole), NOT through any `DecoratedDescent`
or Skeleton rung. It flips clean-three AUTOMATICALLY the instant the engine hole lands — no further
edit to `HeadlineL1Mint` is needed at discharge for the prestage itself.

**Signature note.** The post-rewrite `aoyagi_learning_coefficient_prestage` signature is now
IDENTICAL to the canonical `aoyagi_learning_coefficient` (Skeleton): both are
`{L} (H : Fin (L+1) → ℕ) (r) (B) (hB : B.rank = r) (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L)
(hpos : ∀ s, r < H s)` in namespace `DLNFibre.DLN.RLCT`, same conclusion. So the rename in step (b)
is call-site-compatible (see step (c)).

---

## The discharge-moment ladder (execute in this order, ideally one commit)

### (a) DELETE the Skeleton canonical

**Target (re-confirm by name):**

    rg -n "^theorem aoyagi_learning_coefficient\b" lean/DLNFibre/DLN/RLCT/Skeleton.lean

Currently `Skeleton.lean:1680-1687`. The decl as it stands:

    theorem aoyagi_learning_coefficient (H : Fin (L + 1) → ℕ) (r : ℕ)
        (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
        (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
        (hpos : ∀ s : Fin (L + 1), r < H s) :
        (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
      -- assemble: D1 (⨅ = rlctAt at the constructed deepestPoint) ▸ L2 (= closed form there).
      rw [deepest_point_reduction H r B hB hr hL]
      exact product_reduction H r B hB hr hL hpos

Delete the decl + its docstring (the `/-- … -/` immediately above, starting ~`:1642`; the block whose
tail is the `Assembled: D1 … A1` sentence). **What dies with it (its term-cone in Skeleton):**
`deepest_point_reduction` (consumes `rlctAt_deepest_le_of_optimal`) and `product_reduction` (consumes
`deepest_regular_core_normal_form ▸ reg_shift_add_core_eq_aoyagiLambda`). These become orphaned — see
step (d) for the cascade prune.

### (b) RE-MINT the canonical name in HeadlineL1Mint (rename the prestage)

In `lean/DLNFibre/DLN/RLCT/Validate/HeadlineL1Mint.lean`, rename
`aoyagi_learning_coefficient_prestage` → `aoyagi_learning_coefficient`. The rewritten body is
ALREADY the L=1/L≥2 fold; no proof change. Namespace stays `DLNFibre.DLN.RLCT`, signature unchanged
(see the signature note above), so the fully-qualified name `DLNFibre.DLN.RLCT.aoyagi_learning_coefficient`
is preserved — the same name the deleted Skeleton decl owned. Do (a) and (b) in the SAME commit so
there is never a transient duplicate `aoyagi_learning_coefficient` (both files are imported by AxCheck).
Update the docstring wording to drop "eventual replacement / controller re-points at mint" (it IS the
canonical now).

### (c) REPOINT `aoyagi_rrr` (the only term-consumer)

**Target:** `RRR.lean:89-93` (re-confirm: `rg -n "theorem aoyagi_rrr\b" lean/DLNFibre/DLN/RLCT/Validate/RRR.lean`).

`aoyagi_rrr` is the SOLE term-consumer of the unsuffixed canonical (verified: `RRR.lean` is imported
by nothing; the only other `aoyagi_learning_coefficient` occurrences are docstrings + the AxCheck
`#print`). Its current proof:

    aoyagi_learning_coefficient (L := 2) H r B hB hr (by norm_num) hpos

**Does it BREAK on the rename?** No — the renamed canonical has the identical signature, so this call
still elaborates (and would auto-upgrade to clean-three once the engine hole lands). But per priorities
R5(iii) we UPGRADE it to clean-three NOW (independent of the engine hole) by repointing to the banked
`aoyagi_learning_coefficient_L2` (`HeadlineL2Assembly.lean:88`, PROVEN clean-three
`[propext, Classical.choice, Quot.sound]`). `_L2` signature:
`(H) (r) (B) (hB) (hr) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hLlt : L < 3) (hpos)`.

Draft replacement (term form, mirrors the current defeq reliance — `rrrLambda H r` is defeq to
`aoyagiLambda H r`, so `ofReal (rrrLambda H r)` unifies with `_L2`'s `ofReal (aoyagiLambda H r)`):

    aoyagi_learning_coefficient_L2 (L := 2) H r B hB hr (by norm_num) (by norm_num) (by norm_num) hpos

If the defeq unification is fussy, the tactic form makes the `rrrLambda = aoyagiLambda` step explicit
via `rrrLambda_eq` (`RRR.lean:58`, `rrrLambda H r = aoyagiLambda H r := rfl`):

    by rw [rrrLambda_eq]
       exact aoyagi_learning_coefficient_L2 (L := 2) H r B hB hr (by norm_num) (by norm_num) (by norm_num) hpos

**Import add to `RRR.lean`:** `import DLNFibre.DLN.RLCT.Validate.HeadlineL2Assembly` (RRR currently
imports `Skeleton`, `Case222Rlct`, `Case212`). Confirm no cycle:
`HeadlineL2Assembly` does not import `RRR` (RRR is a leaf — imported by nothing).
**Effect:** `aoyagi_rrr` UPGRADES to clean-three. Also strike the RRR docstring lines that name the two
old open obligations (`deepest_regular_core_normal_form`, `rlctAt_deepest_le_of_optimal`) as inherited
sorries (RRR.lean:26-27, 76-78, 86-88) — they no longer are; `aoyagi_rrr` now rides `_L2` clean-three.

### (d) PRUNE the orphaned Skeleton rungs + the DecoratedDescent orphan (AFTER (a)-(c), never before)

**Verify orphanhood by grep before EACH delete** (term-application, not docstrings):

    # for NAME in each candidate below:
    rg -n "$NAME (H |M |r |\()" lean/DLNFibre/ | rg -v ":[0-9]+: *(--|\*)"

A candidate is safe to delete when that grep returns ONLY lines inside the decl being deleted (or
nothing). Delete in dependency order (deepest-consumer first):

1. `aoyagi_learning_coefficient` (Skeleton) — done in (a).
2. `product_reduction` (Skeleton, ~:1105) + `deepest_point_reduction` (Skeleton, ~:1150) — orphan once
   (1) is gone (verified now: their ONLY term-uses are inside the canonical at `:1687`/`:1686`).
3. `deepest_regular_core_normal_form` (Skeleton, ~:1087, its `sorry` at ~:1094) + `rlctAt_deepest_le_of_optimal`
   (Skeleton, ~:1135, its `sorry` at ~:1140) — orphan once (2) is gone (verified now: their ONLY
   term-uses are inside `product_reduction` at `:1110` / `deepest_point_reduction` at `:1160`).
4. `resolution_charts` (Skeleton, ~:1191) — ALREADY term-orphaned on this branch (NO term-application
   use anywhere; every hit is a docstring). It is a pure fossil now; prune with the batch.
   (Map to priorities R5's "Skeleton:1094/:1140/:1197": those three line numbers ARE
   `deepest_regular_core_normal_form` / `rlctAt_deepest_le_of_optimal` / `resolution_charts` — the
   three sorry-carrying rungs; the "+ product/deepest_point_reduction" are the two wiring theorems in
   item 2 above.)
5. `aoyagi_learning_coefficient_gen_of_descent` (`RouteMSJMint.lean:41`) — ORPHANED BY DELIVERABLE 1
   (the prestage arm rewrite was its only term-consumer; verified). Prune candidate. If pruned, its
   own cone orphans next (a DEEPER prune, gate the same way): `routeMBoxThresholdFinite_of_decoratedDescent`
   and then `DecoratedDescent` (`RouteMSJDecoratedRec.lean:206`) — delete these ONLY after confirming
   no other term-consumer (they are the fork-6 tombstone family). Do NOT delete `DecoratedDescent`
   pre-emptively; verify by grep first. (The `RouteMSJMint` import into `HeadlineL1Mint` is ALREADY
   dropped as part of deliverable 1 — nothing to do there at discharge.)

Note: also strike the now-dead docstring cross-references to these five Skeleton rungs scattered
across the D1/L2/R1 Validate lane (the `rlctAt_deepest_le_of_optimal` / `deepest_regular_core_normal_form`
/ `resolution_charts` mentions the grep in step (d) surfaces) — cosmetic, batch at leisure.

### (e) The `#guard_msgs` axiom gate (STAGED text — lands in AxCheck at discharge)

`AxCheck.lean` is another seat's live surface right now — this is PLAN TEXT only; it lands there at
the discharge. Two enforced gates (the mechanism per priorities R5: `#guard_msgs in #print axioms`
FAILS the build if the axiom set drifts from clean-three — a bare `#print` is diagnostic-by-another-name
and does NOT satisfy R5).

There is NO existing `#guard_msgs in #print axioms` block in the tree to copy verbatim; the emitted
format is `'<fully-qualified-name>' depends on axioms: [propext, Classical.choice, Quot.sound]`.
`#guard_msgs` is whitespace/quote-sensitive, so **capture the `/-- info: … -/` line VERBATIM from a
bare `#print axioms` run at discharge, then wrap it** — do not hand-type the expected line. Template
(mirroring the `#guard_msgs in` wrapper usage at `Foundations/Lambda.lean:97-109`):

    /-- info: 'DLNFibre.DLN.RLCT.aoyagi_learning_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
    #guard_msgs in
    #print axioms DLNFibre.DLN.RLCT.aoyagi_learning_coefficient

    /-- info: 'DLNFibre.DLN.RLCT.Engine.chartBridgeFaithful_buildTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
    #guard_msgs in
    #print axioms DLNFibre.DLN.RLCT.Engine.chartBridgeFaithful_buildTree

**Existing AxCheck lines to fix at discharge (they go stale/broken):**
- `AxCheck.lean:512` `#print axioms aoyagi_learning_coefficient` — the name is preserved by the rename,
  so this line still resolves; UPGRADE it to the `#guard_msgs` gate above and fix its comment
  ("sorryAx expected — 5 rungs pending" → clean-three).
- `AxCheck.lean:1281` `#print axioms …aoyagi_learning_coefficient_prestage` — the prestage is RENAMED
  away in step (b), so this line will FAIL TO RESOLVE (unknown identifier). Remove it (or repoint to
  the canonical — but the canonical gate is already at :512).
- `AxCheck.lean:192-194` (the "5 Skeleton rungs" prose) + `:1277-1279` (the prestage comment "carrying
  `hDescent` as an honest HYPOTHESIS (not sorryAx)") — BOTH stale. The `:1277-1279` prose is stale
  ALREADY on this branch after deliverable 1 (the prestage now carries `sorryAx` via the engine, not
  `hDescent`); update at discharge.

---

## Consumer / cycle audit (verified on this branch)

- **Import acyclicity (deliverable 1):** `HeadlineL1Mint` is imported ONLY by `AxCheck.lean`;
  `EngineDriver`'s closure (`EngineObligations`, `HeadlineGenAssembly`, and below) does NOT import
  `HeadlineL1Mint`. Adding `import …EngineDriver` to `HeadlineL1Mint` is acyclic. ✓
- **`_prestage` consumers:** only `AxCheck.lean:1281` (`#print axioms`, name-only). Dropping the
  `hDescent` binder breaks no term-consumer. ✓
- **`_gen_of_descent` consumers:** only the prestage arm (rewritten away) + its own decl. → ORPHAN
  (prune candidate, step (d).5). ✓
- **Canonical `aoyagi_learning_coefficient` term-consumers:** only `aoyagi_rrr` (RRR.lean:93) +
  `AxCheck.lean:512` (name-only). → step (c). ✓
- **`RouteMSJMint` import drop (done in deliverable 1, build-verified):** after the arm rewrite,
  `HeadlineL1Mint`'s remaining content is `aoyagi_learning_coefficient_L1` (uses
  `deepest_regular_core_normal_form_L1` from `DeepestBaseL1` + foundational `deepestPoint`/`prod`/
  `optimalSet` reachable via `DeepestBaseL1` and `EngineDriver`) and the prestage (uses
  `aoyagi_learning_coefficient_gen` + `Engine.engine_box_threshold_finite`, both via `EngineDriver`).
  Nothing from `RouteMSJMint` remained referenced, so its import was dropped and the file rebuilt green
  (`scripts/lb DLNFibre.DLN.RLCT.Validate.HeadlineL1Mint`, EXIT=0; axiom footprint unchanged). This
  severs `HeadlineL1Mint`'s transitive dependence on the `DecoratedDescent` machinery (fork-6 tombstone
  spirit).
