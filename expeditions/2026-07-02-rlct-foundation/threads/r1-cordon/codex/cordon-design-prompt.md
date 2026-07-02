# Citation cordon design — decorrelated review request

## Context
Lean 4.29 + Mathlib. A math-formalisation repo (`DLNFibre`). Goal: a machine-enforced
"citation cordon" so that "what is fully formalised vs cited" is a checkable, forget-proof
invariant. Cited external theorems (monuments: resolution of singularities, Aoyagi's RLCT
computation, Watanabe's bound) are Lean `axiom`s; the kernel auto-tracks every axiom
dependency via `collectAxioms` (the `#print axioms` engine).

## The mechanism
For a declaration D:
  UNACCOUNTED(D) = collectAxioms(D) − FOUNDATIONAL − CITED_TAGGED
where
  FOUNDATIONAL = {propext, Classical.choice, Quot.sound}  (explicit, extensible allowlist)
  CITED_TAGGED = { axioms carrying the @[cited "<source>"] attribute }
D is "proved modulo declared cites" ⟺ UNACCOUNTED(D) = ∅.

## Components
1. `@[cited "<source>"]` — a `registerParametricAttribute String`; getParam parses a string
   literal from the syntax, stored as structured data; getParam? reads it back per-axiom.
2. One core (DRY) over `Lean.collectAxioms`: computes UNACCOUNTED set + CITED set (the tagged
   axioms D uses, with their sources) + reads each axiom's source module (Environment.getModuleFor?).
3. Frontends:
   - `#audit_cited foo` — in-file command mirroring `#print axioms` (uses realizeGlobalConstWithInfos
     + collectAxioms, then filters). Elaboration-time, has the live env with extensions loaded.
   - `lake exe cited-audit` + `scripts/cited` wrapper — the repo gate, ENFORCING (nonzero exit).
     Loads the DLNFibre env via `importModules (loadExts := true)` after `enableInitializersExecution`
     (the runLinter pattern; unsafe). Three checks:
     (a) UNACCOUNTED = ∅ over all public decls in DLNFibre/**;
     (b) every `axiom` declared in DLNFibre/** is @[cited] AND its source module file path matches
         `**/Cited.lean` (an allowlist of located cite files);
     (c) `--manifest`: per-headline cite map from the @[cited] sources.

## Adversarial fixtures (built FIRST, they are the spec)
(a) fully-proved decl → FORMALISED (UNACCOUNTED=∅, CITED=∅)
(b) decl using a tagged+located cite axiom → CITED[src]
(c) decl using an UNTAGGED axiom → UNACCOUNTED, gate must FAIL
(d) an axiom outside Cited.lean / untagged → LOCATION violation, gate must FAIL
(e) transitive: A uses B, B is @[cited] → A classified CITED (kernel transitivity)

## Questions for you (xhigh reasoning)
1. Is `collectAxioms − foundational − @[cited]` SOUND and COMPLETE as a definition of
   "proved modulo declared cites"? Any way an unaccounted dependency could hide?
2. Is the forget-proofness argument correct: forgetting the @[cited] tag on an axiom means
   collectAxioms still returns it, it is not in CITED_TAGGED, so it lands in UNACCOUNTED and the
   gate goes red? Any escape?
3. Parametric attribute (String param) vs a bare @[cited] tag + mandatory `CITED[src]` docstring
   the tooling parses — which is more robust for this use? Edge cases of parametric attributes in
   an env-reading exe (loadExts, enableInitializersExecution)?
4. Edge cases: (i) Mathlib foundational axioms BEYOND the 3 — does Mathlib introduce others (e.g.
   `Lean.ofReduceBool`, `Lean.trustCompiler`, `Classical.choice` variants, quotient/propext only)?
   Should the allowlist be static-3 or discovered? (ii) `native_decide` introduces `Lean.ofReduceBool`
   as an axiom — the repo bans native_decide, so should the cordon TREAT ofReduceBool as UNACCOUNTED
   (a feature, catching sneaked-in native_decide)? (iii) A `sorry` becomes `sorryAx` — should that be
   UNACCOUNTED too (yes, I think — but scripts/sorries already catches it; is double-coverage good)?
5. Location check: is matching the axiom's source-module file path against `**/Cited.lean` the right
   invariant, or is there a cleaner in-Lean way (e.g. requiring cite axioms to also carry a marker)?
6. Any failure mode where the exe's env (imported oleans) disagrees with the in-file `#audit_cited`
   env (elaboration), causing a green `#audit_cited` but red gate or vice versa?
7. Anything I'm missing that would make this cordon claim "green = no unaccounted axioms" FALSELY.

Be concrete and adversarial. This is the load-bearing correctness step of the whole rung.
