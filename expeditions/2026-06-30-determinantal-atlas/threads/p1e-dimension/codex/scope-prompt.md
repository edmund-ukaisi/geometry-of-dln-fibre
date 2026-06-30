<task>
I am a Lean-4/Mathlib formaliser on a "build-the-buildable" expedition. Rung P1.e: re-home + generalize
the "rank-stratum dimension r(n+m−r) / codimension (n−r)(m−r)" results into a new clean module
`Core/RingTheory/Determinantal/Dimension.lean`, in a BARE Mathlib-mirror namespace (`Matrix` / `Ideal`),
NOT the project's `DLNFibre.Core` namespace.

THE ASSIGNMENT BRIEF SAYS (verbatim, the "precision point"):
  "These results RIDE A CITED result 'Brick A' (the determinantal codimension/height). Keep Brick A
   explicitly named and Cited — do NOT fold it into a theorem name that reads as a fully-proved dimension.
   Separate Proved/Cited. First establish how Brick A currently exists in-repo (the tree is axiom-free, so
   Brick A is NOT a global axiom; it is either a threaded hypothesis or a separately-stated cited lemma)
   and PRESERVE that structure — do not convert it to a global axiom, and do not 'prove' it by absorbing it.
   name = content."

WHAT I ACTUALLY FOUND IN THE REPO (this contradicts the brief):
  - "Brick A" is the theorem `codimRepCanonical_productRankLocusLE_eq_cCodim` in `Core/SigmaCodim.lean`.
    Its docstring states explicitly: "**Brick A (Proved, zero-cited, general in r).**" It is PROVED
    unconditionally (over CharZero + Infinite field) by the project's own orbit-closure codimension engine
    (`codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim` + the per-orbit Voigt lower bound + a
    minimising Kostant-partition realizer). No `sorry`, no `axiom`.
  - The WHOLE Lean tree is sorry-free AND axiom-free (`scripts/sorries` → 0 sorry, 0 axiom). I confirmed
    `#print axioms` on these would be the standard `[propext, Classical.choice, Quot.sound]`.
  - The ONLY genuine citations in the repo are DLN-side analytic RLCT bricks (`cited_watanabe_upper`,
    `ln_lower` = Aoyagi/Watanabe `rlct ≤ ½·codim` and the matching lower bound), threaded as fields of a
    structure in `DLN/RlctPayoff.lean`. They are NOT in the Core determinantal/dimension/height stack at all.
  - The two source files for P1.e:
    * `DeterminantalStratumDim.lean`: `varietyDim_productRankLocusLE_stratum` (variety dim = r(n+m−r));
      its proof uses Brick A (the PROVED `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`) + the
      catenary bridge `codimRep + varietyDim = card = m·n` + the combinatorial `cCodim ![n,m] r = (n−r)(m−r)`.
    * `DeterminantalChartRing.lean`: `height_map_sigmaIdeal_away_eq_cCodim` (localized base ideal height
      = C = (n−r)(m−r)), also via the PROVED Brick A.
  So: the recon report that produced the brief said "rides cited Brick A" — but the code says Brick A is
  PROVED, zero-cited. The recon appears to have mis-tagged it.

ADDITIONAL SCOPE FINDING:
  - The dimension/codim/height results are NOT bare-`Matrix` content: they are wired to the project's DLN
    orbit-codimension engine (`RepCoord d`, `canonicalCoord`, `codimRepCanonical`, `sigmaIdeal`, `varietyDim`,
    the catenary bridge). The genuinely matrix-general/re-homeable pieces are: the arithmetic identity
    `(n−r)·(m−r) + r·(n+m−r) = m·n` (pure ℕ, with r ≤ n, r ≤ m) and the combinatorial codim value
    `cCodim ![n,m] r = (n−r)(m−r)` — but `cCodim` itself is a project engine object, not Mathlib.
  - P1.b/c/d already landed sibling modules `Core/RingTheory/Determinantal/{Basic,Strata,Schur}.lean` in the
    bare `Matrix` namespace, general over `[Field k]`/`[CommRing R]`; `Schur.lean` already has
    `finrank_pivotRankChart_params = δ = r(p+q−r)` and the arithmetic `r*r + r*(q−r) + (p−r)*r = r*(p+q−r)`.
  - `dStratum`/`stratumPartition`/the stratum-Kostant lemmas are consumed by ~8 files in the Phase-2 bundle
    layer (out of scope this rung). A move-and-rename of `dStratum` would ripple into Phase 2.

MY TENTATIVE PLAN:
  1. name=content cuts BOTH ways: naming a PROVED result `_of_brickA` or "Cited" would be an INVERSE
     overclaim (under-claiming a proved result as cited). So I will NOT introduce a `_of_brickA`/cited
     framing for the dimension. Instead: re-home the genuinely-general arithmetic/codim-value content to the
     bare-namespace `Dimension.lean`, and keep the variety-dimension headline where it depends on the DLN
     engine, but state it precisely as PROVED (not cited), with a docstring that names its load-bearing
     input (the PROVED Brick A) as Proved, not Cited.
  2. Because the dimension HEADLINE is engine-bound (not matrix-general), the honest re-home is: move the
     pure-`ℕ` arithmetic + the closed-form codim/dim *formulas* and a clean restatement into `Dimension.lean`
     (bare namespace), and leave the engine-coupled `varietyDim_…_stratum` either (a) generalized in place
     and re-pointed, or (b) thinly re-exported. I will NOT fabricate a "cited Brick A hypothesis" the repo
     doesn't have.
  3. Confirm I do NOT introduce any global axiom; #print axioms stays the standard 3.
</task>

<output_contract>
  Answer in 4 short sections, terse:
  (A) BRICK-A VERDICT. Given Brick A is PROVED zero-cited in-repo (not cited), is my reading correct that
      naming the dimension result `_of_brickA`/"Cited" would be a precision VIOLATION (under-claiming),
      and the honest move is to state it as Proved while naming its proved input? Or is there a reading
      under which the brief's "keep Brick A cited" is still right (e.g. a hidden citation I should hunt
      harder for)? If you think I should hunt harder, name exactly what to grep for.
  (B) RE-HOME SCOPE. Given the dimension headline is DLN-engine-bound (not bare-Matrix), what is the
      RIGHT minimal content to put in a bare-`Matrix`/`Ideal`-namespace `Dimension.lean` vs what should
      stay engine-coupled? Is it acceptable (name=content / bedrock) for `Dimension.lean` to hold the
      general arithmetic + formula restatements and re-export, with the engine-bound headline staying in
      its current DLN-Core home but generalized/cleaned? Or should I force the whole headline into the
      bare namespace (which I think is impossible without dragging the orbit-codim engine)?
  (C) PRECISION NAMING. Concrete naming guidance for the dimension + codim theorems so name=content holds:
      object-eq vs finrank-eq vs dimension(ringKrullDim/height)-eq must be distinguished. Give the 2–3
      theorem names you'd use.
  (D) TRAPS. The single biggest way this rung goes subtly wrong (precision or scope), and the cheapest guard.
</output_contract>

<grounding_rules>
  Flag inference vs fact. You do NOT have the repo; reason from the description I gave. If a claim needs
  repo evidence I have not provided, say "would need to check X" rather than asserting.
</grounding_rules>
