<task>
You are auditing a Lean 4 formalisation for PRECISION/NAMING honesty (does a theorem's
name + statement denote exactly what it proves, no more?) and for "is this the right
object / non-vacuous / honestly discharged". Be adversarial and neutral — I want you to
FIND overclaim if it exists, not reassure me.

Context (deep-linear-network RLCT project, Aoyagi's learning coefficient). Three theorems:

(1) `aoyagi_learning_coefficient_frontPivot` (file DeepestNormalFormFrontPivot.lean:125).
Statement (paraphrased faithfully):
  hypotheses: H : Fin(L+1)→ℕ, r:ℕ, B matrix with B.rank=r, hr (r ≤ H s ∀s),
    hL (1≤L), hL2 (2≤L), hpos (r < H s ∀s),
    hJfront (the B-determined pivot embedding .choose = frontEmbed — the "B's rank-r pivot
             columns are the first r" front-pivot WLOG hypothesis),
    htop (B's top r rows full rank),
    hGne (reduced-core germ nonvanishing near 0),
    hRValue (rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)  -- R1's resolution CORE VALUE),
    hD1 ( (⨅ w ∈ optimalSet H B, rlctAt (dlnLoss H B) w) = rlctAt (dlnLoss H B) (deepestPoint) )
  conclusion:
    (⨅ w ∈ optimalSet H B, rlctAt (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)
  proof: rw [hD1, deepest_normal_form_of_value_frontPivot ..., reg_shift_add_core_eq_aoyagiLambda ...].
  So it rewrites the infimum to rlctAt(deepestPoint) via hD1, then applies the (now-proven)
  deepest-point normal form (rlctAt deepestPoint = nReg/2 + lambdaCore, front-pivot route),
  then the closed-form recombination nReg/2 + lambdaCore = aoyagiLambda.

Facts about the environment (VERIFIED by me):
  - hRValue is the value of `resolution_charts` (Skeleton R1), which is STILL a `sorry`.
  - hD1 is the value of `deepest_point_reduction` (Skeleton D1), whose ≥-direction
    `rlctAt_deepest_le_of_optimal` is STILL a `sorry`. hD1's ≤-direction is free
    (deepestPoint ∈ optimalSet). So the only NON-trivial content of the equality hD1 is
    the ≥-leg (rlctAt deepestPoint ≤ everything).
  - hJfront, htop are OPEN alignment/WLOG hypotheses (deferred to "KC1").
  - The genuinely NEW thing just proved (by closing an inline `hstep2`) is the general-L
    (L≥3) DEEPEST-POINT gauge-slice normal form: rlctAt(dlnLoss H B)(deepestPoint) =
    rlctAtOn(regularShift + coreΦ), via a front-pivot gauge chart. The `deepest_normal_form_of_value_frontPivot`
    step consumes that.
  - The theorem is NOT wired into any Skeleton theorem; it is only referenced by an
    `#print axioms` line in an AxCheck file. The Skeleton learning-coefficient target
    (`deepest_regular_core_normal_form`, Skeleton:1124) is STILL a `sorry`.

(2) Its docstring calls hD1 "the D1 ≥-leg `hD1` (`⨅ = rlctAt deepestPoint`)".

(3) For contrast, the L=2 sibling `deepest_regular_core_normal_form_L2` has conclusion
    ONLY `rlctAt(dlnLoss H B)(deepestPoint) = nReg/2 + ofReal(lambdaCore M)` (the deepest-point
    normal form), explicitly conditional on hJfront/htop/hRValue, with a candid docstring.
    It does NOT reach `⨅ = aoyagiLambda`.

Questions:
Q1. Is the NAME `aoyagi_learning_coefficient_frontPivot` + the conclusion `⨅ = aoyagiLambda`
    an OVERCLAIM given that two load-bearing inputs (hRValue = R1, hD1 = D1-≥leg) are (a) taken
    as explicit hypotheses and (b) in fact still unproven `sorry`s elsewhere? Consider the
    principle "a result's name and statement denote exactly what is proven — no more", where
    a conditional theorem `foo (h : Hard) : Big` is generally acceptable if h is an EXPLICIT
    hypothesis and documented. Does the "learning coefficient" naming cross a line, or is it a
    legitimate conditional assembly node?
Q2. Is calling hD1 (an EQUALITY ⨅ = rlctAt deepestPoint) "the D1 ≥-leg" in the docstring a
    precision slip? Justify.
Q3. Is there a vacuity risk: could the hypothesis set {hpos, hJfront, htop} be mutually
    UNSATISFIABLE (making the theorem vacuously true)? Give a concrete config
    (L, H, r, B) that plausibly satisfies hpos ∧ htop ∧ (B's pivot columns are the first r),
    or argue why hJfront (about a Classical.choice) cannot be witnessed concretely.
Q4. What is the single most precise one-sentence restatement of what closing `hstep2` actually
    ESTABLISHED as new bedrock (as opposed to what it assembled conditionally)?
</task>

<output_contract>
Four numbered answers Q1–Q4, each ≤ 6 sentences. For Q1 give a verdict token:
OVERCLAIM / ACCEPTABLE-CONDITIONAL / BORDERLINE + one-line reason. For Q3 give either a
concrete (L,H,r,B) or a crisp impossibility argument. No preamble.
</output_contract>

<grounding_rules>
Distinguish clearly what you can INFER from the given statements vs what you would need to
SEE in the Lean source to be sure. Flag any assumption you are forced to make. Do not invent
Lean lemma behavior; reason from the stated shapes. You may NOT claim the build/axioms are
clean — that is being verified separately.
</grounding_rules>
