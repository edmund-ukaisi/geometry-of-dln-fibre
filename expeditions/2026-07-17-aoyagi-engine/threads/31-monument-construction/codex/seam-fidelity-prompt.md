<task>
I am a FIDELITY reviewer auditing a Lean 4 salvage adapter in an Aoyagi-DLN RLCT
formalisation. I need a decorrelated read on whether a "realization seam" predicate
is the RIGHT geometric obligation, or whether it is (a) vacuously/trivially
satisfiable in a way that does NOT correspond to a real resolution atlas, (b)
over-constrained (unsatisfiable by the real atlas, so the residual sorry has a FALSE
statement), or (c) has a gap in the derivation "seam ⟹ hlb ∧ hattain".

SETUP.
- `d : Fin (N+1) → ℕ` are DLN layer widths. `coreGen d e` is the concrete flattened
  product-map entry family (the matrix-multiplication map entries), a family
  `Fin (d_N·d_0) → (Fin (flatDim d) → ℝ) → ℝ`. Its sum of squares `∑ (coreGen)ᵢ²` is
  the zero-product square-Frobenius DLN loss (up to a measure-preserving flatten).
- `Resolution F 0` is a record: a finite atlas of certified analytic `Chart`s of `∑Fᵢ²`
  at the origin. Each `Chart` carries: an analytic map `g`, a compact source domain,
  a two-sided ideal identity `⟨Fᵢ∘g⟩ = ⟨monomialFam bexp⟩` on a neighbourhood, a
  Jacobian certificate `|det Dg| = jacWeight jac · unit`, a dominant monomial index
  `k₀`, a divisibility chain, and unit-multiplicity on binding axes. `bindingAxes (bexp k₀)`
  = the coordinate axes `a : Fin D` where the dominant monomial's exponent is positive.
  `(charts c).jac a + 1` is the chart's binding-axis exponent (paper's M_{s,k}).
- The Engine (a retired-but-kernel-checked combinatorial construction) builds a
  FIXED resolution TREE `buildTree d (conOracle d) conRoot` whose leaves carry divisor
  exponents `l.divExp k` (nat). `terminalExponents (buildTree d ...)` = the flat list of
  all `l.divExp k` over all leaves. Two Engine theorems are proved axiom-clean:
    * `minAdm_le_terminalExponents`: every terminal exponent ≥ `minAdm d`. (width-free)
    * `o5_core_realized` (needs positive widths): ∃ leaf l, ∃ k, `l.divExp k = minAdm d`.
  And a bridge `qipMin d = minAdm d = cCodim d 0` (the paper's codimension C).

THE SEAM (`AtlasRealizes d res`, res : Resolution (coreGen d e) 0), a conjunction:
  (i)  ∀ chart c, ∀ a ∈ bindingAxes((charts c).bexp (charts c).k₀),
         (charts c).jac a + 1  ∈  terminalExponents(buildTree d (conOracle d) conRoot).
  (ii) ∀ leaf l ∈ leaves(buildTree d (conOracle d) conRoot), ∀ k : Fin l.numDiv,
         ∃ chart c, ∃ a ∈ bindingAxes((charts c).bexp (charts c).k₀),
           (charts c).jac a + 1  =  l.divExp k.
Note both clauses use VALUE membership/equality of nat exponents (not a structural
chart↔leaf correspondence).

THE ADAPTER derives, from `AtlasRealizes d res`:
  hlb:     ∀ c, ∀ a ∈ bindingAxes(...), qipMin d ≤ (jac a + 1 : ℤ)
           [proof: clause (i) puts jac a+1 in terminalExponents, minAdm ≤ it, qipMin=minAdm]
  hattain: ∃ c, ∃ a ∈ bindingAxes(...), (jac a + 1 : ℤ) = qipMin d
           [proof: o5_core_realized gives leaf l, k with divExp k = minAdm; clause (ii)
            at that (l,k) gives c,a with jac a+1 = divExp k = minAdm = qipMin]
The residual sorry (the "monument") is now `∃ res : Resolution (coreGen d e) 0, AtlasRealizes d res`.
The FINAL value theorem computes `2·rlctAt(∑coreGenᵢ²) 0 = res.divisorMin` (a SEPARATE
frontier CoV leaf) and `res.divisorMin = qipMin` (from hlb+hattain), giving
`2·rlctAt = cCodim d 0`. `rlctAt` is intrinsic to the fixed function `∑coreGenᵢ²`.

QUESTIONS.
1. Vacuity/false-surjectivity: is clause (ii) trivially satisfiable, or can `AtlasRealizes`
   be satisfied by a res that is a genuine `Resolution (coreGen d e) 0` but whose binding
   divisors do NOT reflect the true geometry — letting the value come out wrong? (Note the
   value is intrinsic via rlctAt; argue whether that closes the hole.)
2. Over-constraint: clause (ii) is UNIVERSAL over all leaves/divisors, but the adapter only
   USES it at the single (l,k) from o5_core_realized. Could the universal form make the
   residual `∃ res, AtlasRealizes` FALSE (unsatisfiable by the real Aoyagi atlas) even
   though `∃ res, hlb ∧ hattain` is TRUE? I.e. is the value-membership seam achievable by
   the intended atlas where "each chart is a leaf, binding axes are the t̃=0 terminal divisors"?
3. Is there any DERIVATION gap in "AtlasRealizes ⟹ hlb ∧ hattain" as sketched?
4. Any fidelity mismatch worth escalating between the seam and the informal claim
   "the geometric charts realize the built resolution tree"?
</task>

<output_contract>
Answer Q1–Q4 in order, each ≤ 8 sentences. For each: a one-word verdict
(VACUOUS / SOUND / OVER-CONSTRAINED / GAP / FAITHFUL / UNCLEAR) then the reasoning.
If you find a concrete counterexample (a res satisfying the seam with wrong value, or a
real-atlas configuration violating clause ii), give it explicitly. End with the single
most important thing a fidelity reviewer should escalate, or "nothing to escalate".
</output_contract>

<grounding_rules>
Distinguish what you can prove from the given signatures (fact) from what you infer about
the intended geometry (inference) — label each. You may NOT assume the Engine tree is
correct Aoyagi geometry; treat `buildTree` as an opaque fixed combinatorial object whose
only guarantees are the two theorems stated. Flag any place your verdict depends on an
unstated assumption.
</grounding_rules>
