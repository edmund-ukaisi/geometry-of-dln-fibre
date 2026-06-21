<task>
I am designing the precise statement boundary for a Lean 4 formalisation of one theorem from a
2024 math paper (Lehalleur–Rimányi, "Geometry of the fibers of the multiplication map of deep
linear neural networks"). The theorem is the "RLCT payoff": for deep linear networks, the real
log-canonical threshold (rlct) of the square-Frobenius loss equals half the codimension of a fibre.

I need you to independently adjudicate ONE question: given that I have ALREADY formalised, with
zero citations, the GEOMETRIC codimension C of the relevant variety, what is the MINIMAL and most
faithful set of facts I must take as a CITED axiom/interface (vs. prove in-engine) so that the
in-engine theorem honestly states "rlct = C/2" WITHOUT silently asserting unproved analytic content?
</task>

<grounding_rules>
Facts (from the paper, verified against source):
1. Loss: K^DLN_B(A) = ‖mult(A) − B‖²_F = Tr((mult A − B)^t (mult A − B)), a polynomial (hence
   real-analytic) function on the real parameter space Rep_d = ∏ Mat. K^DLN_B ≥ 0.
2. (K^DLN_B)^{-1}(0) = mult^{-1}(B) = the fibre. (elementary)
3. rlct(F) := sup{ s | |F|^{-s} locally integrable }. Definition uses real-analytic resolution of
   singularities / archimedean zeta meromorphic continuation (Atiyah). Mathlib has NO rlct,
   log-canonical-threshold, or singular-learning-theory machinery.
4. General bound (Prop 8.4(iii) / eqn rlct_upper_bound_glob): for nonneg real-analytic F with the
   inf attained, rlct(F) ∈ (0, codim F^{-1}(0) / 2]. CITED (resolution of singularities).
5. The paper's main theorem (Thm 8.6, "thm:aoyagi-rlct"): rlct(K^DLN_B) = codim mult^{-1}(B) / 2.
   Its PROOF is: compare the paper's own codim formula (Thm 7.x) against Aoyagi [aoyagi] Theorem 1,
   which independently computed rlct(K^DLN_B) directly. So the equality is purchased by Aoyagi's
   analytic computation, recognised as matching the codim. The codim→rlct identification is NOT
   reproved geometrically in the paper.
6. I have LANDED in Lean (zero-cited, over an algebraically closed char-0 field, then base-changed):
   the GEOMETRIC codimension C = codim Σ̄^r (as Ideal.height of a minimal prime), and the fibre-codim
   shift codim mult^{-1}(B) = codim Σ̄^r + r(d_0 + d_N − r).

Output-contract rules:
- Keep INFERENCE separate from FACT. If you are inferring what "should" be axiomatised, say so.
- Do NOT write Lean code; describe the interface shape in prose + signatures.
- Be specific about which of {the rlct DEFINITION, the general bound rlct ≤ codim/2, the equality
  rlct(K^DLN_B) = codim/2} must be Cited, and which (if any) could be proved from the others.
</grounding_rules>

<output_contract>
1. The minimal Cited interface: exactly which facts go in as axioms, stated as cleanly as possible.
   Distinguish the two plausible designs: (A) axiomatise the WHOLE equality rlct(K^DLN_B)=codim/2
   directly (Aoyagi as a black box); (B) axiomatise the rlct as an opaque function + the general
   bound + a separate lower-bound mechanism. Which is more faithful to "name = content"?
2. Whether the in-engine theorem, after plugging the geometric C into the interface, proves anything
   non-trivial, or is a pure restatement — and whether that matters for honesty.
3. The single biggest way a reader could be MISLED by a poorly-named/scoped version of this theorem,
   and the guard against it.
4. Is the component count θ (number of top-dimensional irreducible components of the fibre) related
   to the rlct or its multiplicity? (One-line answer + reason.)
</output_contract>
