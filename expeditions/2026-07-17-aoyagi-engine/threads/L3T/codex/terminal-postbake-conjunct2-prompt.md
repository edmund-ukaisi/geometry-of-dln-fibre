<task>
Adjudicate whether a Lean conclusion is derivable from its hypotheses. Re-derive; don't trust me.

SETTING (ℝ^D polynomial world). At a fold node p (state S=L last layer, J = cleared ≥ 1), a TERMINAL-reaching
edge (rollover). foldResid p : Fin M → (ℝ^D→ℝ) → ℝ (M = d_N·d_0; residual family, SAME index type as the
generator family coreGen). σ = the step map; σ 0 = 0. foldB(child) u = (u pivot)^δ · foldB p(σ u), δ = [J=0]
so δ=0 here (J≥1); thus foldB(child) = foldB p ∘ σ. foldRegion = univ. foldB(child) is a nonzero polynomial.

StepInv F g b resid q V := (∀i j ContinuousOn (q i j) V) ∧ (∀i (F i∘g)0=0) ∧ (∀u∈V ∀i, (F i∘g)u = ∑_j q i j u·(b u·resid j u)).

HYPOTHESES (this is ALL):
 (H-D) ∃ q, StepInv coreGen (foldG p) (foldB p) (foldResid p) q univ.   -- FORWARD divisibility only (no Bézout/backward)
 (H-slot) ∀ j, [foldResid p j is Deg1-supported-and-vanishes-at-0] OR [∃ unit_j, continuous, unit_j 0 ≠ 0, foldResid p j = unit_j].  -- per-slot: degree-1 OR unit
 (H-cleared) ∃ (j₀ : Fin M) (unit_p), continuous unit_p ∧ unit_p 0 ≠ 0 ∧ foldResid p j₀ = unit_p.   -- a cleared/unit residual slot
Also S3: (coreGen i∘foldG p) 0 = 0 for all i.

CONCLUSION conjunct (2) to adjudicate:
 ∃ (i₀ : Fin M) (unit : ℝ^D→ℝ), continuous unit ∧ unit 0 ≠ 0 ∧
   ∀ u, (coreGen i₀ ∘ foldG(child)) u = foldB(child) u · unit u.

MY CLAIM (verify/refute): NOT derivable. Any valid `unit` equals the intrinsic divisibility quotient
Q_{i₀}(u) := (coreGen i₀∘foldG(child))u / foldB(child)u on {foldB(child)≠0} (dense), so unit 0 = Q_{i₀}(0).
Q_{i₀}(0) = ∑_j q(i₀,j)(0)·foldResid p j(0) [via H-D pulled through σ, σ0=0] = q(i₀,j₀)(0)·unit_p(0) (only the
unit slot j₀ is nonzero at 0; degree-1 slots vanish). So need q(i₀,j₀)(0) ≠ 0 for some i₀. But q is the
EXISTENTIAL witness of (H-D) (forward divisibility) — nothing forces its (i₀,j₀)-entry nonzero at 0. Indeed a
q with q(·,j₀) ≡ 0 (generators represented via other slots) satisfies (H-D) yet kills conjunct 2. The
born-terminally GENERATOR (i₀ bare) is backward/Bézout content; H-cleared only gives a bare RESIDUAL slot.
Charitable check: if q were the Kronecker-derived pullback (diagonal ≡ 1), then q(j₀,j₀)=1 and it works —
but (H-D) is ∃q, not that specific q.
</task>
<output_contract>
1. VERDICT {DERIVABLE, NOT-DERIVABLE/FALSE, DEPENDS-ON-q}.
2. If not derivable: the cleanest witness (a q satisfying H-D but killing conjunct 2), or the missing hypothesis.
3. Does H-slot (the per-slot disjunction) add anything that closes it (vs H-cleared alone)?
4. Minimal fix: what generator-side datum makes conjunct 2 provable?
Under ~350 words. Flag INFER vs KNOW.
</output_contract>
<grounding_rules>Reason from the defs; the residual index type = the generator index type (both Fin M), but foldResid p and coreGen are DIFFERENT functions.</grounding_rules>
