<task>
Adjudicate ONE structural question about a singularity resolution, independently. I withhold my leaning.
</task>

<setup>
Loss F = ‖C¹·C²·C³···‖² of a product of matrices, resolved at the origin by Aoyagi's SEQUENTIAL (S,J)
blow-up: at each step, take the current "corank block" Δ (the residual block of the current layer's
matrix, coupling to the downstream product Z = C^{s+1}···), blow up ONE radial coordinate u for the WHOLE
block (Δ = u·Δ', top-left normalised), charge u by the full block codimension, then use unit-triangular
(det-1) row/col transforms to reduce Δ' to diag(1, D_next), advancing to a smaller residual block; recurse
carrying D_next × the downstream product. Terminal (fully-diagonal) loss = Σ b_i² (b_i = products of the
introduced radials) — normal crossing.
</setup>

<facts_established>
- For a corank-2 block Δ (2×2) coupled to a downstream product Z (symbolic, exact): ‖Δ·Z‖² = u²·‖Δ'·Z‖²
  (single radial u factors CLEANLY, Jacobian u³); and unit-triangular transforms L=[[1,0],[-b,1]] (rows),
  R=[[1,-a],[0,1]] (cols), depending ONLY on Δ' (NOT on Z), reduce Δ' to diag(1, δ'), δ'=d-ab. The
  reduced loss = ‖pivot row‖² (Morse) + δ'²·‖(downstream row)‖² (a corank-1 coupled residual). The
  unit transforms absorb into the ADJACENT downstream factor (C² ↦ Q⁻¹C²), leaving the DEEPER shared
  factor C³ UNTOUCHED (product associativity, exact).
- So a corank-2 step REDUCES to: one clean radial u + a Morse pivot + a corank-1 coupled residual — the
  latter being the same object as the corank-1 (e.g. (3,3,3,3)) recursion, which closes.
- The RLCT VALUE ½·minAdm is independently certified for all branch types.
</facts_established>

<the_question>
Does this SEQUENTIAL single-radial-per-block resolution REACH normal crossing (Σ b_i²) for a genuinely
COUPLED corank-≥2 case at L≥3 — i.e. where the corank-2 block at one layer and the rank-drops at deeper
layers SHARE the deeper product factors (e.g. M=(3,3,3,4), binding branch (1,0,0), layer-1 corank block
2×2, layer-2 charge 3, sharing C³)? Or is there a coupled corank-≥2 configuration where the sequential
per-layer scheme leaves a residual that a finite explicit chart cover CANNOT express as normal crossing —
so that a SIMULTANEOUS (non-sequential) resolution of the shared degeneracies is genuinely required?

Probe hardest at: after the corank-2 reduction to a corank-1 residual δ'²·‖(downstream row)‖², when the
recursion later resolves the downstream product (which shares factors with OTHER blocks already resolved),
can the deeper resolution be done independently, or do the already-introduced radials (u, δ') RE-COUPLE
with the deeper blow-up in a way no sequential chart captures?
</the_question>

<grounding_rules>
- Distinguish PROVE / argue / heuristic. The value is not in question; the STRUCTURE (sequential reaches
  normal crossing vs needs simultaneous) is.
- If sequential suffices, say why the "re-coupling" concern is void. If simultaneous is needed, give the
  concrete configuration and the residual that no sequential chart expresses.
- Do NOT assume my leaning.
</grounding_rules>

<output_contract>
1. VERDICT: sequential-reaches-normal-crossing | simultaneous-required | uncertain.
2. The decisive reason, focused on the re-coupling of already-introduced radials with the deeper blow-up.
3. If sequential: the one step most likely to be intricate (but bounded) in a formalisation.
</output_contract>
