<task>
Lean-4/Mathlib (v4.29) measure-theory DESIGN review. Deep linear network RLCT, depth-2 "Schur core"
finiteness. Define (frobSq = squared Frobenius norm; matBox r c T = the box of r×c matrices with entries in
[−T,T]; rmatMul = matrix product):

  SchurCore p r c' T  :=  ∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} (frobSq(Δ·S))^{−c'}  < ⊤   (c'>0).

GOAL: prove SchurCore p r c' T for ALL r, in the "cap-B regime" c' ≤ p/2 (more precisely whenever
c' < lam(r,p) := ½·minAdm(r,r,p) AND lam(r,p) ≤ p/2 — the regime where the binding stratum is t=0, i.e.
p ≥ 2r roughly). Call this lemma schurCoreP_directMorse. It is the cap-B branch of a p-dependent dispatch
(the cap-A branch is the existing "carve" + corank recursion, for c' > p/2).

WHAT IS ALREADY BUILT (sorry-free, {r,p}-general, that I MUST reuse — do not redesign these):
1. The r²-chart RADIAL-Δ cover: SchurCore reduces (flatten the r² Δ-cells, MeasurableEquiv) to a SUM over
   r² charts p∈Fin(r²); each chart is, after the radial blow-up Δ = (radial a)·(angular ratios z over
   Fin(r²−1)), an integral
     ∫_{a∈[−T,T]} ∫_{z∈[−1,1]^{r²−1}} |a|^{(r²−1)−2c'} · (angular integrand in z,S).
   (This is matBoxG_outer_flat / gFlatG_cover_sum, p-free — the cover reshapes the r×r Δ-block only.)
2. radial_aAxis_divisor_lt_top : ∫_{a∈[−T,T]} |a|^{(r²−1)−2c'} da < ⊤  ⟺  c' < r²/2.  [the cap-B radial axis]
3. radial_loss_chart_lt_top {r p} : the FULL per-chart blow-up
     ∫_a ∫_R |a|^{r²−1} · frobSq((a·R)·S)^{−c'} < ⊤  for c' < r²/2, GIVEN
     hSfin : ∫_{R∈matBox r r T} frobSq(R·S)^{−c'} < ⊤  (the angular box-integral, S fixed).
   It Tonelli-separates the radial axis (item 2) from the angular hSfin.

THE GAP for cap-B: in the existing p=4 firing, the angular integral is bounded by the CARVE +
corank-recursion (needs hr:3≤r + the IH — this is the cap-A machinery, threshold c'>2=p/2). For cap-B
(c' ≤ p/2, which includes r=1,2 at p=4 — closed there by SEPARATE hand lemmas using the radial cover, NOT
the carve) I need the angular bound WITHOUT the recursion: a DIRECT proof that
   hSfin : ∫_{R∈matBox r r T} frobSq(rmatMul R S)^{−c'} < ⊤   (S∈matBox r p, or jointly over (R,S))
holds for c' small (c' ≤ p/2, or c' < r²/2). My numerics: ½·minAdm(r,r,p) is the SHARP threshold; in cap-B
the binding stratum is t=0 with value r² (so lam=r²/2), i.e. the {Δ=0}/{R=0} normal-crossing of r² linear
forms — codim r², so frobSq(Δ·S)^{−c'} is locally integrable near the deepest point iff c' < r²/2.

QUESTIONS:
1. What is the cleanest DIRECT bound for the angular/joint integral ∫∫ frobSq(R·S)^{−c'} over the bounded
   box, valid for c' < r²/2 (cap-B), reusing items 1–3 and NOT the carve/recursion? Candidate routes:
   (a) bound frobSq(R·S) BELOW by a single dominant squared-entry / a sum of squares of the r² entries of
   a fixed column, reducing to a product of 1-D ∫|x|^{−2c'} type integrals (finite iff 2c' < 1?? — that
   gives c'<1/2, too weak). (b) Use the {Δ=0} radial blow-up DIRECTLY: SchurCore's OWN radial blow-up
   (item 1, on Δ) already yields radial axis |a|^{r²−1−2c'} (finite c'<r²/2) × angular ∫_z∫_S
   frobSq((unit-norm R(z))·S)^{−c'}, and on the angular slice ‖R(z)‖ is bounded below (the pivot entry
   |z_pivot|=1 after blow-up), so frobSq(R(z)·S) ≥ c₀·frobSq(S)-ish — is the angular integral then just
   ∫_S frobSq(S)^{−c'} over the box, finite for c' < (r·p)/2 (always true in cap-B since r²≤... )? Which
   route is both TRUE at the sharp threshold c'<r²/2 and Lean-tractable?
2. Is there a subtlety: does frobSq(R(z)·S) ≥ c₀·frobSq(S) actually hold on the blow-up chart (R(z) has a
   unit pivot entry but could still annihilate S if S is in its kernel)? If not, what is the correct lower
   bound that survives integration?
3. Does directMorse even NEED a separate angular argument, or can it reuse radial_loss_chart_lt_top (item 3)
   with hSfin supplied by a SIMPLER sub-lemma (e.g. ∫_R frobSq(R·S)^{−c'} < ⊤ for FIXED S≠0 by a
   Δ=0-blow-up on R), summed/Tonelli'd over S? Give the cleanest decomposition.
</task>

<output_contract>
Terse. Sections:
1. The recommended DIRECT angular/joint bound for cap-B (the exact inequality chain), reusing items 1–3,
   TRUE at the sharp c'<r²/2. Name the one load-bearing lower bound on frobSq(R·S).
2. The kernel-annihilation subtlety (Q2): does the naive frobSq(R·S) ≥ c₀·frobSq(S) hold? If not, the fix.
3. Whether directMorse = radial cover + item-3 with a simple hSfin, or needs genuinely new angular content.
   Give the lemma decomposition (3–5 named sub-lemmas) + a risk tag [LOW/MED/HIGH] each.
4. The ONE thing most likely to bite in the Lean build of this branch.
</output_contract>

<grounding_rules>
Reviewing a DESIGN. Flag INFERENCE vs known Mathlib v4.29 fact. If unsure a lemma exists, say "verify".
Do not write full proofs — give the inequality chain + decomposition. Mark risks [LOW/MED/HIGH].
</grounding_rules>
