<task>
Adjudicate whether a CRUDE coercivity bound closes a matrix-integral finiteness at the target exponent, or
undershoots and needs a SHARPER anisotropic estimate. Exact algebra; I withhold my lean.
</task>

<setup>
Inner slice (fixed deep data θ): g_cc(x) = ‖L_θ x‖², x ∈ ℝ^7 (a 7-dim corner; = 2×2 corank Γ + 1×3
boundary v). L_θ injective on the good chart (its 7 singular values s_1≥…≥s_7>0). A BANKED endpoint proves
∫_{[-1,1]^7} g_cc^{-c'} < ⊤ for c'<7/2 (full 7-dim degree-2 positive-definite corner). We must integrate the
inner value over the DEEP DATA θ (a factor box), where L_θ degenerates (s_7 = σ_min(L_θ) → 0).

Two ways to bound the inner value for the outer integration:
- CRUDE (banked `corner_block_lintegral_le`): inner ≤ a(θ)^{-c'} = σ_min(L_θ)^{-2c'}  (a = sphere-min of
  g_cc = σ_min²). This is the WORST-direction bound (g_cc ≥ σ_min²‖x‖²).
- SHARP: the TRUE inner value as ONE direction collapses (σ_7=σ→0, s_1..s_6 = O(1)).

A banked tail lemma (ProductTube) integrates σ_min(tail)^{-α} over the factor box for α<1 (the binding
threshold α<1 ⟺ c'<7/2 for this tail). σ_min(L_θ) relates to σ_min(tail) up to a bounded factor on the
good chart.
</setup>

<questions>
Q1 (the sharp inner-value exponent). Compute ∫_{[-1,1]^7}(Σ_{j=1}^6 x_j² + σ² x_7²)^{-c'} dx as σ→0
   (6 stable directions weight 1, one collapse weight σ). Integrate the 6-dim stable block first, then the
   collapse. Give the exact blow-up σ^{-β}. Is β = 2c'-6 (codims-add: only the collapse charges, the 6
   stable are bounded) or β = 2c' (the crude worst-direction)?
Q2 (crude vs sharp threshold over the tail). The outer integral over θ, via ProductTube (integrates
   σ_min(tail)^{-α}, α<1): CRUDE feeds α=2c' (from σ_min^{-2c'}); SHARP feeds α=2c'-6 (from σ_min^{-(2c'-6)}).
   For which c' does each close (α<1)? Crude: 2c'<1 ⟹ c'<? Sharp: 2c'-6<1 ⟹ c'<? Which reaches 7/2?
Q3 (verdict + what the sharp estimate is). Does the crude corner_block_lintegral_le bound UNDERSHOOT (fails
   to reach 7/2), requiring the SHARPER anisotropic estimate σ_min^{-(2c'-6)}? Is that sharp estimate the
   per-singular-value / two-block-radial structure (stable block bounded below by κ, only the collapsing
   direction charges — the "front-first majorant" α'=2c'-6), i.e. does the abandoned front-majorant
   twoBlock_radial analysis become the REUSABLE sharp inner estimate here? And on the DEEPER stratum (two
   directions collapse), does the same codims-add recurse (β=2c'-5, integrated against the higher-codim
   tube), i.e. is the deeper rung a corank recursion?
</questions>

<output_contract>
For Q1–Q3: exact algebra + "FACT" vs "INFERENCE". End: crude closes at 7/2 (simpler) OR sharper anisotropic
needed (+ what it is + which stratum binds). Keep the fixed-θ inner finiteness (7/2, banked) separate from
the outer-integration coarseness.
</output_contract>

<grounding_rules>
Exact radial/Beta scaling. The crude bound over-charges the 6 stable directions as if collapsing. Keep
"the bound's threshold" separate from "the true integral's threshold".
