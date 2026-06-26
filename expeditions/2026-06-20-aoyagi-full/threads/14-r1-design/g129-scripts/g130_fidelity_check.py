# Pin-down of the TWO fidelity gaps, by tracing the Lean transport chain symbolically (not numerics —
# this is about WHICH POINT the rlct is evaluated at, and WHAT the unit-strip demands).
print("=== (i) χ 0 = 0  — does the transport need the chart to FIX the deepest point? ===")
print("""
schur_recursion_step_sound concludes:
   rlctAtOn (dlnLoss M 0) (chart (0,0)) = nReg/2 + rlctAtOn (G²) 0
The base point of the TRANSPORTED rlct is `chart (0,0)` (from rlctAtOn_comp_homeomorph:
   rlctAtOn (F∘e) w0 = rlctAtOn F (e w0),  here w0=(0,0) ⟹ e w0 = chart (0,0)).

The RLCT programme is anchored at the DEEPEST point w* (= deepestPoint H r B), the singular zero of
the loss — L2/D1/R1 all compute rlctAt … w*. For schur_recursion_step_sound's output to BE the rlct
at the deepest point, we NEED  chart (0,0) = w*  (the deepest point), equivalently the chart's source
origin maps to the deepest point.

In the flat per-node coords w* IS the origin 0 (post-blow-up the deepest point is the chart origin),
so the obligation is exactly  χ (0,0) = 0  (= the flat deepest point).
WITHOUT it: `chart (0,0)` is some OTHER point; rlctAtOn (dlnLoss M 0) (chart(0,0)) is the rlct at the
WRONG point. Since rlctAt VARIES over the fibre (Skeleton L2 docstring: "the local RLCT varies over
the fibre, equalling the closed form at the deepest point"), the value at chart(0,0)≠w* is in general
NOT the Aoyagi λ. => the split would compute a sound equation about the wrong point — USELESS for the
cover, which must chain rlct AT THE DEEPEST POINT.  ⟹  χ 0 = 0 is REQUIRED for downstream soundness.
""")
print("=== (ii) u ≠ 0 near 0 — does the unit-strip need u bounded away from zero? ===")
print("""
schur_recursion_step_sound's hu hypothesis:  ∃ U ∈ 𝓝 (0,0), ∀ w∈U, a ≤ |u w| ∧ |u w| ≤ b,  a>0.
This is consumed by rlctAtOn_unit_invariant_aux, whose forward/backward legs use:
   |u|^{−c'} ≤ a^{−c'}   (needs a>0: lower bound away from 0)   [strip u from u·F]
   |u|^{ c'} ≤ b^{ c'}   (needs b<∞: upper bound)               [restore]
If u is NOT bounded BELOW by a>0 (i.e. u → 0 somewhere in every nbhd of 0, or u(0)=0), the bound
a^{−c'} is vacuous (a=0 ⟹ a^{−c'}=∞), the Integrable.bdd_mul step FAILS, and the unit-strip is FALSE:
a factor that VANISHES changes the rlct (it is a genuine zero of the integrand, not a unit).
=> the factor u in `flatCore∘χ = u·(reg+core)` must be a GENUINE UNIT: bounded in [a,b], a>0, near 0.
   `u ≠ 0 near 0` (germ-nonvanishing + locally bounded) is REQUIRED. Measurability alone (umeas) is
   NOT enough — it does not prevent u(0)=0 or u→0.
""")
print("=== Cross-check against #129: the squeeze verdict makes BOTH pins MORE acute ===")
print("""
#129 showed the per-node factor is NOT a clean single-unit u·(ΣE²+G²); the sound route is the SQUEEZE
c₁Φ ≤ F ≤ c₂Φ. In the squeeze packaging, the 'unit' role is played by the constants c₁,c₂ (>0) — these
are bounded-away-from-0 by construction (a>0 with a=c₁). So (ii) is automatically met IF the datum
records the squeeze constants as a genuine [c₁,c₂], c₁>0. If instead the datum keeps the abstract
`u` with only `Measurable u`, (ii) is UNMET. And (i) χ0=0 is needed identically in the squeeze route:
the squeeze compares F and Φ AT THE SAME POINT near the deepest point — that point must be the deepest
point, i.e. the chart/comparison is anchored at χ0 = w* = 0.
""")
