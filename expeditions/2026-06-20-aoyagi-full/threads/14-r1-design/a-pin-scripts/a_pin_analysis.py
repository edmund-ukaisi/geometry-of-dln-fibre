import sympy as sp
# PIN prereq-(a): is the homogeneous-residual split at an ARBITRARY fibre point v obtained from
# #111's ORIGIN chart (schur_chart_exists @ 0), or is it a SEPARATE construction?
#
# SETUP. D1>= compares rlctAt(dlnLoss B) at deepest vs at an arbitrary fibre point v (prod v = B).
# The loss germ at v: F(v + w) = ||prod(v+w) - B||^2. We want: F(v+w) = [regular block] + [homogeneous
# residual core ||C'||^2] in suitable local coords, so Aoyagi Thm2 (+ rlctAt_mono) applies.
#
# #111's schur_chart_exists: resolves the CORE ||prod(C)||^2 at the ORIGIN 0 in Params(M) (reduced
# widths M = H - r). It's the resolution of the deepest point's core. It is NOT a priori about a germ
# at an arbitrary v.
#
# THE TWO CANDIDATE ANSWERS:
# (A) #111-instantiated: there's a GAUGE map g_v (analytic change of coords) carrying the germ at v to
#     [regular] + [core germ at ITS origin], and #111's origin-chart resolves that core. Then (a) is
#     schur_chart_exists applied AT the translated origin = purely #111-gated.
# (B) SEPARATE: the arbitrary-v split needs its own existence lemma (the regular/core SPLIT at v),
#     distinct from #111's origin resolution.
#
# KEY STRUCTURAL FACT to determine which: the fibre {prod = B} is a SINGLE GL-gauge orbit's union of
# strata. At an arbitrary fibre point v, the loss germ is NOT homogeneous (linear leading part, from #112).
# The split into [regular] + [homogeneous core] is a LOCAL NORMAL FORM at v. Question: does this normal
# form come from #111 (origin core resolution) or is it a prior, separate step?
#
# ANSWER via the layering (from #112's D1 decomposition):
# D1>= = [step 1: gauge/normal-form c-o-v at v: germ -> regular block + homogeneous residual core]
#        [step 2: Aoyagi Thm2 (homogeneity scaling + rlctAt_mono) on the residual core]
#        [step 3: deepest-in-closure (cone)]
# STEP 1 IS THE (a) PREREQ. It is the SPLIT at v. #111 (schur_chart_exists @ origin) is the RESOLUTION
# of the core ||prod(C)||^2 -- which is used DOWNSTREAM (for the VALUE), NOT for the split at v.
# But D1>= does NOT need the core's VALUE (it's value-free, #112). So D1>= does NOT need #111 at all
# for the comparison -- it needs the SPLIT (step 1), then Aoyagi Thm2 on the (unresolved) core.
print("=== Re-examining: does D1>= even NEED #111's chart, or just the SPLIT at v? ===")
print("From #112: D1>= is VALUE-FREE. It uses Aoyagi Thm2 (homogeneity scaling + rlctAt_mono) on the")
print("residual CORE -- it does NOT resolve the core (no monomialThreshold, no value). So D1>= needs")
print("the SPLIT at v [regular + homogeneous core], NOT the core's RESOLUTION (#111).")
print()
print("So the (a) prereq = the SPLIT at v. Is THAT #111's schur_chart_exists, or separate?")
print("schur_chart_exists (the #111 G3.2 chart) gives, in a pivot chart at the ORIGIN:")
print("  ||prod(C)||^2 = monomial * ||C'||^2 (the recursion-closing reduced-chain identity).")
print("That is the SCHUR REDUCTION, a statement about the CORE at its origin -- the strict-transform.")
print("The (a) SPLIT at v is DIFFERENT: it's ||prod(v+w) - B||^2 = [reg quadratic] + [homog core],")
print("a Morse/constant-rank split at v. They are NOT the same lemma.")
