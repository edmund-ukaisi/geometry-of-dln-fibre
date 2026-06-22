# RECONCILE: does the achiever path have a SINGLE binding divisor with (k,h)=(1, m₀−1), as
# of_mult_and_achiever requires (hh₀: h i₀ j₀ = m₀−1)? Or does codim-m₀ split across several per-node divisors?
print("=== The binding divisor: single (1, m₀−1) vs accumulated across nodes ===")
print("""
of_mult_and_achiever needs ONE divisor j₀ on the achiever path i₀ with h i₀ j₀ = m₀−1 (and k=1), giving
monomialThreshold (d i₀)(k i₀)(h i₀) = ⨅_j axisRatio(h i₀ j)(k i₀ j) ≤ axisRatio(m₀−1, 1) = m₀/2, AND
threshold_ge gives ≥ m₀/2, so the path's threshold = m₀/2 exactly.

KEY: monomialThreshold = ⨅_j axisRatio over the path's divisors. So the path's threshold = ½·(min codim
over its divisors). For the path's threshold to EQUAL ½·m₀, the path's MINIMUM-codim divisor must be the
codim-m₀ binding center. Two cases reconcile:

(a) r1-design §2 BINDING-DIVISOR form: the binding branch resolves the T* stratum in ONE codim-m₀ center
    blow-up (after the regular pivot split exposes the residual block whose vanishing IS S(T*)). That
    single blow-up's divisor has (k,h)=(1, m₀−1) directly — the (2,2,2) ρ-chart: h=2=Mval−1=m₀−1. ✓
    This is the form of_mult_and_achiever wants: ONE j₀ with h=m₀−1.

(b) INCREMENTAL (per-factor) form: if the path blows up per-factor (codim accumulates as several divisors
    h_1,...,h_p with Σ(h_i+1) related to m₀), the MINIMUM axisRatio over them is what counts. The path's
    threshold = ½·min_i(h_i+1). For this to = ½·m₀, the BINDING (smallest-ratio) divisor must have
    (h+1) = m₀, i.e. h = m₀−1 — so there's still a SINGLE binding divisor with h=m₀−1 (the others have
    larger ratio, don't bind). So even incrementally, the achiever's BINDING divisor is (1, m₀−1).

⟹ EITHER WAY of_mult_and_achiever's witness (i₀, j₀) is: i₀ = the path through T*'s binding center,
   j₀ = its codim-m₀ binding divisor, (k i₀ j₀, h i₀ j₀) = (1, m₀−1). The achiever cert provides exactly
   this. (The (2,2,2) anchor confirms form (a): the ρ binding divisor (1,2), m₀=3.)
""")
print("CONCLUSION: the achiever cert hands fm3: (i₀ = the binding path to T*, j₀ = its codim-m₀ binding")
print("divisor) with k i₀ j₀=1 (regular sequence/multilinearity), h i₀ j₀ = m₀−1 (codim-m₀ blow-up Jacobian).")
print("This is exactly of_mult_and_achiever's (i₀,j₀,hk₀,hh₀). The value lands: threshold = m₀/2 = ½·m₀ = lambdaCore.")
