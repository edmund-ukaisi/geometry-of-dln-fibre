import sympy as sp
# Characterize the elementary route precisely: is the (a)-split a TRIANGULAR unit-pivot elimination
# (elementary, Mathlib-light) rather than the full constant-rank theorem?
#
# The structure: at v, the q regular generators have linear parts with a UNIT pivot each. Solving them
# is GAUSSIAN ELIMINATION on the linear parts, with the nonlinear coupling handled by the unit pivot
# (each solved variable's higher-order dependence has a unit denominator). This is:
#   - For a SINGLE generator g = u + h.o.(includes the solved var w with coeff -> unit): w = solve, an
#     analytic implicit function with a UNIT linear coefficient = Mathlib's analytic implicit function
#     for a 1-variable unit-derivative map (MUCH lighter than the general constant-rank theorem).
#   - Iterated triangularly over the q generators (Gaussian elimination order).
print("=== What the elementary route actually needs (vs the general constant-rank theorem) ===")
print("The (a)-split = a TRIANGULAR sequence of q one-variable analytic implicit solves, each with a")
print("UNIT linear coefficient (pivot). NOT the general constant-rank theorem (which handles arbitrary")
print("rank, non-triangular, needs the full IFT + rank-constancy on a nbhd).")
print()
print("What's needed in Lean:")
print(" (1) the gauge to expose unit pivots in the linear parts = block_elimination (#5, DONE) +")
print("     explicit row/col reduction (the det-1 Schur, the #121 straightening, already designed).")
print(" (2) a 1-variable analytic implicit-function / inverse for a unit-derivative analytic map.")
print("     THIS is lighter than constant-rank. Does Mathlib have it? It has HasFDerivAt + the inverse")
print("     function theorem for maps with invertible fderiv (ContDiff / analytic). The 1-var unit-deriv")
print("     case is the cleanest instance.")
print()
print("KEY DISTINCTION: a114e07e's 'constant-rank theorem' is the GENERAL Morse/rank-constancy result.")
print("The DLN family needs only the TRIANGULAR-unit-pivot version (Gaussian elimination + 1-var unit")
print("implicit solves), because the chain structure + the gauge give an EXPLICIT pivot order. That's")
print("the elementary family-specific route. Whether Mathlib's inverse-function-theorem suffices for the")
print("triangular version (vs needing the full constant-rank) is the precise question for a114e07e/Codex.")
print()
# Verify the triangular structure holds for the chain: the generators (prod entries) at v, after the
# gauge, have a triangular unit-pivot linear structure. This follows from the rank-r block-normal form:
# the regular block is the rank-r IDENTITY corner, whose linear perturbation is the identity (unit pivots
# on the diagonal) -- triangular by construction. The residual core has NO linear part (homogeneous).
print("The chain structure GUARANTEES the triangular unit-pivot form: after block_elimination, the")
print("regular block is the rank-r IDENTITY corner; its linear perturbation has IDENTITY (unit diagonal)")
print("linear part = triangular unit pivots. The core has no linear part. So the split = solve the")
print("identity-corner block (trivial unit pivots) + leave the homogeneous core. ELEMENTARY.")
