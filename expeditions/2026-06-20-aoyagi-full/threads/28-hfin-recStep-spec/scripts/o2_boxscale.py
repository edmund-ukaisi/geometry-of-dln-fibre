import sympy as sp
# The free Sc-box has side up to 4 ([-2,2]); the IH/recursion is naturally stated on side 2 ([-1,1]).
# Does the box side matter for FINITENESS at the threshold? NO: rescale Sc = 2*Sc', Sc' in [-1,1]:
#   ∫_{Sc in [-2,2]} g(Sc) dSc = 2^{(m^2)} ∫_{Sc' in [-1,1]} g(2 Sc') dSc'   (linear rescale, Jac=2^{m^2})
# and g(2Sc') = ∫_{S_bot} frobSq(2 Sc' * S_bot)^{-c'} = 2^{-2c'} ∫_{S_bot} frobSq(Sc'*S_bot)^{-c'}
#   = 2^{-2c'} g(Sc').   So ∫_{[-2,2]} g = 2^{m^2 - 2c'} ∫_{[-1,1]} g(Sc') dSc'.   FINITE iff the
# side-1 box integral is finite -- SAME threshold. The box side is a harmless constant factor.
m, cp = sp.symbols('m cprime', positive=True)
print("∫_{Sc∈[-2,2]^{m²}} g(Sc) dSc = 2^{m² − 2c'} · ∫_{Sc'∈[-1,1]^{m²}} g(Sc') dSc'")
print("  (Sc=2Sc' rescale: Jac=2^{m²}, g(2Sc')=2^{−2c'}g(Sc') by frobSq homogeneity degree 2).")
print("=> the side-4 free-box core is FINITE iff the side-2 (standard) core is. SAME threshold λ_{m,p}.")
print("   The box side is a spectator-independent CONSTANT factor 2^{m²−2c'}. No threshold shift.")
print()
print("ALSO note: S_bot box stays side 2T (it is the free block, untouched by the M22->Sc translation).")
print("And the Sc-box being side 4 (not 2) is harmless: the recursion's IH covers any FIXED box side.")
