import sympy as sp
# Check the (2,2,2) ANCHOR: does its deepest split give a clean ΣEᵢ²+G²? The anchor's resolvedForm
# (Case222Resolution.lean) = E²+F0²+(qE+δG)²+(qF0+δH)². Is THAT a clean nReg-squares + core²?
E,F0,delta,q,G,H = sp.symbols('E F0 delta q G H', real=True)
resolvedForm = E**2 + F0**2 + (q*E+delta*G)**2 + (q*F0+delta*H)**2
print("=== (2,2,2) anchor resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)² ===")
print("  Is this a clean Σ(nReg squares) + (core)²? NO — it's 4 squares but they're COUPLED via q,δ.")
print("  The anchor does NOT produce ΣEᵢ²+G²; it produces this COUPLED resolved form, which is THEN")
print("  BLOWN UP (step2: blow up the vertex {E=F0=δ=0}) — the split into regular+core happens at the")
print("  LEAF level (post-blow-up), NOT at the deepest-split level.")
print()
print("=== IMPLICATION for a114e07e (the real answer to the seam gap) ===")
print("a114e07e's expected target 'S1.5 needs literal ΣEᵢ²+G²' is the WRONG form for the L2 deepest split.")
print("The (2,2,2) anchor (the GREEN reference) does NOT split into ΣEᵢ²+G² at the deepest point — the")
print("regular/core separation is NOT a clean sum-of-squares decomposition reachable by the deepest χ.")
print()
print("So the L2 product_reduction split is NOT 'F∘χ = ΣEᵢ²+G² then S1.5'. The honest structure:")
print("the regular block (the nReg directions where prod-B is a nondeg quadratic = the IDENTITY-corner")
print("perturbation) DOES separate from the core, but via the SMOOTH-POINT structure, not a SoS split.")
print("Let me pin what L2 ACTUALLY needs: is it the regular block = a nondeg quadratic FORM (Hessian rank")
print("nReg) whose rlct is nReg/2 by smoothBlockND, + the core transverse? That's a Morse-Bott split, which")
print("DOES need a normal-form theorem (the constant-rank issue resurfaces at the SPLIT level!).")
