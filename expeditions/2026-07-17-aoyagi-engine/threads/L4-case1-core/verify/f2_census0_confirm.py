"""seat-L4D — decorrelated confirm of the F₂ census-0 identity (my (d) cheerful check, owed).
Full-faithful F₂ (do-not-zero-but-absorb): A₀→Q₁A₀Q₂=diag(1,e₂), A₁→A₁Q₁⁻¹ (+γ), input→·Q₂⁻¹.
Product-preserving ⟹ P_cl = P_uncl IDENTICALLY ⟹ ⟨cleared⟩=⟨uncleared⟩ trivially ⟹ bridge PROVABLE, census 0.
Contrast: r4Clear pure-zero (diag literal, no Q₂⁻¹) and the −γ recoord FAIL (L4C rows B/C). (2,2,2,2), pivot (0,0)."""
import sympy as sp
u=lambda l,r,c: sp.Symbol(f'u{l}{r}{c}')
A2=sp.Matrix([[u(2,0,0),u(2,0,1)],[u(2,1,0),u(2,1,1)]])
A1=sp.Matrix([[u(1,0,0),u(1,0,1)],[u(1,1,0),u(1,1,1)]])
b,g=u(0,0,1),u(0,1,0); e2=u(0,1,1)-g*b
A0=sp.Matrix([[1,b],[g,u(0,1,1)]])                 # RAW A₀
Q1=sp.Matrix([[1,0],[-g,1]]); Q2=sp.Matrix([[1,-b],[0,1]])
Q1inv=Q1.inv(); Q2inv=Q2.inv()
Puncl=sp.expand(A2*A1*A0)
# Full-faithful F₂: A₁·Q₁⁻¹ (+γ recoord) · (Q₁·A₀·Q₂=diag(1,e₂)) · Q₂⁻¹ input
blockcl=sp.expand(Q1*A0*Q2)
Pcl_F2=sp.expand(A2*(A1*Q1inv)*blockcl*Q2inv)
print('block clear Q₁·A₀·Q₂ =', blockcl.tolist(), ' (= diag(1,e₂), e₂=',sp.expand(e2),')')
print('F₂ full-faithful: P_cl == P_uncl ?', sp.expand(Pcl_F2-Puncl)==sp.zeros(2,2))
assert sp.expand(Pcl_F2-Puncl)==sp.zeros(2,2), 'F₂ must preserve the product identically'
# contrast (B): pure-zero r4Clear (literal diag, no Q₂⁻¹, −γ recoord) — expect ≠
A1_mg=A1.copy(); A1_mg[0,0]=A1[0,0]-g*A1[0,1]; A1_mg[1,0]=A1[1,0]-g*A1[1,1]  # −γ recoord
Pcl_pz=sp.expand(A2*A1_mg*sp.Matrix([[1,0],[0,e2]]))   # literal diag, no Q₂⁻¹
print('pure-zero (−γ, no Q₂⁻¹): P_cl == P_uncl ?', sp.expand(Pcl_pz-Puncl)==sp.zeros(2,2), '(expect False)')
print('\nCONFIRMED: F₂ full-faithful preserves the product IDENTICALLY ⟹ ⟨cleared⟩=⟨uncleared⟩ ⟹ StepInv close by')
print('EQUALITY (no ideal-membership, no M-bridge) ⟹ +1 core DISSOLVES, census 0. Pure-zero does NOT (unsound).')
