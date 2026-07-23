"""seat-L4D — the decisive follow-up (provisional; pnp's faithful harness is authoritative): does
branch-(ii)'s A₁ recoord ABSORB the E_J failure remainder γ·(A₂A₁)_{·,1}?

branch-(ii) (canonNormalizationOf, pivot (0,0)): A₁ → A₁' with col-a(=col-0) ± γ·col-1  (γ=u010=A₀[1][0]);
sign = +γ for Q₁⁻¹ (current def), −γ for Q₁ (§8(i)/(m) flip). Test BOTH. Both foldResid branches apply
branch-(ii) (it's the shear) BEFORE r4Clear/blowup, so P_uncl and P_cl BOTH use A₁'.
  uncleared A₀ = [[1,β],[γ,e₂]] ; cleared A₀ = [[1,0],[0,e₂]] (r4Clear zeros β,γ).
KILL/DISSOLVE: uncleared ∈ ⟨cleared⟩ with A₁' → bridge sound (dissolve); still fails → §7.
"""
import sympy as sp
from sympy import groebner, symbols
names = ['u200','u201','u210','u211','u100','u101','u110','u111','u001','u010','u011']
xs = symbols(names)
(u200,u201,u210,u211,u100,u101,u110,u111,u001,u010,u011) = xs
A2 = sp.Matrix([[u200,u201],[u210,u211]])
A1 = sp.Matrix([[u100,u101],[u110,u111]])
b, g = u001, u010
e2 = u011 - g*b
A0u = sp.Matrix([[1,b],[g,e2]]); A0c = sp.Matrix([[1,0],[0,e2]])
for sign, tag in [(+1,'+γ (Q₁⁻¹, current def)'), (-1,'−γ (Q₁, §8(m) flip)')]:
    A1p = A1.copy()
    A1p[0,0] = A1[0,0] + sign*g*A1[0,1]
    A1p[1,0] = A1[1,0] + sign*g*A1[1,1]
    Pu = sp.expand(A2*A1p*A0u); Pc = sp.expand(A2*A1p*A0c)
    gb = groebner([sp.expand(Pc[i,j]) for i in range(2) for j in range(2)], *xs, order='grevlex')
    res = {(i,j): (sp.expand(gb.reduce(sp.expand(Pu[i,j]))[1])==0) for i in range(2) for j in range(2)}
    allok = all(res.values())
    print(f'branch-(ii) sign {tag}: uncleared ∈ ⟨cleared⟩ (with A₁ recoord) = {allok}')
    for (i,j),m in res.items():
        print(f'    P_uncl[{i}][{j}] member = {m}')
    print(f'  ⟹ {"DISSOLVE (branch-ii absorbs the γ-remainder; bridge sound)" if allok else "STILL FAILS (§7 suspect persists)"}')
