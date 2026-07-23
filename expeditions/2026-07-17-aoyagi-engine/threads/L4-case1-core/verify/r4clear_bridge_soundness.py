"""seat-L4D — SOUNDNESS check for arch-C-3's r4Clear bridge BEFORE rendering it as a correctness lemma.

The child StepInv close needs (uncleared ∈ ⟨cleared⟩ with continuous cofactors M):
  foldResid_p(σu) = ∑_{j'} M_{j,j'}(u) · foldResid_p(r4Clear σu),   M polynomial/continuous.
r4Clear = pivot-cross ZERO (β=u001→0, γ=u010→0); branch-(i) already put the interior e₂=u011−u010·u001.
(2,2,2,2), layer-0 pivot (0,0):
  uncleared A₀ = [[1, β],[γ, e₂]]   (cross intact, interior e₂)
  cleared   A₀ = [[1, 0],[0, e₂]]   (cross zeroed)
Residual family = entries of P = A₂·A₁·A₀ (coreGen). r4Clear is NOT invertible (loses β,γ), so M is NOT a
matrix inverse — this is genuine polynomial IDEAL MEMBERSHIP.
KILL-CONDITION: if any uncleared entry ∉ ⟨cleared entries⟩ over ℚ[u], the bridge is FALSE ⟹ r4Clear-in-
foldResid breaks the StepInv chain (§7/soundness obstruction, NOT a bounded frontier).
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
A0_uncl = sp.Matrix([[1, b],[g, e2]])
A0_cl   = sp.Matrix([[1, 0],[0, e2]])
P_uncl = sp.expand(A2*A1*A0_uncl)
P_cl   = sp.expand(A2*A1*A0_cl)

Icl = [sp.expand(P_cl[i,j]) for i in range(2) for j in range(2)]
gb = groebner(Icl, *xs, order='grevlex')
fails = []
print('membership of uncleared entries in ideal ⟨cleared entries⟩ (remainder 0 ⟺ member):')
for i in range(2):
    for j in range(2):
        rem = sp.expand(gb.reduce(sp.expand(P_uncl[i,j]))[1])
        member = (rem == 0)
        print(f'  P_uncl[{i}][{j}] member = {member}' + ('' if member else f'   remainder = {rem}'))
        if not member:
            fails.append(((i,j), rem))
if fails:
    print('\nKILL: naive all-entries bridge FALSE — uncleared NOT ⊆ ⟨cleared⟩.')
else:
    print('\nOK: all-entries bridge sound.')

# --- Refinement: which columns fail? (pnp slot map: col-1 = D_J residual, col-0 = E_J cleared/pivot col) ---
print('\n--- per-column membership ---')
for jcol, tag in [(0, 'col-0 = E_J (pivot/cleared column)'), (1, 'col-1 = D_J (running exceptional e₂)')]:
    print(f'{tag}:')
    for i in range(2):
        rem = sp.expand(gb.reduce(sp.expand(P_uncl[i, jcol]))[1])
        print(f'  P_uncl[{i}][{jcol}] member of ⟨all cleared⟩ = {rem == 0}')

# D_J-only ideal: is the D_J (col-1) uncleared in ⟨D_J cleared entries⟩ (col-1 only)?
Icl_DJ = [sp.expand(P_cl[i, 1]) for i in range(2)]
gb_DJ = groebner(Icl_DJ, *xs, order='grevlex')
print('\nD_J-only: uncleared col-1 ∈ ⟨cleared col-1⟩?')
for i in range(2):
    rem = sp.expand(gb_DJ.reduce(sp.expand(P_uncl[i, 1]))[1])
    print(f'  P_uncl[{i}][1] member of ⟨cleared col-1⟩ = {rem == 0}')

# b-weighted (b = u_pivot = the (0,0,0) coord): does the pivot factor rescue the E_J entries?
bpiv = sp.Symbol('u000'); xs2 = list(xs) + [bpiv]
Icl_b = [sp.expand(bpiv * P_cl[i, j]) for i in range(2) for j in range(2)]
gb_b = groebner(Icl_b, *xs2, order='grevlex')
print('\nb-weighted (b=u_pivot): b·uncleared ∈ ⟨b·cleared⟩ (all entries)?')
for i in range(2):
    for j in range(2):
        rem = sp.expand(gb_b.reduce(sp.expand(bpiv * P_uncl[i, j]))[1])
        print(f'  b·P_uncl[{i}][{j}] member = {rem == 0}')

print('\n' + '='*78)
print('VERDICT: the NAIVE bridge (uncleared ∈ ⟨cleared⟩, all entries) is FALSE — the E_J (col-0)')
print('entries fail, remainder γ·(A₂A₁)_{·,1} = u010·(deeper 2nd col), NOT rescued by the b-factor.')
print('CAVEAT (load-bearing): this model uses RAW A₁ — it does NOT apply branch-(ii)\'s Q₁ recoord')
print('(A₁ → A₁·Q₁, col-0 ∓ γ·col-1), which is precisely the γ/pivot-COLUMN handler. The failing')
print('remainder is a γ·(2nd col) term, so branch-(ii) PLAUSIBLY absorbs it. ⟹ SUSPECT, not a')
print('confirmed kill: the definitive check is uncleared ∈ ⟨cleared⟩ on the EXACT composition WITH')
print('branch-(ii)\'s A₁ recoord (+ the b-ledger), pnp\'s faithful-harness lane. If it FAILS there too')
print('⟹ pure-zero r4Clear breaks the StepInv ideal (sound R4 needs the Q₂⁻¹ neighbor-absorption =')
print('the §7 fold-touch); if branch-(ii) absorbs the γ-side ⟹ the bridge holds, legit +1 frontier.')
