"""seat-L4D — §8(m) at the SOURCE: the inter-edge u₀₀₁ enters via the UNSCOPED branch-(ii) sum, and the
frozen §8(i) DEF-EDIT-3(b) scope `cleared ≤ i` drops it. Grounds why pnp's u₀₀₁² is NOT a re-open — it is
the unscoped current formula; the render is scoped.

Setup (2,2,2,2), layer 0, two consecutive layer-0 clears:
  ed1 = pivot (a₁,b₁)=(0,0); after ed1, cleared = 1 (index 0 is cleared).
  ed2 = second layer-0 clear, pivot col b₂ = 1; s.cleared = 1 at ed2.
ed2's branch-(ii) recoord image on a layer-1 coord (row) = Σ_i readEntry(0, i, b₂=1)·readEntry(1, row, i),
i over the layer index, i ≠ col. readEntry(0, i, 1) is the layer-0 col-1 entry at row i:
  i=0 → readEntry(0,0,1) = u001  (ed1's pivot ROW 0 — the entry ed1's clear zeroes; UNCLEARED here
        because ed1 is applied OUTERMOST/after ed2 in foldResid∘pathMap).
  i=1 → readEntry(0,1,1) = u011.
The current (baked) formula sums ALL i≠col (UNSCOPED) ⟹ carries the i=0 term u001·A1[row,0] ⟹ downstream
square. §8(m) scopes to `cleared ≤ i` (i ≥ 1) ⟹ the i=0 cleared-row term drops ⟹ no u001 from this source.
honest_clear_2222.py (ran exit 0) confirms the faithful residual carries u001 only as a degree-1
COEFFICIENT (s·center-coord), never squared — matching the scoped semantics (u001 lives in the clear/
input-change U⁻¹, not re-summed into the deeper recoord).
"""
import sympy as sp
u = lambda l, r, c: sp.Symbol(f'u{l}{r}{c}')
A1 = lambda row, i: sp.Symbol(f'A1_{row}{i}')   # layer-1 entries (deeper factor being recoorded)
b2, cleared, col = 1, 1, 1                        # ed2 pivot col; cleared frontier after ed1; excluded col
Drange = 2

def recoord_image(row, scoped):
    lo = cleared if scoped else 0                 # §8(m): scoped sum starts at `cleared`
    return sp.expand(sum(
        (u(0, i, b2) * A1(row, i)) for i in range(lo, Drange) if i != col))

for row in range(Drange):
    un = recoord_image(row, scoped=False)
    sc = recoord_image(row, scoped=True)
    print(f'row {row}: UNSCOPED = {un}   |   SCOPED(cleared≤i) = {sc}')

# UNSCOPED carries the i=0 term with coefficient u001 (ed1's uncleared pivot-row entry).
assert any(u(0, 0, b2) in recoord_image(r, scoped=False).free_symbols for r in range(Drange)), \
    'unscoped sum must read u001 (the i=0 cleared-row term)'
# SCOPED drops it: u001 appears in NO scoped recoord image.
assert all(u(0, 0, b2) not in recoord_image(r, scoped=True).free_symbols for r in range(Drange)), \
    'scoped sum (cleared≤i) must drop the u001 source term'
print('\n§8(m) CONFIRMED at the source: UNSCOPED branch-(ii) reads u001 (ed1 pivot-row, i=0=cleared row); '
      'the `cleared ≤ i` scope drops it ⟹ no inter-edge u001 from the recoord. pnp tested the UNSCOPED '
      'current formula — re-run on the SCOPED render. NOT a re-open; the frozen §8(i) already carries the fix.')
