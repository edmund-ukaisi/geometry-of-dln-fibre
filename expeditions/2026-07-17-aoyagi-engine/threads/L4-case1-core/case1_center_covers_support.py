#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Conjunct-1 (divisibility) SPECIFY check: does the δ=1
# divisibility need the blow-up center ed.center to COVER the residual support, and does hcenter (⊆) supply it?
"""
Conjunct-1 needs: foldResid_p(stepMap u) = u_pivot · foldResid(child)  (so foldB gains u_pivot uniformly).
stepMap = blockBlowupMap ed.center ed.pivot ∘ shear. blockBlowupMap: pivot ↦ u_pivot; center∖pivot ↦
u_pivot·(·); SPECTATOR (∉ ed.center) ↦ (·) unchanged. So a residual term c_i·u_i gains u_pivot IFF
i ∈ ed.center. hinv gives the residual degree-1 on supportAt(parent); hcenter gives ed.center ⊆
supportAt(parent). CONCERN: if ed.center ⊊ supportAt(parent), the support-coords in
supportAt(parent)∖ed.center are SPECTATORS → their terms do NOT gain u_pivot → divisibility FAILS.
Test: residual = c_a·u_a + c_b·u_b (support {a,b}); blow-up center = {pivot,a} (⊊ support, missing b).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

up, a, b = sp.symbols('u_pivot u_a u_b')     # pivot, support coord a (in center), support coord b (NOT in center)
ca, cb = sp.symbols('c_a c_b')               # coefficients (deeper; treat as symbols)
resid = ca * a + cb * b                       # degree-1 on support {a,b}

# blow-up over center = {pivot, a} (b is a SPECTATOR); shear = id for simplicity (isolates the cover issue)
def stepmap(coord):
    if coord == up: return up            # pivot ↦ u_pivot
    if coord == a:  return up * a        # center coord ↦ u_pivot·(·)
    return coord                          # spectator (b) ↦ unchanged
def qm(coord):                            # blockBlowupCoordQuot pivot: pivot↦1 else (·)
    return sp.Integer(1) if coord == up else coord

resid_step = sp.expand(resid.subs({a: stepmap(a), b: stepmap(b)}, simultaneous=True))   # resid(stepMap u)
child = sp.expand(resid.subs({a: qm(a), b: qm(b)}, simultaneous=True))                  # foldResid(child)=resid(qm)
lhs_minus = sp.expand(resid_step - up * child)
print(f"    resid(stepMap) = {resid_step}")
print(f"    u_pivot·child  = {sp.expand(up*child)}")
print(f"    difference     = {lhs_minus}")

check("(center ⊊ support): crux FAILS — resid(stepMap) ≠ u_pivot·child (the b-term c_b·u_b lacks u_pivot)",
      lhs_minus != 0)
check("the failing residue is exactly the SPECTATOR support term c_b·u_b (× (1−u_pivot))",
      sp.expand(lhs_minus - (cb * b - up * cb * b)) == 0)

# CONTRAST: center = {pivot, a, b} (COVERS support) → crux holds
def stepmap2(coord):
    if coord == up: return up
    if coord in (a, b): return up * coord
    return coord
resid_step2 = sp.expand(resid.subs({a: stepmap2(a), b: stepmap2(b)}, simultaneous=True))
child2 = sp.expand(resid.subs({a: qm(a), b: qm(b)}, simultaneous=True))
check("(center = support {a,b}): crux HOLDS — resid(stepMap) = u_pivot·child (both terms gain u_pivot)",
      sp.expand(resid_step2 - up * child2) == 0)

print(f"\ncenter-covers-support check: {'PASS (concern confirmed)' if ok else 'FAIL'}")
print("VERDICT: conjunct-1 divisibility needs residual-support ⊆ ed.center (blow-up covers the support).")
print("  hinv gives residual degree-1 on supportAt(parent); hcenter gives ed.center ⊆ supportAt(parent)")
print("  (the OPPOSITE inclusion). A free ed with ed.center ⊊ supportAt(parent) leaves spectator support")
print("  coords whose terms do NOT gain u_pivot ⟹ divisibility FAILS. The construction has ed.center =")
print("  the full carve block = supportAt(parent), so it's fine THERE — but the free-ed leaf as stated")
print("  admits ed.center ⊊ supportAt(parent). Need ed.center ⊇ supportAt(parent) (⟹ = with hcenter),")
print("  i.e. hcenter should be an EQUALITY (or a second ⊇ clause), not just ⊆.")
sys.exit(0 if ok else 1)
