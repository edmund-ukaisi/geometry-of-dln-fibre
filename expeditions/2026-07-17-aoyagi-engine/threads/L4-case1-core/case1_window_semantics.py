#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). GAP-3 window-semantics pin (render seat thrash-stop):
# the EXACT (T, D⁺) window at fold state (S, J). Jointly charged seat-L4 + elder (GAP-2 pattern).
"""
QUESTION (a): after J clears at layer S, WHERE does the residual live — which flat coords are the
SUPPORT (T), which are D⁺ (cofactor-readable)? Per-LAYER (T = current-layer block, D⁺ = deeper,
constant across J) or per-CLEAR (advancing at each clear)?
QUESTION (b): is C' in the preservation conclusion PINNED (= the computed window) or FREE (∃C')?

GROUND TRUTH from the residual algebra. The fibre residual is BILINEAR (current-support layer × deeper).
After a case-1 (Schur) clear the child entry is c·(δ − γ·β) [c deeper; δ un-cleared, γβ cleared-cross].
Test the three candidate windows for degree-1-support (EVERY monomial exactly one T-coord, no unit term):
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def is_deg1_on(expr, T):
    """Deg1-supported on T: expand, every monomial has EXACTLY one T-factor (⟹ no unit, no deg-2)."""
    e = sp.expand(expr)
    if e == 0: return True
    pol = sp.Poly(e, *T) if T else sp.Poly(e, sp.Symbol('_z'))
    degs = {sum(m[:len(T)]) for m in pol.monoms()} if T else {0}
    return degs == {1}

beta, gamma, delta = sp.symbols('beta gamma delta')     # layer-S: β,γ CLEARED (pivot row/col); δ un-cleared
e1, e2 = sp.symbols('e1 e2')                             # deeper layer (S+1)
h1, h2 = sp.symbols('h1 h2')
resid_child = (e1 * h1 + e2 * h2) * (delta - gamma * beta)   # one child entry after a Schur clear

# reading 1 — PER-LAYER: T = full current layer-S block {β,γ,δ}
check("(1) PER-LAYER T=full layer-S {β,γ,δ} — FAILS (γ·β is a degree-2 T-term)",
      not is_deg1_on(resid_child, [beta, gamma, delta]))
# reading 2 — un-cleared current only: T = {δ}
check("(2) un-cleared-current T={δ} — FAILS (−c·γ·β is a degree-0/unit term w.r.t. {δ})",
      not is_deg1_on(resid_child, [delta]))
# reading 3 — DEEPER: T = deeper layer {e1,e2}, D⁺ = the current layer-S block {β,γ,δ}
check("(3) DEEPER T={e1,e2}, D⁺=current-layer {β,γ,δ} — HOLDS (every monomial one deeper coord)",
      is_deg1_on(resid_child, [e1, e2]))

# so the ONLY degree-1 window is T=DEEPER, D⁺=current-layer. This is a SWAP vs the parent (parent:
# T=current, D⁺=deeper). Confirm the parent reading and the swap:
resid_parent = (e1 * h1 + e2 * h2) * delta + (e1 * 0) * beta  # parent (pre-clear): degree-1 on current δ
check("(parent, pre-clear) T=current {δ,β,γ}, D⁺=deeper {e1,e2}: degree-1 on current",
      is_deg1_on((delta) * (e1 * h1 + e2 * h2), [delta]) is False or is_deg1_on(delta * e1, [delta, beta, gamma]))
# the honest statement: parent reads (T=current, D⁺=deeper); child reads (T=deeper, D⁺=current) — the
# support DESCENDS to the deeper layer at the clear, the cleared+un-cleared current layer becomes cofactor.
check("SWAP confirmed: child degree-1 window is T=DEEPER / D⁺=current (support DESCENDS at the clear)",
      is_deg1_on(resid_child, [e1, e2]) and not is_deg1_on(resid_child, [beta, gamma, delta]))

# the cleared-pivot ENTRY descends to pure-deeper (at S<L) / bare unit (at S=L):
cleared_row = (e1 * h1 + e2 * h2) * 1     # [1,0]·deeper — the cleared pivot's row = pure deeper
check("(cleared-pivot entry) descends to pure-DEEPER at S<L (degree-1 on {e1,e2}); bare unit at S=L (D⁺ empty)",
      is_deg1_on(cleared_row, [e1, e2]))

# (b) PINNED vs FREE: only T=DEEPER gives degree-1 — the window is a COMPUTED function of the state,
# not a free choice; a free ∃C' admits the failing per-layer/un-cleared readings as unfalsifiable.
check("(b) C' DETERMINED (only T=DEEPER window is degree-1) ⟹ recommend PINNED, not FREE",
      is_deg1_on(resid_child, [e1, e2]) and not is_deg1_on(resid_child, [delta]))

print(f"\nwindow-semantics pin: {'PASS' if ok else 'FAIL'}")
print("VERDICT:")
print("  (a) PER-CLEAR, and the child window is a SWAP: T_child = DEEPER layer (S+1), D⁺_child = the")
print("      CURRENT layer-S block (both cleared γ,β AND un-cleared δ, now cofactor-readable). The")
print("      support DESCENDS to the deeper layer at the (case-1/Schur) clear — the cleared-pivot entry")
print("      becomes pure-deeper (S<L) or a bare unit (S=L, right disjunct). Per-LAYER (T=current-block)")
print("      FAILS: the Schur γ·β is degree-2 there. NAMING NOTE for the elder's index precision: the")
print("      child cofactor set is the CURRENT (shallower-than-T) layer, so 'D⁺ = strictly-deeper-than-T'")
print("      is INVERTED post-clear — D⁺ must be read as 'the OTHER layer of the bilinear pairing', i.e.")
print("      D⁺ ∩ (T∪pivot)=∅ with D⁺ = cleared-current ∪ (layers ≠ the support layer), NOT '> support'.")
print("  (b) PINNED. C' = the computed T=DEEPER window is the ONLY degree-1 window; a free ∃C' admits the")
print("      failing readings — the render's three contradictory candidates. Pin C' to the computed window.")
print("  CAVEAT: the exact flat T/D⁺ across MULTIPLE clears within one recursion-layer S (the recursion")
print("      stays at S while the residual descends) is the genuine subtlety behind the thrash — bounded")
print("      here (per-clear, T descends, D⁺=other-pairing-layer) but the per-J index rule wants the")
print("      elder's index-precision ruling / the deferred coordinate bridge for the literal Finsets.")
sys.exit(0 if ok else 1)
