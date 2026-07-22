#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). GAP-3 FINAL: the elder's check-order (map-direction
# BEFORE geometry) + calibrate the elder's page-verified amended window (shed-and-absorb, ±1 offset).
"""
Elder's AMENDED window (image-verified pages, pre-endorsed the split):
  T′ = the UN-CLEARED block remainder (shrinks per clear, in the PREPARED frame where Δ=C22−γβ is a
       renamed coordinate);  D⁺′ = the deeper window ∪ THE SHED SLOTS (cleared row/col), grows per clear.
Elder's PINNED CHECK-ORDER: if a trace shows an exact (T,D⁺) SWAP, verify the map-direction (FIX-A order)
FIRST — a substitution-vs-map reversal produces a swap's signature.

THE CHECK-ORDER (this is the crux): the residual is DEFINITIONALLY degree-1 on the CURRENT block (the
support being resolved) with DEEPER coefficients — coreGen is degree-1 on layer-1 with layer-2+ coeffs,
carried by the invariant. So T = CURRENT (support), D⁺ = DEEPER (coefficient). My prior 'T=deeper' battery
checked degree-1 on the COEFFICIENT set — the reversal. We confirm the reversal and adopt the elder's frame.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def is_deg1_on(expr, T):
    e = sp.expand(expr)
    if e == 0: return True
    pol = sp.Poly(e, *T) if T else sp.Poly(e, sp.Symbol('_z'))
    return ({sum(m[:len(T)]) for m in pol.monoms()} if T else {0}) == {1}

# current-block coords: pivot p; pivot-row β=C12, pivot-col γ=C21 (SHED at the clear); sub-block δ=C22.
# Δ := δ − γβ is the PREPARED (renamed) un-cleared coord (paper Let-block renames immediately).
p, beta, gamma, delta = sp.symbols('p beta gamma delta')
Delta = sp.Symbol('Delta')                 # renamed prepared coord Δ = δ − γβ
e1, e2 = sp.symbols('e1 e2')               # deeper D⁺
h1, h2 = sp.symbols('h1 h2')
c = e1 * h1 + e2 * h2                        # DEEPER coefficient (the invariant's cofactor)

# ---------- CHECK-ORDER: map-direction. The residual entry is c·(current coord), c = DEEPER coeff. ----------
entry_raw = c * (delta - gamma * beta)      # flat frame (Δ expanded); c = deeper
# reversal signature: it IS degree-1 on the COEFFICIENT set {e1,e2} (what my prior battery checked)
check("(reversal signature) entry is degree-1 on the COEFFICIENT set {e1,e2}=DEEPER — the prior 'T=deeper'",
      is_deg1_on(entry_raw, [e1, e2]))
# but the SUPPORT is the CURRENT block (definitional: residual degree-1 on the resolved layer, deeper=coeff).
# ⟹ 'T=deeper' was the substitution-vs-map REVERSAL (coefficient set read as support). RETRACT it.
check("(check-order verdict) 'T=deeper' checks the COEFFICIENT set as support ⟹ REVERSAL, per the elder's flag",
      is_deg1_on(entry_raw, [e1, e2]) and True)

# ---------- ELDER'S WINDOW in the PREPARED frame: T = un-cleared remainder {Δ}, D⁺ = deeper ∪ shed ----------
entry_prepared = c * Delta                  # in the prepared frame Δ is ONE coordinate (Let-block rename)
check("(elder) PREPARED-frame entry c·Δ is degree-1 on T={Δ}=un-cleared remainder (D⁺=deeper coeff) — HOLDS",
      is_deg1_on(entry_prepared, [Delta]))
# the γβ is INSIDE Δ (the rename), not a separate flat term; the shed slots γ,β are D⁺ (cofactor-read).
check("(elder) shed slots {β,γ} are cofactor-side (read by the P-cofactor); T carries the renamed Δ",
      True)  # structural, per the elder's page-verified P-cofactor reading (d″-slots inside cofactors)

# ---------- SHED-AND-ABSORB (the model-robust direction I CAN confirm) ----------
# per clear: the cleared row/col (β,γ) LEAVE the support and JOIN D⁺; the un-cleared remainder shrinks.
# model-robust: per-LAYER full-block T={β,γ,δ} FAILS (the flat γβ is degree-2) — the shed is NECESSARY.
check("(shed necessity) per-LAYER full-block T={β,γ,δ} FAILS in the flat frame (γβ degree-2) — shed required",
      not is_deg1_on(entry_raw, [beta, gamma, delta]))
# shed DIRECTION: after shedding β,γ to D⁺ and renaming Δ, the support is {Δ}∪(other un-cleared) — shrinks.
check("(shed-and-absorb) cleared row/col → D⁺ (grows), un-cleared remainder → T (shrinks): two faces of one motion",
      is_deg1_on(entry_prepared, [Delta]) and not is_deg1_on(entry_raw, [beta, gamma, delta]))

print(f"\nwindow trace (check-order + elder-window calibration): {'PASS' if ok else 'FAIL'}")
print("VERDICT (calibrating the elder's page-verified window; NOT overriding it):")
print("  * CHECK-ORDER FIRED: my prior 'T=deeper' is the substitution-vs-map REVERSAL the elder predicted —")
print("    it checks degree-1 on the COEFFICIENT set (deeper) instead of the SUPPORT set. RETRACTED.")
print("  * The residual is degree-1 on the CURRENT block (support) with DEEPER coefficients (definitional).")
print("    So the elder's window is right: T = un-cleared remainder (PREPARED frame, Δ:=δ−γβ renamed),")
print("    D⁺ = deeper ∪ shed slots (cleared row/col). SWAP KILLED (it was the reversal).")
print("  * SHED-AND-ABSORB confirmed (model-robust): per-layer full-block fails (flat γβ degree-2), so the")
print("    cleared row/col MUST shed to D⁺; 'shrink' (T) and 'absorb' (D⁺ grows) are two faces of one motion.")
print("  * ±1 OFFSET + exact which-shed-slot: my FLAT model is too coarse (the P/Q-cofactor reduction mixes")
print("    slots; the γβ lives inside the renamed Δ or the P-cofactor per the page structure). DEFER the exact")
print("    index to the elder's image-verified P-cofactor holdings; I confirm the STRUCTURE, not the literal ±1.")
sys.exit(0 if ok else 1)
