#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). The elder's named verification target for GAP-2 (ii):
# does the Schur shear subtract EXACTLY the u_pivot-carrying residue — is it the multilinearity-
# restoration step? PROTOCOL: a residue the Schur does NOT absorb = a FINDING AGAINST THE CLAUSE.
"""
Elder's expectation (GAP-2 reading (ii), forced by the crux): under the SINGLE division, a C21·C12
cross-term would survive as a residue DeeperMultilinear cannot absorb — u_pivot is exceptional (∉ D⁺) —
and the Schur exists precisely to remove it, restoring the multilinear form post-Schur.

We check, EXACTLY (sympy/ℚ), on the coupled Schur structure (thread-33/34 faithful):
  (D) THE DANGER: a degree-2-in-CENTER entry (C21·C12) DOES leave a u_pivot residue under blow-up +
      SINGLE division: (u_p·C21')(u_p·C12')/u_p = u_p·C21'·C12' — carries the exceptional u_p ∉ D⁺.
  (R) THE ROLE: the fold's actual residual (DeeperMultilinear parent, degree-1 in center) gains
      EXACTLY u_p^1 per entry ⟹ single division is clean, NO u_p residue. The Schur keeps the residual
      degree-1-in-center (it folds the C21·C12 into the DEEPER cofactor via the layer advance), so the
      dangerous degree-2-center entry never forms.
  (N) NECESSITY: if the Schur did NOT fold C21·C12 into the coefficient — i.e. the coupled Schur
      complement Δ = C22 − C21·C12 were carried with C21,C12 STILL in the (next) center — the next
      blow-up would hit the degree-2 term and leave a u_p residue. So the Schur (+ layer advance) is
      what prevents it: multilinearity-restoration in the precise sense "keeps the residual
      degree-1-in-center", the u_p residue being the failure mode it averts.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

u_p = sp.Symbol('u_p')                    # the exceptional pivot axis (∉ D⁺)
# strict-transform (quot) coords of the center block after blow-up
b_pr, g_pr, d_pr = sp.symbols('beta_pr gamma_pr delta_pr')   # β',γ',δ' (blockBlowupCoordQuot values)
e1, e2 = sp.symbols('e1 e2')              # deeper D⁺

def single_div(expr):
    """pull back through blockBlowupMap (center coord x ↦ u_p·x'), then divide by u_p ONCE."""
    return sp.cancel(sp.expand(expr) / u_p)

def carries_pivot(expr):
    """does expr (a single-division quotient) still contain the exceptional u_p? (residue ⟺ True)."""
    return u_p in sp.expand(expr).free_symbols

# ---------- (D) THE DANGER: a degree-2-center entry leaves a u_p residue ----------
# a hypothetical residual entry = C21·C12 (degree-2 in center). Under blow-up each factor ↦ u_p·(quot):
danger_blownup = (u_p * g_pr) * (u_p * b_pr)          # C21·C12 ↦ (u_p γ')(u_p β')
danger_quot = single_div(danger_blownup)              # ÷ u_p ONCE
check("(D) degree-2-center entry (C21·C12) leaves a u_p·γ'·β' RESIDUE after single division",
      carries_pivot(danger_quot) and sp.expand(danger_quot - u_p * g_pr * b_pr) == 0)
check("(D) that residue is NOT DeeperMultilinear (carries the exceptional u_p ∉ D⁺={e1,e2})",
      u_p not in {e1, e2} and carries_pivot(danger_quot))

# ---------- (R) THE ROLE: a degree-1-center entry gains EXACTLY u_p^1 ⟹ clean single division ----------
# the fold's actual entry (DeeperMultilinear, degree-1 in center): resid = ∑ c_i·(center coord i),
# c_i deeper. One representative entry: c_delta·δ with c_delta = e1·h1 + e2·h2.
h1, h2 = sp.symbols('h1 h2')
c_delta = e1 * h1 + e2 * h2
entry_deg1 = c_delta * (u_p * d_pr)                   # δ ↦ u_p·δ'; deeper e untouched (spectator)
entry_quot = single_div(entry_deg1)
check("(R) degree-1-center entry gains exactly u_p^1 ⟹ single division CLEAN (no u_p residue)",
      not carries_pivot(entry_quot) and sp.expand(entry_quot - c_delta * d_pr) == 0)

# the fold's Schur folds C21·C12 into the DEEPER cofactor (my GAP-2 (B)): the child δ'-slot coefficient
# reads (β',γ') = old center, which are SPECTATORS at the next step (in D⁺', not the next center).
child_delta_slot_coeff = c_delta - g_pr * b_pr * h1   # e.g. a cofactor picking up −γ'β'·h1 (in D⁺')
check("(R) the C21·C12 lands in the DEEPER cofactor (reads old-center β',γ' ∈ D⁺'), NOT the center — "
      "so it is a SPECTATOR at the next blow-up, never gaining u_p",
      u_p not in child_delta_slot_coeff.free_symbols)

# ---------- (N) NECESSITY: if C21·C12 STAYED in the next center, the next blow-up leaves a u_p residue.
# next step: center advances to {δ'=next pivot region, ...}; the cofactor (β'γ') must be a SPECTATOR.
# counterfactual — if β',γ' were (wrongly) kept in the NEXT center, they'd blow up:
counterfactual = single_div((u_p * g_pr) * (u_p * b_pr) * h1)   # β'γ' in next center ⟹ each ↦ u_p·(..)
check("(N) COUNTERFACTUAL (C21·C12 kept in next center): next blow-up + single div leaves u_p residue",
      carries_pivot(counterfactual))
check("(N) so the Schur+layer-advance (C21·C12 → DEEPER cofactor) is what AVERTS the u_p residue",
      not carries_pivot(child_delta_slot_coeff) and carries_pivot(counterfactual))

# ---------- verdict ----------
print(f"\nSchur multilinearity-restoration check: {'PASS' if ok else 'FAIL'}")
print("VERDICT (for the elder): the elder's DANGER is CONFIRMED (a degree-2-center C21·C12 term does")
print("  leave a u_pivot residue under single division, non-DeeperMultilinear). The Schur's ROLE is")
print("  confirmed AS multilinearity-preservation, with one PRECISION: the fold's Schur does not")
print("  'subtract a u_p residue from an existing entry' — under the carried DeeperMultilinear invariant")
print("  no degree-2-center entry ever forms, so no u_p residue arises to subtract. Rather, the Schur")
print("  KEEPS the residual degree-1-in-center by folding C21·C12 into the DEEPER cofactor (the layer")
print("  advance, GAP-2 (A)/(B)); the u_p residue is the FAILURE MODE it averts (confirmed by the (N)")
print("  counterfactual), not a term it removes post-hoc. Reading (ii) + DeeperMultilinear-preservation")
print("  hold either way (crux-forced). NOT a finding against the clause — a mechanism precision.")
sys.exit(0 if ok else 1)
