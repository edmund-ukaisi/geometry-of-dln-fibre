import sympy as sp
# C5 det-unit verification (controller flagged). With C1 now ITERATED pivotBlowupOn (no lemma2
# straightening), where does the det-unit live? C5 = block-column split → complement via C1 (blow-up,
# Jacobian x_p^{card-1} — NOT det-unit, it's the monomial weight) + survivor via C2 (pass-through GL).
# The C2 pass-through GL change is the ONLY det-unit piece in C5. Verify C2's pass-through is det-unit.
#
# C2: active factor C_s FULL rank on the prefix image. Pass it through = absorb its invertible action
# into the next factor's coords. The change of variables on the next factor's coords is multiplication by
# (the relevant block of) C_s — but C_s is FULL RANK, so its action is an INVERTIBLE linear map; the
# Jacobian is det(C_s)^(±something), a UNIT iff det(C_s) ≠ 0 near the point. 
# WORRY: at the deepest point C_s → 0, so det(C_s) → 0 — NOT a unit! The pass-through can't be a naive
# GL absorption at the singular point. Resolve:
print("=== C5/C2 det-unit: the pass-through is NOT a naive GL absorption at the singular point ===")
print("""
C2 (full-rank pass-through) at the deepest point: the active factor C_s is full rank ON THE PREFIX IMAGE
but its ENTRIES → 0 at the deepest point (the whole core vanishes there). So 'absorb C_s's invertible
action' via a GL change would have Jacobian det(C_s) → 0 — NOT a unit. 

RESOLUTION (the correct C2 mechanism): C2 is NOT a GL absorption. After C_s is full-rank on the prefix,
the product C_{>s}·C_s has the SAME rank-defect locus as C_{>s} restricted to im(C_s) — so C2 DESCENDS
to the chain C_{>s} on the (smaller) image, treating C_s's full-rank block via its OWN blow-up if needed.
The 'pass-through' is: the rank drop is downstream, so C2 recurses on C_{>s} (depth L drops, one factor
consumed). The det-unit framing was MY error in #138/#140 ('a measure-preserving GL change, det a unit')
— at the deepest point that's false. CORRECT: C2 = descend on the downstream chain (L drops), the active
full-rank factor's coords become spectator/regular coords OR get their own pivotBlowupOn.

⟹ C5's det-unit concern is MOOT under the iterated-blow-up frame: there is NO det-unit GL absorption.
C5 = complement via C1 (iterated blow-up, monomial weight) + survivor via C2 (descend on downstream chain,
L drops). BOTH are blow-up/recursion, neither a det-unit GL change. The C5 'block-column det-unit' I
flagged before #27 is DISSOLVED — there's no det-unit step to verify; it's all iterated blow-up.
""")
print("FLAG for the controller: my #138/#140 C2 description ('measure-preserving GL change, det a unit')")
print("is ALSO an off-path artifact (det→0 at the deepest point). Correct C2 = descend on the downstream")
print("chain via the dispatcher (L drops), full-rank factor's coords spectator/own-blow-up. Same monomial")
print("frame as C1. Should fix C2's wording too — no det-unit GL absorption anywhere in the route.")
