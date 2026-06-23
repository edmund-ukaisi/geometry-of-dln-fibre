import numpy as np
# Cross-confirm pp-r1realize's per-node chain for t=(3,3,2,2,2,0) against my cascade.
# Their reading: t_0=M^1=3, rank chain t_0..t_6 = [3,3,3,2,2,2,0] (7 values), nodes s=1..6.
# Node s: drop t_{s-1} → t_s. Their node classification:
#   s=1: 3→3 C2;  s=2: 3→3 C2;  s=3: 3→2 C5;  s=4: 2→2 C2;  s=5: 2→2 C2;  s=6: 2→0 C1.
#
# RECONCILE THE INDEXING: the original "t=(3,3,2,2,2,0)" was the rank VECTOR (t_1,...,t_L), L=6? or the
# partial-product ranks. pp-r1realize prepends t_0=M^1=3, giving the FULL rank chain [t_0,...,t_L].
# Wait — t=(3,3,2,2,2,0) has 6 entries. If these are (t_1,...,t_6), then with t_0=3 the chain is
# [3, 3,3,2,2,2,0] = 7 values, t_0..t_6, L=6. pp-r1realize's chain [3,3,3,2,2,2,0] — let me check it's
# consistent: t_0=3, t_1=3, t_2=3, t_3=2, t_4=2, t_5=2, t_6=0.
# But the ORIGINAL t=(3,3,2,2,2,0) read as (t_1..t_6) = t_1=3,t_2=3,t_3=2,t_4=2,t_5=2,t_6=0.
# pp-r1realize's [3,3,3,2,2,2,0] = [t_0..t_6] with t_0=3 PREPENDED ⟹ t_1..t_6 = 3,3,2,2,2,0 = ORIGINAL ✓.
chain = [3,3,3,2,2,2,0]  # t_0..t_6, pp-r1realize's
print("pp-r1realize chain t_0..t_6 =", chain)
print("Original t=(t_1..t_6) =", chain[1:], " (matches (3,3,2,2,2,0)? ", chain[1:]==[3,3,2,2,2,0], ")")
print()
# Per-node classification: node s drops t_{s-1}→t_s. Classify:
print("Per-node (s: t_{s-1}→t_s):")
for s in range(1,7):
    prev, cur = chain[s-1], chain[s]
    if cur==prev: cls="C2 (pass-through, gauge — no rank drop)"
    elif cur==0: cls="C1 (full drop to 0)"
    elif prev>cur>0: cls=f"C5 (PARTIAL, complement {prev-cur}, survivor {cur})"
    else: cls="?"
    print(f"  s={s}: {prev}→{cur}  {cls}")
print()
# MY CASCADE per-node read (the cascade C_s = diag(1^{t_s}, 0), running rank = t_s):
# The cascade's node at step s drops the running rank t_{s-1}→t_s. SAME classification:
print("MY cascade per-node read (C_s = diag(1^{t_s},0), drop t_{s-1}→t_s): IDENTICAL — the cascade's")
print("per-node rank-drop sequence IS this chain. Cross-confirm pp-r1realize's (a) and (b):")
print()
# (a) are s=1,2,4,5 gauge (not recursion nodes)?
print("(a) s=1(3→3),s=2(3→3),s=4(2→2),s=5(2→2): NO rank drop ⟹ C2 pass-through = GAUGE, NOT recursion")
print("    nodes. CONFIRM ✓ — the det-1 reindex absorbs them (no ΣM drop, no divisor). The cascade's")
print("    C_s=diag(1^{t_s},0) at these = full-rank diag (t_{s-1}=t_s), a gauge pass-through.")
print()
# (b) at C5 node s=3, complement-1/survivor-2 from diag(1,1,0)?
print("(b) s=3 (3→2): the cascade C_3 = diag(1,1,0) — keeps 2 (the SURVIVOR), zeroes 1 (the COMPLEMENT).")
print("    So complement=1, survivor=2. CONFIRM ✓ — exactly pp-r1realize's split. Matches diag(1,1,0).")
print()
# recursion steps + codim-list:
print("RECURSION STEPS (the divisor-contributing nodes): s=3 (C5, ΣM drops 2) + s=6 (C1, full drop). The")
print("4 C2 nodes (s=1,2,4,5) are gauge (no divisor). So the achiever leaf's codim-list = [codim(C5 s=3),")
print("codim(C1 s=6)] — one appendDivisor per drop step. MATCHES pp-r1realize's '2 recursion steps, 4 gauge'.")
print()
print("VERDICT: pp-r1realize's per-node chain MATCHES my cascade EXACTLY. (a) s=1,2,4,5 = gauge ✓; (b) C5")
print("s=3 complement-1/survivor-2 from diag(1,1,0) ✓. ONE fully-spelled realization skeleton. CONFIRMED.")
print()
print("ONE PRECISION (the ΣM-drop counts pp-r1realize noted): C5 at s=3 'ΣM drops 2', C1 at s=6 'ΣM drops 4'.")
print("Worth a check: the C1 full-drop 2→0 drops ΣM by... the schurState C1 drops ΣM by 2 per step (drop_0=")
print("drop_1=1). A full 2→0 = TWO rank-units, but as ONE C1 node it's the rank-2→0 Schur descent. The ΣM-drop")
print("of a rank-r→0 C1 node: needs care — is it 2 (one Schur step) or 2r? Flag to pp-r1realize: confirm the")
print("C1 s=6 ΣM-drop count (2 vs 4) against the schurState measure — the lex-termination uses the actual drop.")
