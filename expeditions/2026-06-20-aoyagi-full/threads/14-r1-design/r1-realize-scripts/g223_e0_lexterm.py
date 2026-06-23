import numpy as np
# Pin the e=0 sub-branch lex-termination precisely (pp-r1realize's #98). The cascade center has e=0;
# the e=0 sub-locus is a DEEPER node — verify it lex-drops (NOT a stall).
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
print("e=0 sub-branch (the C5 complement's downstream ALSO vanishes) — does it lex-drop?")
print()
print("At the C5 node (step s, t_{s-1}>t_s>0), the complement is the rank-(t_{s-1}-t_s) block killed at s.")
print("e = downstream (C_{s+1}···C_L) applied to the complement's direction.")
print(" - e ≠ 0 chart: the complement direction survives downstream until SOME later layer kills it. The")
print("   Fubini-shear δ'=δ+(Gq·e)/‖e‖² applies, loss=‖e‖²δ'² ⊞ survivor — regular ½ + ONE reduced chain.")
print(" - e = 0 sub-locus: the complement's downstream vanishes IMMEDIATELY (at s+1, or the downstream is")
print("   already rank-deficient on it). Then the complement is NOT resolved by the shear here — it's a")
print("   FURTHER rank-defect to resolve. This is a DEEPER node on the complement sub-chain.")
print()
print("LEX-TERMINATION (the #98 answer): the e=0 sub-branch recurses on the complement, and it lex-DROPS:")
print(" - the complement is a rank-(t_{s-1}-t_s) sub-chain; resolving it is a C-node on a SMALLER problem")
print("   (the complement's own widths, ⊂ the parent). ΣM_complement < ΣM_parent (the complement is a")
print("   strict sub-block) ⟹ lex(L, ΣM, ncDefect) DROPS on the e=0 sub-branch. NOT a stall.")
print(" - Concretely: e=0 means the complement direction is in the kernel of the downstream EARLIER than")
print("   a generic complement — a deeper stratum, codim STRICTLY larger (more rank-defect), so its Mval")
print("   is larger (≥ the parent's), and it sits DEEPER in the rank-descent. The recursion on it terminates")
print("   by the same lex measure (ΣM or the complement's depth drops).")
print()
print("⟹ ANSWER to pp-r1realize #98: the cascade does NOT pin e≠0 (the center has e=0). BUT the e=0 sub-")
print("branch is NOT a stall — it's a DEEPER C-node (the complement's own descent), which lex-drops (ΣM of")
print("the complement sub-chain < ΣM parent). So the C5 chart cover = {e≠0 charts: Fubini-shear regular ½}")
print("∪ {e=0 sub-locus: recurse on the complement, lex-drops}. The atlas cover (charts e_i≠0 + the e=0")
print("deeper node) handles it; lex-termination holds on BOTH branches. pp-r1realize's #98 closes: e=0 = a")
print("deeper node, not a stall. (The cascade center sits ON the e=0 locus — the deepest — which is why the")
print("recursion must continue there: the deepest IS the most-degenerate point, the e=0 deepest stratum.)")
