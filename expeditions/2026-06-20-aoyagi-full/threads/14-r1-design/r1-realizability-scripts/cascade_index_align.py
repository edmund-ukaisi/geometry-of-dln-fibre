# PIN the index alignment for fm3's #116 question.
# CORE (CascadeRealizable.lean):
#   cascadeTuple d t : s ↦ partialId (d s.succ)(d s.castSucc)(t s),  s : Fin N,  d : Fin(N+1)→ℕ.
#   submult_succ: submult i p.succ = A_p * submult i p.castSucc. New LEFT factor = A_p = cascadeTuple d t p.
#   At that step, partialId_mul(r=d_{p+1}, m=d_{p.castSucc}=d_p, c=d_i, a=t_p, b=prev) needs a ≤ m, i.e.
#       SIDE CONDITION (Core):  t_p ≤ d_{p.castSucc} = d_p.        [p : Fin N, so p ∈ {0,...,N-1}, d_p = M_p]
#   This is EXACTLY the hypothesis ht in submult_cascade_prefix: ∀ p:Fin N, t p ≤ d p.castSucc.
#
# So fm3's "t_{p+1} ≤ d_p" (their submult_succ framing where the new factor index is named differently)
# RESOLVES, in Core's own indexing, to:  t_p ≤ d_p  (the s-th block's rank ≤ its INPUT width d_p = d s.castSucc).
# (fm3 wrote "t_{p+1} ≤ d_p" using a 1-shifted t-naming; Core's def names the block's rank t_p directly,
#  and the gate is t_p ≤ d_{p.castSucc} = d_p. Same inequality, Core's clean form.)
#
# LAMBDA (Lambda.lean): T : Fin L → ℕ, admBound: T j ≤ (j=0 ? min(M_0,M_1) : M_{j.succ}=M_{j+1}).
#   The t-superscript convention: T j  =  t^{(j+1)} in the paper's 1-indexed t^{(1)}..t^{(L)}
#   (design-spec: t^{(j)} = rank of first-j product; T is 0-indexed so T j = t^{(j+1)}).
#   The cascade's block-s rank t_s (Core, 0-indexed s:Fin N) = the running rank AFTER block s = t^{(s+1)}
#   = T s (Lambda 0-indexed). So Core t_s = Lambda T s.  [t-index aligned: both 0-indexed over Fin N=Fin L]
#
# Now the SIDE CONDITION in Lambda terms:  t_s ≤ d_s, i.e.  T s ≤ M_s  (d=M, the widths).
# Does admBound give T s ≤ M_s?  admBound: T s ≤ M_{s+1} (for s≥1), ≤ min(M_0,M_1) (s=0).
#   - s ≥ 1: admBound gives T s ≤ M_{s+1}.  We NEED T s ≤ M_s.  DIFFERENT INDEX (M_{s+1} vs M_s)!
#   - s = 0: admBound gives T 0 ≤ min(M_0,M_1) ≤ M_0.  We NEED T 0 ≤ M_0 (=d_0).  ✓ (min ≤ M_0).
# So at s=0 it's clean; at s≥1 admBound gives the M_{s+1} bound, NOT directly M_s. INDEX-SHIFT FLAGGED.
print("INDEX ALIGNMENT (decl-checked vs Core CascadeRealizable + Lambda):")
print("  Core side condition (ht in submult_cascade_prefix): t_p ≤ d_{p.castSucc} = d_p, p:Fin N.")
print("  = the block's rank ≤ its INPUT width d_p (= M_p with d=M). fm3's 't_{p+1}≤d_p' = this in Core's clean form.")
print()
print("  Lambda admBound gives: T s ≤ M_{s+1} (s≥1), ≤ min(M_0,M_1) (s=0).  [Core t_s = Lambda T s]")
print("  NEEDED: t_s ≤ d_s = M_s.")
print("    s=0: admBound T_0 ≤ min(M_0,M_1) ≤ M_0 = d_0.  CLEAN ✓")
print("    s≥1: admBound T_s ≤ M_{s+1}, but NEED T_s ≤ M_s.  *** INDEX-SHIFT: M_{s+1} ≠ M_s ***")
print()
# BUT — the weak-DECREASE saves it. admPred has T weakly decreasing: T s ≤ T_{s-1} ≤ ... ≤ T_0,
# AND each T_j ≤ M_{j+1}. For T_s ≤ M_s, use: T_s ≤ T_{s-1} ≤ M_s (admBound on T_{s-1}: T_{s-1} ≤ M_s).
# So T_s ≤ T_{s-1} ≤ admBound(s-1) = M_s (for s-1 ≥ 1, admBound = M_{(s-1)+1} = M_s). CHAIN GIVES IT.
print("THE FIX (weak-decrease closes the shift): admPred has T weakly-DECREASING (T_s ≤ T_{s-1} ≤ ... ≤ T_0).")
print("  For s ≥ 1: T_s ≤ T_{s-1} ≤ admBound(s-1).")
print("    s-1 ≥ 1: admBound(s-1) = M_{(s-1)+1} = M_s.  ⟹ T_s ≤ M_s ✓")
print("    s-1 = 0 (s=1): admBound(0) = min(M_0,M_1) ≤ M_1 = M_s.  ⟹ T_1 ≤ T_0 ≤ M_1 = M_s ✓")
print("  So T_s ≤ M_s holds for ALL s — via (weak-decrease) ∘ (admBound at s-1), NOT admBound at s directly.")
print()
# Sanity vs the anchors:
def check(M, T):
    L=len(M)-1; tt=list(T)
    # Core gate: t_s ≤ d_s = M_s for s=0..L-1
    ok = all(tt[s] <= M[s] for s in range(L))
    detail = [(s, tt[s], M[s], tt[s]<=M[s]) for s in range(L)]
    return ok, detail
for M,T,lab in [([2,2,2],[1,0],"(2,2,2) T*=(1,0)"),([3,2,3],[1,0],"(3,2,3) T*=(1,0)")]:
    ok,detail=check(M,T)
    print(f"  ANCHOR {lab}: t_s ≤ M_s ∀s? {ok}  detail (s,t_s,M_s,ok): {detail}")
