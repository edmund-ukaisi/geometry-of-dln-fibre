# CHECK 2 first (∀M role arithmetic): does #{R/Rfin free entries} = minAdm - 1 ?
# Build the budget from the engine's role structure:
#   Per interior boundary s=k+1 (k>=1, i.e. genuine drops, NOT the identity boundary k=0):
#     E-block free entries = r_s * c_s  where r_s = Text(s)-Text(s+1) = t_{s-1}-t_s, c_s = Wext(s)-Text(s+1) = M_s - t_s.
#   Live leaf Rfin_L free entries = Text(L-1) * Wext(L)? -- leaf C_L = u*Rfin, shape Text(L)?... 
#     From RouteMFlatLive: rfin : Matrix (Fin (Text L)) (Fin (Wext L)).  But Text L = 0 (the leaf rank).
#     Hmm Text M t L = t_{L-1}=0 at achiever. So rfin is 0x(Wext L) = EMPTY?? 
#   Wait -- in B_det3333 the leaf Rfin3 was 1x3 (Text? rows). Let me recompute Text for 3333:
#     Text3333=[3,3,2,1,0]. Text L = Text 3 = 1 (NOT 0!).  L=3, Text[3]=1. leaf rfin: Text[3] x Wext[3] = 1x3. 3 free.
#   So the convention: Text[L] = the LEAF rank = the last genuine drop value (1 for 3333), NOT 0.
#   And the achiever_path I computed (2,1) had the leaf appended as 0 -- that was MY extra. The engine's
#   Text bottoms at Text[L] = t_{L-1} = the leaf rank (1 for 3333, from drops (2,1)).
# Let me recompute with the engine convention and the LIVE leaf.

def redChain(t,M): return (t,)+tuple(M[2:])
def minAdmRec(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec(redChain(t,M)) for t in range(min(M[0],M[1])+1))
def achiever_path(M):
    L=len(M)-1
    if L<=1: return ()
    best=None;bt=None
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdmRec(redChain(t,M))
        if best is None or v<best: best=v;bt=t
    return (bt,)+achiever_path(redChain(bt,M))

def budget(M):
    M=tuple(M); L=len(M)-1
    ap=achiever_path(M)         # the genuine drop ranks, length L-1 (for L>=2): t at boundaries 1..L-1
    # Engine Text: Text[0]=M0, Text[1]=M0 (identity bd), Text[k+1]=ap[k-1] for genuine boundaries.
    # Reconstruct Text from known: 222 Text=[2,2,1] (ap=(1,)); 3333 Text=[3,3,2,1,0]? NO we said [3,3,2,1,0]
    # but ap=(2,1). Text=[3,3,2,1,...]. Let me derive: Text[0]=M0=3, Text[1]=M0=3, then ap=(2,1) gives Text[2]=2,Text[3]=1, leaf Text[4]? 
    # 3333 has L=3 so Text indices 0..3+? Text was Text M t : N->N with Text(k) for k=0..L. L=3 => Text[0..3].
    # Text3333=[3,3,2,1,0] has 5 entries -> that's Text[0..4], i.e. it extends past L. The DECODER uses Text up to leaf.
    # Cleanest: Text[k] for k=0..L where L=len(M)-1. Text[0]=M0; Text[k]=ap[k-1] for k=1..L? 
    #   3333: L=3, ap=(2,1) only length 2, need Text[1],Text[2],Text[3]. Mismatch.
    # The Lean tach3333=[3,2,1,0] (the Fin(L+1)=Fin 4 descent t), Text[k]=tach[k-1] for k>=1, Text[0]=M0.
    #   tach=[3,2,1,0]: Text[0]=M0=3, Text[1]=tach[0]=3, Text[2]=tach[1]=2, Text[3]=tach[2]=1, Text[4]=tach[3]=0.
    #   So tach = [M0, *ap, 0] = [3,2,1,0]? ap=(2,1) => [3,2,1,0]. YES. tach[0]=M0=3, then ap, then 0.
    # Text[k]=tach[k-1] (k>=1), Text[0]=M0. So Text=[M0, tach0=M0, tach1, tach2, tach3]=[3,3,2,1,0]. 
    tach=[M[0]]+list(ap)+[0]   # length L+1 (Fin L+1)
    # Text[k] = M0 if k==0 else tach[k-1], for k=0..L+1
    def Text(k): return M[0] if k==0 else (tach[k-1] if k-1 < len(tach) else 0)
    def Wext(k): return M[k] if k<=L else 1
    # E-block free entries: per boundary s=k+1, k=0..L-1 (the GenBlk boundaries). 
    #   But k=0 is identity (Rmat 0 = 0, no E). Genuine E at s=1..L-1? E shape: r_s x c_s, 
    #   r_s = Text(s)-Text(s+1), c_s = Wext(s)-Text(s+1).
    E_total=0
    for s in range(1,L):     # interior boundaries s=1..L-1 (s=L is the leaf, handled by Rfin)
        r = Text(s)-Text(s+1); c = Wext(s)-Text(s+1)
        E_total += r*c
    # Live leaf Rfin_L: shape Text(L) x Wext(L). Text(L)=tach[L-1]=ap[-1] (last genuine drop). Wext(L)=M[L].
    leaf = Text(L)*Wext(L)
    return E_total, leaf, E_total+leaf, minAdmRec(M)

for M in [(2,2,2),(3,3,3,3),(2,3,2),(4,3,3,2),(3,4,3,3),(2,2,2,2),(4,4,2,2),(3,3,3,3,3)]:
    E,leaf,tot,ma=budget(M)
    print(f"M={M}: E-free={E}, leaf-free={leaf}, total u-scaled={tot}, minAdm-1={ma-1}, MATCH={tot==ma-1}")
