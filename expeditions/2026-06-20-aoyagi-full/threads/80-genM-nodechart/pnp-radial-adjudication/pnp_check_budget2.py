# Refined: total u-scaled SLOTS = minAdm; exactly ONE slot is the fixed-1 pivot anchor (NOT free).
# => #{FREE u-scaled entries} = minAdm - 1 = the radial det exponent. The pivot coord (flat 0) IS the anchor.
# Verify: my 'total u-scaled' = minAdm in EVERY case above. Let me confirm and locate the anchor.
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
    M=tuple(M);L=len(M)-1;ap=achiever_path(M);tach=[M[0]]+list(ap)+[0]
    def Text(k): return M[0] if k==0 else (tach[k-1] if k-1<len(tach) else 0)
    def Wext(k): return M[k] if k<=L else 1
    E=sum((Text(s)-Text(s+1))*(Wext(s)-Text(s+1)) for s in range(1,L))
    leaf=Text(L)*Wext(L)
    return E+leaf, minAdmRec(M)
print("Claim: total u-scaled SLOTS = minAdm (one is the fixed anchor); FREE = minAdm-1.")
allok=True
for M in [(2,2,2),(3,3,3,3),(2,3,2),(4,3,3,2),(3,4,3,3),(2,2,2,2),(4,4,2,2),(3,3,3,3,3),(5,4,3,2),(2,4,4,2)]:
    tot,ma=budget(M)
    ok = (tot==ma)
    allok = allok and ok
    print(f"M={M}: total u-scaled SLOTS={tot}, minAdm={ma}, SLOTS==minAdm? {ok}  => FREE={tot-1}, minAdm-1={ma-1}")
print("\nALL: total u-scaled slots == minAdm?", allok, " => #FREE u-scaled = minAdm-1 (the fixed-1 anchor is the -1).")
