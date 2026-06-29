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
for M in [(4,3,3,2),(3,4,3,3)]:
    M=tuple(M);L=len(M)-1;ap=achiever_path(M);tach=[M[0]]+list(ap)+[0]
    Text=[M[0]]+[tach[k] for k in range(len(tach)) if False]
    Text=[(M[0] if k==0 else (tach[k-1] if k-1<len(tach) else 0)) for k in range(L+2)]
    Wext=[M[k] if k<=L else 1 for k in range(L+2)]
    print(f"M={M}: minAdm={minAdmRec(M)}, achiever drops={ap}")
    print(f"   tach={tach}")
    print(f"   Text(k) k=0..L+1 = {Text}")
    print(f"   Wext(k) = {Wext[:L+1]}")
    print(f"   flatDim = {sum(M[k]*M[k+1] for k in range(L))}")
    # boundaries: s=1..L-1 interior (E-blocks), leaf at s=L
    for s in range(1,L):
        t_s=Text[s]; t_s1=Text[s+1]; r=t_s-t_s1; c=Wext[s]-t_s1
        print(f"   bd s={s}: Text_s={t_s},Text_(s+1)={t_s1}: K is {t_s1}x{t_s1}, X is {r}x{t_s1}, N is {t_s1}x{c}, E is {r}x{c} (={r*c} free)")
    print(f"   leaf s={L}: Rfin = Text_L x Wext_L = {Text[L]}x{Wext[L]} ({Text[L]*Wext[L]} slots incl 1 anchor)")
