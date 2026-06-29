import sympy as sp
# (3,3,3,3,3): L=4, minAdm? flatDim = 4*9=36. Text=[3,3,2,1,?]. achiever drops...
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
        if best is None or v<best:best=v;bt=t
    return (bt,)+achiever_path(redChain(bt,M))
M=(3,3,3,3,3);L=4
ap=achiever_path(M);tach=[M[0]]+list(ap)+[0]
def Text(k): return M[0] if k==0 else (tach[k-1] if k-1<len(tach) else 0)
def Wext(k): return M[k] if k<=L else 1
print(f"M={M}: minAdm={minAdmRec(M)}, ap={ap}, tach={tach}")
print(f"Text(0..L)={[Text(k) for k in range(L+1)]}, Wext={[Wext(k) for k in range(L+1)]}")
# Per boundary s=1..L-1: C_{s+1} = layer-s kept rows (first Text_{s+1} rows of layer s), 
#   shape Text_{s+1} x Wext_{s+1}.  W_s = layer-s lift rows (last c_s = Wext_s - Text_{s+1} rows).
# layer s flat block: rows Fin Wext_s, cols Fin Wext_{s+1}, flat offset = sum_{j<s} Wext_j*Wext_{j+1}.
off=0; offsets=[]
for s in range(L):
    offsets.append(off); off+=Wext(s)*Wext(s+1)
print(f"layer flat offsets: {offsets}, total flatDim={off}")
print()
print("chain_s reindex (s=1..L-1): reads layer-s flat block, splits rows into kept(C_{s+1})+lift(W_s):")
for s in range(1,L):
    ts1=Text(s+1); cs=Wext(s)-Text(s+1); ws1=Wext(s+1)
    print(f"  chain_{s}: layer{s} block (Wext{s}={Wext(s)} x Wext{s+1}={ws1}), offset {offsets[s]}.")
    print(f"           C_{s+1} = kept rows 0..{ts1-1} (Text_{s+1}={ts1}) x cols 0..{ws1-1}")
    print(f"           W_{s}   = lift rows {ts1}..{Wext(s)-1} (c_{s}={cs}) x cols 0..{ws1-1}")
    print(f"           leaf? s==L-1={s==L-1}: C_{s+1}=C_L = u*Rfin (the live leaf) when s=L-1={L-1}")
