import functools, itertools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def count(M, tach):
    L=len(M)-1; Text=[M[0]]+[tach[k] for k in range(L)]; Wext=list(M)
    interior=sum((Text[k]-Text[k+1])*(Wext[k]-Text[k+1]) for k in range(1,L)); leaf=Text[L]*Wext[L]
    return interior+leaf, Text, interior, leaf
# (3,3,4): find the chain tach giving active=minAdm. minAdm(3,3,4)=8. L=2. tach = (tach0=3, tach1, tach2=0).
# Text=[3, tach0=3, tach1, tach2=0]? No: M has 3 entries, L=2, tach has 3 entries (Fin 3): tach0,tach1,tach2.
# Text=[M0=3, tach0, tach1, tach2]? That's 4 = L+2 entries, but Text indexed 0..L=0..2 plus... 
# Actually Text(k) for k=0..L: Text0=M0, Text(k+1)=tach(k) for k=0..L-1. tach: Fin(L+1)=Fin 3.
# tach0=M0=3 (identity), tach1=the drop, tach2=0 (leaf). Text=[3, 3, tach1, 0]? No — Text(0)=3,Text(1)=tach0=3,
# Text(2)=tach1, and leaf Text(L)=Text(2). Hmm L=2 so Text(0),Text(1),Text(2). Text(2)=tach1. leaf=Text(2).
# But tach2=0 is tach(L)=tach(2) used where? Cgen leaf C_L=C_2=u*Rfin(2), Text(2)=tach1. 
# Let me just enumerate tach=(3,a,0) with 3>=a>=0 and Text=[3,3,a] (Text2=a), leaf=Text2*Wext2=a*4.
# Wait Text(1)=tach0=3, Text(2)=tach1=a. interior k=1: r=Text1-Text2=3-a, c=Wext1-Text2=3-a. leaf=Text2*Wext2=a*4.
M=(3,3,4)
for a in range(4):
    tach=(3,a,0)
    Text=[3,3,a]; Wext=[3,3,4]
    if a>3: continue
    interior=(Text[1]-Text[2])*(Wext[1]-Text[2])  # k=1
    leaf=Text[2]*Wext[2]
    print(f"  (3,3,4) tach={tach} Text={Text}: interior={interior}+leaf={leaf}={interior+leaf}, minAdm=8, match={interior+leaf==8}")
# flatDim question:
print()
def flatDim(M): return sum(M[k]*M[k+1] for k in range(len(M)-1))
for M in [(2,2,1),(2,2,2),(3,3,4),(3,3,3,3)]:
    print(f"M={M}: minAdm={minAdmRec(M)}, flatDim(N)={flatDim(M)}, minAdm<=N? {minAdmRec(M)<=flatDim(M)}")
