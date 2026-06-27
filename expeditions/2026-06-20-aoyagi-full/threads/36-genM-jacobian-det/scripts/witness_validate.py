import sympy as sp

# Build the chain Hmat telescope EXACTLY per the Lean structure, for B_det M at a parameter point.
# Chain: C_L = u*Rfin_L; C_k = Bmat_k*chainQ(N_k) + u*Rmat_k; A_k = chainA(N_k,W_k,C_{k+1}).
# chainQ(N): t x M' = [I_t | N] (t=Text(k+1), M'=Wext(k), residual cols c=M'-t).
# chainA(N,W,C): M' x m' (M'=Wext(k), m'=Wext(k+1)) = [[C - N*W],[W]] over rows (t kept, c=M'-t lift).
# Hmat: Hmat_L = Rfin_L; Hmat_k = Bmat_k*Hmat_{k+1} + E_k*suffix_{k+1}; E_k = Rmat_k*A_k; suffix_L=I,
#   suffix_k = A_k * suffix_{k+1}. prod = u*Hmat_0 (C_0=1).
# We compute Hmat_0 symbolically and check nonzero at a witness.

def build_chain(M, tach, blocks, u):
    # M: list len L+1; tach: list len L+1 (tach[0]=M[0], tach[k]=Text(k)); 
    # blocks: dict with Bmat[k] (k=0..L-1 used for boundaries; Bmat[0]=I), N[k],W[k],Rmat[k],Rfin (matrices, sympy).
    L=len(M)-1
    Text=[M[0]]+[tach[k] for k in range(1,L+1)]  # Text[0]=M0, Text[k]=tach[k]
    Wext=list(M)
    # chainQ
    def chainQ(k):
        t=Text[k+1]; Mp=Wext[k]; c=Mp-t; N=blocks['N'][k]
        Q=sp.zeros(t,Mp)
        for i in range(t): Q[i,i]=1
        for i in range(t):
            for jj in range(c): Q[i,t+jj]=N[i,jj]
        return Q
    # C
    C={}
    C[L]=u*blocks['Rfin']
    for k in range(L-1,-1,-1):
        Bk=blocks['B'][k]; Qk=chainQ(k); Rk=blocks['Rmat'][k]
        C[k]=Bk*Qk + u*Rk
    # A
    def chainA(k):
        t=Text[k+1]; Mp=Wext[k]; c=Mp-t; mp=Wext[k+1]; N=blocks['N'][k]; W=blocks['W'][k]; Cn=C[k+1]
        A=sp.zeros(Mp,mp)
        kept=Cn - N*W  # t x mp
        for i in range(t):
            for jj in range(mp): A[i,jj]=kept[i,jj]
        for i in range(c):
            for jj in range(mp): A[t+i,jj]=W[i,jj]
        return A
    A={k:chainA(k) for k in range(L)}
    # suffix
    suf={L: sp.eye(Wext[L])}
    for k in range(L-1,-1,-1):
        suf[k]=A[k]*suf[k+1]
    # Hmat
    H={L: blocks['Rfin']}
    for k in range(L-1,-1,-1):
        Ek=blocks['Rmat'][k]*A[k]  # Text[k] x Wext[k+1]... wait E_k = Rmat_k * A_k : Text[k] x Wext[k+1]
        H[k]=blocks['B'][k]*H[k+1] + Ek*suf[k+1]
    return C,A,suf,H,Text,Wext

# === (3,3,3,3): tach=(3,3,2,1) [Text=[3,3,2,1]], Wext=[3,3,3,3], L=3 ===
# Text[0]=3,Text[1]=3,Text[2]=2,Text[3]=1. r_k=Text[k]-Text[k+1]: r1=1,r2=1,r3(leaf)=Text3=1.
# c_k=Wext[k]-Text[k+1]: c1=3-2=1,c2=3-1=2. leaf Rfin: Text3 x Wext3 = 1x3.
u=sp.Symbol('u')
def test_3333(witness='simple'):
    M=[3,3,3,3]; tach=[3,3,2,1]; L=3
    Text=[3,3,2,1]; Wext=[3,3,3,3]
    # block dims: B[0]:3x3=I; B[1]:Text1 x Text2 =3x2; B[2]:Text2 x Text3=2x1.
    # N[0]: Text1 x c0 = 3x0 (c0=Wext0-Text1=0); N[1]:Text2 x c1=2x1; N[2]:Text3 x c2=1x2.
    # W[0]: c0 x Wext1=0x3; W[1]:c1 x Wext2=1x3; W[2]:c2 x Wext3=2x3.
    # Rmat[0]:Text0 x Wext0=3x3=0; Rmat[1]:Text1 x Wext1=3x3; Rmat[2]:Text2 x Wext2=2x3.
    # Rfin: Text3 x Wext3 = 1x3.
    B={0:sp.eye(3), 1:sp.zeros(3,2), 2:sp.zeros(2,1)}
    N={0:sp.zeros(3,0),1:sp.zeros(2,1),2:sp.zeros(1,2)}
    W={0:sp.zeros(0,3),1:sp.zeros(1,3),2:sp.zeros(2,3)}
    Rmat={0:sp.zeros(3,3),1:sp.zeros(3,3),2:sp.zeros(2,3)}
    Rfin=sp.zeros(1,3)
    # SIMPLE witness (my wrong §5): all Bmat diag=1, leaf pivot Rfin(0,0)=1, else 0.
    if witness=='simple':
        B[1][0,0]=1; B[1][1,1]=1  # kept diag
        B[2][0,0]=1
        Rfin[0,0]=1  # leaf pivot
    blocks={'B':B,'N':N,'W':W,'Rmat':Rmat,'Rfin':Rfin}
    C,A,suf,H,_,_=build_chain(M,tach,blocks,u)
    return H[0]
H0=test_3333('simple')
print("(3,3,3,3) SIMPLE §5 witness: Hmat_0 =")
sp.pprint(H0)
print("Hmat_0 == 0 ?", H0==sp.zeros(*H0.shape))

print("\n=== Reproduce the controller's FAILURE case: live block at s=1, DEAD leaf ===")
def test_3333_failure():
    M=[3,3,3,3]; tach=[3,3,2,1]; L=3
    B={0:sp.eye(3), 1:sp.zeros(3,2), 2:sp.zeros(2,1)}
    N={0:sp.zeros(3,0),1:sp.zeros(2,1),2:sp.zeros(1,2)}
    W={0:sp.zeros(0,3),1:sp.zeros(1,3),2:sp.zeros(2,3)}
    Rmat={0:sp.zeros(3,3),1:sp.zeros(3,3),2:sp.zeros(2,3)}
    Rfin=sp.zeros(1,3)  # DEAD leaf
    # live block at boundary s=1 only (Rmat[1] E-block, the bottom-right r1xc1=1x1), kept diag, NO leaf, W=0:
    B[1][0,0]=1; B[1][1,1]=1; B[2][0,0]=1
    Rmat[1][2,2]=1  # the E-block at boundary 1 (bottom-right 1x1)... wait dims: Rmat1 is 3x3, E-block r1xc1=1x1
    # at bottom-right = position (Text1-1, ... ). r1=Text1-Text2=3-2=1 rows, c1=Wext1-Text2=3-2=1 cols. 
    # bottom-right: row Text2..Text1-1 = row 2, col Text2..Wext1-1 = col 2. So Rmat1[2,2]=1.
    blocks={'B':B,'N':N,'W':W,'Rmat':Rmat,'Rfin':Rfin}
    C,A,suf,H,_,_=build_chain(M,tach,blocks,u)
    return H[0]
Hf=test_3333_failure()
print("live-block-at-s=1, dead-leaf, W=0: Hmat_0 =")
sp.pprint(Hf)
print("Hmat_0 == 0 ?", Hf==sp.zeros(*Hf.shape), " <- THIS is the controller's failure (#1)")
