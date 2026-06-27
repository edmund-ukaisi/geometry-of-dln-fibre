import sympy as sp
u=sp.Symbol('u')
def build_chain(M, Text, blocks):
    L=len(M)-1; Wext=list(M)
    def chainQ(k):
        t=Text[k+1]; Mp=Wext[k]; c=Mp-t; N=blocks['N'][k]
        Q=sp.zeros(t,Mp)
        for i in range(t): Q[i,i]=1
        for i in range(t):
            for jj in range(c): Q[i,t+jj]=N[i,jj]
        return Q
    C={L:u*blocks['Rfin']}
    for k in range(L-1,-1,-1):
        C[k]=blocks['B'][k]*chainQ(k)+u*blocks['Rmat'][k]
    def chainA(k):
        t=Text[k+1]; Mp=Wext[k]; c=Mp-t; mp=Wext[k+1]; N=blocks['N'][k]; W=blocks['W'][k]; Cn=C[k+1]
        A=sp.zeros(Mp,mp); kept=Cn-N*W
        for i in range(t):
            for jj in range(mp): A[i,jj]=kept[i,jj]
        for i in range(c):
            for jj in range(mp): A[t+i,jj]=W[i,jj]
        return A
    A={k:chainA(k) for k in range(L)}
    suf={L:sp.eye(Wext[L])}
    for k in range(L-1,-1,-1): suf[k]=A[k]*suf[k+1]
    H={L:blocks['Rfin']}
    for k in range(L-1,-1,-1):
        H[k]=blocks['B'][k]*H[k+1]+ (blocks['Rmat'][k]*A[k])*suf[k+1]
    return C,A,suf,H

M=[3,3,1,3]; Text=[3,2,0,0]; Wext=[3,3,1,3]; L=3
e,w1,w2=sp.symbols('e w1 w2')
# CORRECT dims: B0:3x2,N0:2x1,W0:1x3,Rmat0:3x3; B1:2x0,N1:0x3,W1:3x1,Rmat1:2x3; B2:0x0,N2:0x1,W2:1x3,Rmat2:0x1; Rfin:0x3
b=dict(B={0:sp.zeros(3,2),1:sp.zeros(2,0),2:sp.zeros(0,0)},
       N={0:sp.zeros(2,1),1:sp.zeros(0,3),2:sp.zeros(0,1)},
       W={0:sp.zeros(1,3),1:sp.zeros(3,1),2:sp.zeros(1,3)},
       Rmat={0:sp.zeros(3,3),1:sp.zeros(2,3),2:sp.zeros(0,1)},
       Rfin=sp.zeros(0,3))
# Effective leaf q: deepest Text>0. Text=[3,2,0,0] -> Text0=3,Text1=2>0,Text2=0. q=1 (boundary index where E lives).
# The DEEPEST active E-block: boundary k=1, Rmat1 (2x3), r1=Text1-Text2=2, c1=3. Put pivot e at Rmat1[0,0].
b['B'][0][0,0]=1; b['B'][0][1,1]=1   # kept-diagonal B0 (3x2): rows 0,1 carry
b['Rmat'][1][0,0]=e                   # inject e at the deepest E (boundary 1)
# carriers: W1 (3x1) routes Wext1=3 -> Wext2=1 ; W2 (1x3) routes Wext2=1 -> Wext3=3.
b['W'][1][0,0]=w1                     # W1[0,0]: carry the injected column (row 0) down
b['W'][2][0,0]=w2                     # W2[0,0]: carry to final output
C,A,suf,H=build_chain(M,Text,b)
H0=sp.simplify(H[0])
print("(3,3,1,3) effective-leaf+carrier Hmat_0 (q=1, e@Rmat1[0,0], carriers w1,w2):")
sp.pprint(H0)
print("nonzero?", H0!=sp.zeros(*H0.shape))
print("at e=w1=w2=1:", sp.simplify(H0.subs({e:1,w1:1,w2:1})).tolist())

print("\n=== FAILURE CHECK: same (3,3,1,3) but carriers = 0 (identity-elsewhere, no carrier) ===")
b2=dict(B={0:sp.zeros(3,2),1:sp.zeros(2,0),2:sp.zeros(0,0)},
       N={0:sp.zeros(2,1),1:sp.zeros(0,3),2:sp.zeros(0,1)},
       W={0:sp.zeros(1,3),1:sp.zeros(3,1),2:sp.zeros(1,3)},
       Rmat={0:sp.zeros(3,3),1:sp.zeros(2,3),2:sp.zeros(0,1)},
       Rfin=sp.zeros(0,3))
b2['B'][0][0,0]=1; b2['B'][0][1,1]=1
b2['Rmat'][1][0,0]=e   # inject e but NO carriers (W=0)
C,A,suf,H=build_chain(M,Text,b2)
H0f=sp.simplify(H[0])
print("no-carrier Hmat_0:")
sp.pprint(H0f)
print("== 0 ?", H0f==sp.zeros(*H0f.shape), " <- confirms the simple witness FAILS (carriers ESSENTIAL)")
