import sympy as sp
u=sp.Symbol('u')
exec(open('/tmp/deadleaf_validate2.py').read().split('M=[3,3,1,3]')[0])

# (3,3,1,3) with CORRECT tach=(3,2,0,0), Text=[3,3,2,0]. Wext=[3,3,1,3]. L=3.
# Text(0)=3,Text(1)=3,Text(2)=2,Text(3)=0. q=deepest Text>0 = index 2 (Text2=2). q=2 < L=3 (DEAD leaf).
# Boundaries: dims with t=Text(k+1),c=Wext(k)-Text(k+1),m'=Wext(k+1):
for k in range(3):
    Text=[3,3,2,0]; Wext=[3,3,1,3]
    t=Text[k+1]; c=Wext[k]-Text[k+1]; mp=Wext[k+1]
    print(f"  k={k}: B_{k}:{Text[k]}x{t}, N_{k}:{t}x{c}, W_{k}:{c}x{mp}, Rmat_{k}:{Text[k]}x{Wext[k]}")
print(f"  Rfin: {[3,3,2,0][3]}x{[3,3,1,3][3]} (leaf)")
# k=0: B0:3x3,N0:3x0,W0:0x3,Rmat0:3x3. k=1: B1:3x2,N1:2x1,W1:1x1,Rmat1:3x3. k=2: B2:2x0,N2:0x3,W2:3x3,Rmat2:2x1. Rfin:0x3.
# q=2: deepest E at boundary 2: r_2=Text2-Text3=2-0=2, c_2=Wext2-Text3=1-0=1. E-block 2x1 (nonempty). 
#   Carrier W_2 (3x3) propagates to leaf output. q=2=L-1, so only W_2 carrier (W_q..W_{L-1}=W_2).
M=[3,3,1,3]; Text=[3,3,2,0]; Wext=[3,3,1,3]; L=3
e,w2=sp.symbols('e w2')
b=dict(B={0:sp.eye(3),1:sp.zeros(3,2),2:sp.zeros(2,0)},
       N={0:sp.zeros(3,0),1:sp.zeros(2,1),2:sp.zeros(0,3)},
       W={0:sp.zeros(0,3),1:sp.zeros(1,1),2:sp.zeros(3,3)},
       Rmat={0:sp.zeros(3,3),1:sp.zeros(3,3),2:sp.zeros(2,1)},
       Rfin=sp.zeros(0,3))
# kept-diagonal B1 (3x2): B1[0,0]=1,B1[1,1]=1. pivot e at Rmat_2 (2x1) bottom-right r2xc2=2x1 -> Rmat2[0,0]=e
#   (row 0 = the kept row reachable). carrier W2 (3x3): W2[0,0]=w2.
b['B'][1][0,0]=1; b['B'][1][1,1]=1
b['Rmat'][2][0,0]=e
b['W'][2][0,0]=w2
C,A,suf,H=build_chain(M,Text,b)
H0=sp.simplify(H[0])
print("\n(3,3,1,3) CORRECT Text=[3,3,2,0], q=2: Hmat_0 =")
sp.pprint(H0)
print("nonzero?", H0!=sp.zeros(*H0.shape), " entry(0,0) at e=w2=1:", H0.subs({e:1,w2:1})[0,0])

# (1,2,2) CORRECT tach=(1,0,0), Text=[1,1,0], Wext=[1,2,2], L=2. q=1 (Text1=1>0,Text2=0). DEAD leaf.
# k=0:B0:1x1,N0:1x0,W0:0x2,Rmat0:1x1. k=1:B1:1x0,N1:0x?,W1:?x2,Rmat1:1x2. Rfin:0x2.
# wait Text=[1,1,0]: Text0=1,Text1=1,Text2=0. k=0:t=Text1=1,c=Wext0-Text1=1-1=0. k=1:t=Text2=0,c=Wext1-Text2=2-0=2.
# B0:Text0xText1=1x1; N0:1x0; W0:0x2; Rmat0:1x1(forced 0). B1:Text1xText2=1x0; N1:0x2; W1:2x2; Rmat1:Text1xWext1=1x2.
# q=1: deepest E at boundary 1: r_1=Text1-Text2=1-0=1, c_1=Wext1-Text2=2-0=2. E-block 1x2 (nonempty). 
#   q=1=L-1, carrier W_1 (2x2). 
M2=[1,2,2]; Text2=[1,1,0]; Wext2=[1,2,2]
b2=dict(B={0:sp.eye(1),1:sp.zeros(1,0)},
        N={0:sp.zeros(1,0),1:sp.zeros(0,2)},
        W={0:sp.zeros(0,2),1:sp.zeros(2,2)},
        Rmat={0:sp.zeros(1,1),1:sp.zeros(1,2)},
        Rfin=sp.zeros(0,2))
ee,ww=sp.symbols('ee ww')
b2['Rmat'][1][0,0]=ee   # E at boundary 1 (1x2), entry (0,0)
b2['W'][1][0,0]=ww      # carrier W_1 (2x2)
C,A,suf,H=build_chain(M2,Text2,b2)
H02=sp.simplify(H[0])
print("\n(1,2,2) CORRECT Text=[1,1,0], q=1: Hmat_0 =", H02.tolist(), "nonzero?", H02!=sp.zeros(*H02.shape))
