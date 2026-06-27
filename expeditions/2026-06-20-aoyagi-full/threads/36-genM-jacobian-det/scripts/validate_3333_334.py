import sympy as sp
u=sp.Symbol('u')
exec(open('/tmp/deadleaf_validate2.py').read().split('M=[3,3,1,3]')[0])  # reuse build_chain

# === (3,3,3,3): Text=[3,3,2,1] (live leaf Text3=1). L=3. ===
# Effective leaf q = deepest Text>0 = Text3=1 -> q=L=3 -> use Rfin_3 (LIVE leaf, the terminal case).
# Per Codex: q=L -> live Rfin pivot, kept path propagates it.
def test3333():
    M=[3,3,3,3]; Text=[3,3,2,1]; Wext=[3,3,3,3]; L=3
    # dims: B0:3x3,B1:3x2,B2:2x1; N0:3x0,N1:2x1,N2:1x2; W0:0x3,W1:1x3,W2:2x3; Rmat0:3x3,Rmat1:3x3,Rmat2:2x3; Rfin:1x3
    e=sp.Symbol('e')
    b=dict(B={0:sp.eye(3),1:sp.zeros(3,2),2:sp.zeros(2,1)},
           N={0:sp.zeros(3,0),1:sp.zeros(2,1),2:sp.zeros(1,2)},
           W={0:sp.zeros(0,3),1:sp.zeros(1,3),2:sp.zeros(2,3)},
           Rmat={0:sp.zeros(3,3),1:sp.zeros(3,3),2:sp.zeros(2,3)},
           Rfin=sp.zeros(1,3))
    # q=L=3: live leaf. kept-diagonal B1,B2 carry; Rfin_3[0,0]=e (the pivot at the live leaf).
    b['B'][1][0,0]=1; b['B'][1][1,1]=1; b['B'][2][0,0]=1
    b['Rfin'][0,0]=e
    C,A,suf,H=build_chain(M,Text,b)
    return sp.simplify(H[0])
H3333=test3333()
print("(3,3,3,3) effective-leaf (q=L=3, live Rfin pivot e, kept-diag B): Hmat_0 =")
sp.pprint(H3333)
print("nonzero?", H3333!=sp.zeros(*H3333.shape), " at e=1:", H3333.subs({sp.Symbol('e'):1})[0,0])

# === (3,3,4): Text=[3,3,1] (live leaf Text2=1). L=2. tStar=(1,0). ===
def test334():
    M=[3,3,4]; Text=[3,3,1]; Wext=[3,3,4]; L=2
    # dims: B0:3x3,B1:3x1; N0:3x0,N1:1x2; W0:0x3,W1:2x4; Rmat0:3x3,Rmat1:3x3; Rfin:1x4
    e=sp.Symbol('e')
    b=dict(B={0:sp.eye(3),1:sp.zeros(3,1)},
           N={0:sp.zeros(3,0),1:sp.zeros(1,2)},
           W={0:sp.zeros(0,3),1:sp.zeros(2,4)},
           Rmat={0:sp.zeros(3,3),1:sp.zeros(3,3)},
           Rfin=sp.zeros(1,4))
    # q=L=2: live leaf. B1 kept-diag (3x1): B1[0,0]=1. Rfin[0,0]=e.
    b['B'][1][0,0]=1
    b['Rfin'][0,0]=e
    C,A,suf,H=build_chain(M,Text,b)
    return sp.simplify(H[0])
H334=test334()
print("\n(3,3,4) effective-leaf (q=L=2, live Rfin pivot e): Hmat_0 =")
sp.pprint(H334)
print("nonzero?", H334!=sp.zeros(*H334.shape), " at e=1:", H334.subs({sp.Symbol('e'):1})[0,0])
