"""
2nd-M per-piece det validation (spec-validate-FIRST, validate ACROSS M).
TEST: the layer-filtration det_comp claim — det(J) = u^{minAdm-1} · prod_k (per-layer DIAGONAL-block det),
each per-layer det a UNIFORM monomial (|det K_s|^{r+c}·LDU·radial). We check:
  (G) the GLOBAL det u-separation + front power = minAdm-1, AND
  (D) the PER-LAYER diagonal-block dets are uniform monomials across M.
We build the LIVE-leaf achiever chart at TWO M with DIFFERENT K-core widths:
  M_A = (3,3,3,3) [known: u^5·a^4·δ^2·b^3]   and   M_B = (2,3,2) [NEW, smaller].
The per-layer diagonal block D_k = ∂(A_k outputs)/∂(layer-k-owned coords), with deeper C frozen.
"""
import sys; sys.path.insert(0,'/tmp/radsep')
import sympy as sp
from sympy import symbols, Matrix, eye, zeros
from families import build, chainQ, chainA, flatten

def run(label, L, M, t, mk_blocks, NC, minAdm_minus1):
    x = symbols('x0:%d'%NC, real=True); u=x[0]
    blocks, coords_by_layer = mk_blocks(x)
    A, C = build(L, M, t, blocks, u)
    vec = flatten(A, L)
    n = len(vec)
    print(f"\n=== {label}: M={M[:L+1]} t_ach={t[:L]} ===  output {n}, coords {NC}, square={n==NC}")
    if n != NC:
        print(f"  NON-SQUARE ({n} vs {NC}) — coord allocation off; FIX before trusting"); return
    # (G) global det
    J = sp.Matrix(n, NC, lambda i,j: sp.diff(vec[i], x[j]))
    det = sp.expand(J.det())
    if det == 0:
        print("  GLOBAL det == 0 (degenerate)"); return
    P = sp.Poly(det, u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
    print(f"  (G) det = {sp.factor(det)}")
    print(f"  (G) u-power [{lo}..{hi}] sep={lo==hi}; front={lo} expected minAdm-1={minAdm_minus1} match={lo==minAdm_minus1}")
    # (D) per-layer diagonal block dets: outputs of layer k vs coords owned by layer k
    out_layer=[]
    for k in range(L):
        for _ in range(A[k].rows*A[k].cols): out_layer.append(k)
    for k in range(L):
        rows=[i for i in range(n) if out_layer[i]==k]
        cols=coords_by_layer.get(k,[])
        if len(rows)!=len(cols):
            print(f"  (D) layer {k}: NON-square diag block ({len(rows)} out vs {len(cols)} coords) — not per-layer-square")
            continue
        Dk = sp.Matrix(len(rows), len(cols), lambda a,b: sp.diff(vec[rows[a]], x[cols[b]]))
        dk = sp.factor(sp.expand(Dk.det()))
        print(f"  (D) layer {k} diag-block det = {dk}")

# ---- M_A = (3,3,3,3), L=3, t_ach=(3,2,1,0) -> Text=[3,3,2,1]. Known det u^5·a^4·δ^2·b^3. NC=27.
def blocks_3333(x):
    i=[1]; nx=lambda: (x[i[0]], i.__setitem__(0,i[0]+1))[0]
    bl={}; cby={}
    bl[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}; cby[0]=[]
    # boundary1: Text1=3,Text2=2 -> B1 3x2 LDU core; N1 2x1; W1 1x3; R1 fixed pivot e33
    a=nx();b=nx();c=nx();d=nx();e=nx();f=nx()  # 6 K-core coords (x1..x6)
    B1=Matrix([[a,a*b],[a*c,a*b*c+d],[a*c*e+a*f,a*b*f+e*(a*b*c+d)]])
    n1a=nx();n1b=nx()  # x7,x8
    N1=Matrix([[n1a],[n1b]]); W1=Matrix([[nx(),nx(),nx()]])  # x9,x10,x11? wait order
    R1=Matrix([[0,0,0],[0,0,0],[0,0,1]])
    bl[1]={'B':B1,'N':N1,'W':W1,'R':R1}
    # boundary2: Text2=2,Text3=1 -> B2 2x1; N2 1x2; W2 2x3; R2 [[0,0,0],[0,eta1,eta2]]
    b2=nx();l2=nx(); B2=Matrix([[b2],[l2*b2]])
    N2=Matrix([[nx(),nx()]]); W2=Matrix([[nx(),nx(),nx()],[nx(),nx(),nx()]])
    R2=Matrix([[0,0,0],[0,nx(),nx()]])
    bl[2]={'B':B2,'N':N2,'W':W2,'R':R2}
    # leaf k=3: Text3=1,W3=3 Rfin 1x3
    bl[3]={'Rfin':Matrix([[nx(),nx(),nx()]])}
    # per-layer coord ownership: assign by debut layer (approx — we check squareness)
    cby[1]=list(range(1,7))+[7,8,9,10,11]   # K-core(6)+N1(2)+W1(3) = 11 ... but layer-1 output A_0 is 3x3=9
    # NB ownership is subtle; we let (D) report non-square if mis-assigned (diagnostic)
    return bl, cby

# ---- M_B = (2,3,2), L=2, t_ach=(1,0) -> Text=[2,1,0]. minAdm=4. NC = flatDim = 2*3+3*2 = 12.
def blocks_232(x):
    i=[1]; nx=lambda: (x[i[0]], i.__setitem__(0,i[0]+1))[0]
    bl={}; cby={}
    # boundary0 identity: Text0=2,Text1=1? NB tach0=M0=2 so Text1 = tach0 = 2; Text(k+1)=tach k.
    # Actually for (2,3,2): tach=(2,1,0) -> Text=[2(=M0), 2? ...]. Use the genM Text: Text0=M0=2,
    #   Text1=tach0=2, Text2=tach1=1, ... wait tach = cons(M0, tStar)=(2, tStar0=1, tStar1=0).
    #   Text(k) for k: Text0=M0=2; Text(k+1)=tach k => Text1=tach0=2, Text2=tach1=1, Text3=tach2=0.
    # So boundary0: Text0=2,Text1=2 (c0=W0-Text1=2-2=0 identity). boundary1: Text1=2,Text2=1
    #   (B1 2x1, c1=W1-Text2=3-1=2). leaf: Text2=1,W2=2.
    # L=2 here (two layers A_0,A_1). M=[2,3,2].
    bl[0]={'B':eye(2),'N':zeros(2,0),'W':zeros(0,3),'R':zeros(2,2)}; cby[0]=[]
    # boundary1: Text1=2,Text2=1 -> B1 2x1 (t=1 core, NO LDU pivot beyond scalar); c1=3-1=2.
    #   N1 1x2; W1 2x3; R1 2x3 (u-carrier, pivot+free).
    b1=nx(); B1=Matrix([[b1],[nx()*b1]])   # 2x1
    N1=Matrix([[nx(),nx()]]); W1=Matrix([[nx(),nx(),nx()],[nx(),nx(),nx()]])
    R1=Matrix([[0,0,0],[0,nx(),nx()]])     # fixed pivot row0=0, free eta in row1? adjust for square
    bl[1]={'B':B1,'N':N1,'W':W1,'R':R1}
    # leaf k=2: Text2=1, W2=2 -> Rfin 1x2
    bl[2]={'Rfin':Matrix([[nx(),nx()]])}
    cby[1]=[]  # diagnostic; report
    print("  (232) coords used:", i[0], "need 12")
    return bl, cby

if __name__=='__main__':
    run("M_A (3,3,3,3)", 3, [3,3,3,3], [3,2,1,0], blocks_3333, 27, 5)
    run("M_B (2,3,2)", 2, [2,3,2], [1,0], blocks_232, 12, 3)  # minAdm-1 = 4-1 = 3
