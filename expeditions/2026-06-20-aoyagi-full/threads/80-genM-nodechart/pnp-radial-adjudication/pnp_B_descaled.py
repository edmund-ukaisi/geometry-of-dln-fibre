import sympy as sp
# The CLEANEST constructive B: the SAME decoder/chain, but DROP the pivot scaling on the R/Rfin blocks.
# i.e. B is phi computed with u-scaled blocks read at u=1 on the ACTIVE slots (the E/leaf), but the
# bare-pivot direction handled by reading y_p. Test: B(y) = [phi with each "u*Rblock" replaced by the
# y-coordinate directly, and bare u -> y_p].  Equivalently: build the chart with C_L = Rfin (NO u),
# C_k = Bmat*chainQ + Rmat (NO u) -- the "de-radialized" decoder -- BUT keep the fixed-1 anchor's
# contribution as y_p (the pivot coordinate). Let me test the de-scaled decoder == B at (3,3,3,3).
x = sp.symbols('x0:27', real=True); u=x[0]; active=[13,14,24,25,26]
def chart(scale_u):
    # scale_u: the multiplier on R/Rfin blocks. phi uses scale_u=u; B uses scale_u=1 but reads y-coords.
    B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
    B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
    W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
    R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
    C3=scale_u*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+scale_u*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+scale_u*R1
    A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
    return [sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
phi=chart(u)
# B via the verified formal-inverse construction (the reference)
y=sp.symbols('y0:27',real=True);sub={x[i]:y[i] for i in range(27)};sub[u]=y[0]
for i in active: sub[x[i]]=y[i]/y[0]
Bref=[sp.cancel(e.subs(sub,simultaneous=True)) for e in phi]
# Candidate "de-scaled decoder" B: chart with scale_u = 1 on R-blocks, BUT the fixed-1 anchor in R1[2,2]
#  contributes a bare 1 (not u) -> that's WRONG, we need it to contribute y_p. Hmm. The anchor IS the pivot.
# Actually in B-coords: the bare-pivot term (from the fixed 1 in R/Rfin) must read y_p. The active E/leaf
# terms read y_active. So B = chart where: u*Rblock -> (the Rblock with its FIXED-1 entry replaced by y_p,
# and its FREE entries x_i replaced by y_i). Let me build that.
def chartB():
    B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
    B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
    W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
    yp=y[0]
    # R-blocks: fixed-1 anchor -> yp ; free entries x13,x14 -> y13,y14 ; leaf x24,25,26 -> y24,25,26
    R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,yp]])     # the anchor '1' scaled by u became yp
    R2=sp.Matrix([[0,0,0],[0,y[13],y[14]]])      # free E entries read directly
    Rf=sp.Matrix([[y[24],y[25],y[26]]])          # free leaf entries read directly
    # NOTE: the chain's non-R coords still use x (the spectators/K-core). In B they are y too (identity).
    xt=[y[i] for i in range(27)]
    B1y=B1.subs({x[i]:y[i] for i in range(27)});B2y=B2.subs({x[i]:y[i] for i in range(27)})
    N1y=N1.subs({x[i]:y[i] for i in range(27)});N2y=N2.subs({x[i]:y[i] for i in range(27)})
    W1y=W1.subs({x[i]:y[i] for i in range(27)});W2y=W2.subs({x[i]:y[i] for i in range(27)})
    C3=Rf;C2=B2y*sp.Matrix.hstack(sp.eye(1),N2y)+R2;C1=B1y*sp.Matrix.hstack(sp.eye(2),N1y)+R1
    A0=C1;A1=sp.Matrix.vstack(C2-N1y*W1y,W1y);A2=sp.Matrix.vstack(C3-N2y*W2y,W2y)
    return [sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
Bcand=chartB()
match=all(sp.simplify(Bcand[i]-Bref[i])==0 for i in range(27))
print("de-scaled-decoder B == formal-inverse B (as maps)?", match)
print(" => B is constructively the SAME decoder with: anchor-1 -> y_p, free R/Rfin entries read directly (NO u, NO division).")
