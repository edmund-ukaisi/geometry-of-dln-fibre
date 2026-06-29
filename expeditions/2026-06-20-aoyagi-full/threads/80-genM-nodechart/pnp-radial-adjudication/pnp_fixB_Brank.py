import sympy as sp
# B in w-coords (leaf-only blowup split): out values
wu,wK,wX,wN,wW0,wW1,wlf0,wlf1 = sp.symbols('wu wK wX wN wW0 wW1 wlf0 wlf1', real=True)
wv=[wu,wK,wX,wN,wW0,wW1,wlf0,wlf1]
# B = chart in w with E(0,0)=wu (additive), leaf = wlf (NOT scaled): 
B=[wK, wK*wN, wK*wX, wK*wN*wX + wu, -wN*wW0 + wlf0, -wN*wW1 + wlf1, wW0, wW1]
JB=sp.Matrix(B).jacobian(sp.Matrix(wv))
print("B outputs:", B)
print("det DB =", sp.factor(JB.det()))
# WHY 0? out[3]=wK wN wX + wu has d/dwu=1. out[4],[5] have d/dwlf=1. So wu,wlf are independent. 
# The issue: wX appears in out[2]=wK wX and out[3]. wN in out[1],[3],[4],[5]. Let me see the rank.
print("rank of JB (generic):", JB.subs({v:sp.Rational(i+2,3) for i,v in enumerate(wv)}).rank())
# 8 cols, if rank<8 -> singular. Find which output is missing a free direction:
# Outputs: K(wK), KN(wK,wN), KX(wK,wX), KNX+u(wu...), -NW0+lf0(wN,wW0,wlf0), -NW1+lf1, W0(wW0), W1(wW1).
# 8 outputs, 8 inputs. Is wX recoverable? out[2]=wK*wX -> wX = out2/wK (needs wK!=0, fine). 
# Hmm should be rank 8. Let me see the actual det expansion.
print("det DB expanded:", sp.expand(JB.det()))
