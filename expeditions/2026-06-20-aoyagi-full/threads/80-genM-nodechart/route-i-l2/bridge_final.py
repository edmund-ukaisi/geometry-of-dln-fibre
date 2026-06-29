import sympy as sp
print("BRIDGE (corrected, against actual genBlkFlatStruct): phiFlatLiveR1 M222 factors as B ∘ pb?")
# genBlkFlatLiveR1 M222 boundary-1 blocks (genBlkFlatStruct + fixed pivot Rmat + live leaf):
#   Bmat1 = [[k],[xx*k]]? No — bmatStack(K,X) with K=readK(1×1)=[a], X=readX(1×1)=[b]: [K;X·K]=[[a],[b·a]] (2x1).
#   Actually B_det222 Bmat1=[[x4],[x5]] is NOT [a; b·a] form — so B_det222 ≠ bmatStack literally; it's the
#   EXPLICIT achiever (sympy-matched) chart, a SPECIFIC point-family. genBlkFlatLiveR1 uses bmatStack(readK,readX).
# The two are the SAME chart at the achiever WITNESS but genBlkFlatLiveR1 is the GENERAL slot-reader decoder.
# For the BRIDGE we need: does phiFlatLiveR1 M222 = B ∘ pb for a faithful u-free B? Test with genBlkFlatLiveR1's
# ACTUAL blocks (bmatStack form), fixed-E pivot, live leaf:
u = sp.Symbol('u'); a,b,n,w0,w1,lf0,lf1 = sp.symbols('a b n w0 w1 lf0 lf1')  # readK=a,readX=b,readN=n,readW=[w0,w1],leaf rfin=[lf0,lf1]
K = sp.Matrix([[a]]); X = sp.Matrix([[b]]); N = sp.Matrix([[n]]); W = sp.Matrix([[w0,w1]])
Bmat1 = sp.Matrix([[a],[b*a]])          # bmatStack(K,X) = [K; X·K]
qN1 = sp.Matrix([[1, n]])                # chainQ(N): [I|N], 1x2
Rfix = sp.Matrix([[0,0],[0,1]])          # rmatPad(pivotEIndicator): fixed 1 at residual (0,0)→bottom-right pad
C1 = Bmat1*qN1 + u*Rfix                   # = [[a, a·n],[b·a, b·a·n + u]]
# Cgen2 (leaf) = u·Rfin = u·[lf0, lf1] (1x2)
C2 = u*sp.Matrix([[lf0, lf1]])
# Agen1 = chainA(N1, W1, C2) = [C2 - N·W ; W]  (kept row 0 = C2 - N·W, lift = W). t=Text2=1,c=Wext1-Text2=1,m'=Wext2=2
A1 = sp.Matrix.vstack(C2 - N*W, W)        # 2x2: [[u·lf0 - n·w0, u·lf1 - n·w1],[w0, w1]]
# Agen0 = chainA(N0,W0,C1) at boundary 0 (identity, c0=0): = C1 (N0:2x0). A0 = C1 (2x2).
A0 = C1
print("A0 =", A0.tolist()); print("A1 =", A1.tolist())
# The chart φ = paramsEquivFlat ∘ (A0,A1). Does it factor B ∘ pb with pb the radial blow-up of the u-coords?
# u multiplies: the fixed pivot (the '+u' in A0[1,1]) and the leaf lf0,lf1 (in A1). 
# Radial active = {pivot} ∪ {lf0,lf1}? The fixed-pivot '+u' is the ADDITIVE term — same affine question.
# But RESOLVED: in the COMPOSITE, treat u as the radial coordinate; the '+u' at A0[1,1] is u read DIRECTLY
# (the pivot coord), and lf0,lf1 are u-scaled (multiplicative). So φ's u-structure:
phi = [A0[0,0],A0[0,1],A0[1,0],A0[1,1], A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
print("φ entries with u:", [e for e in phi if u in sp.sympify(e).free_symbols])
# A0[1,1] = b·a·n + u (u ADDITIVE, coeff 1 — the gauge pivot); A1[0,*] = u·lf - n·w (u MULTIPLICATIVE on lf).
print("→ u appears: ADDITIVELY at A0[1,1] (the fixed-pivot gauge, +u·1); MULTIPLICATIVELY at A1[0,*] (u·leaf).")
print("This is the SAME structure as the affine-radial resolution: the additive +u is the pivot COORD")
print("(blown up multiplicatively by pb as the pivot direction); leaf u·lf are the scaled actives.")
print("So phiFlatLiveR1 M222 has the SAME u-structure as the (2,2,2) template (T222: u0 the radial coord).")
