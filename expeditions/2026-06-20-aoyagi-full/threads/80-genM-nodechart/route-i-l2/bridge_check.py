import sympy as sp
print("="*72); print("BRIDGE: phi222 (B_det222, free-E pivot) vs phiFlatLiveR1 M222 (genBlkFlatLiveR1, fixed-E)"); print("="*72)
# Both are phiGen (radial=u) M222 tach222 (decoder x) hle, differing in the decoder.
# tach222=(2,1,0): Text=[2,2,1,...] wait Text M222 tach222: T0=t0=2, T1=t1=1? Let me use the banked: Text222_0=2,_1=2,_2=1.
# Boundary k=1 (the genuine boundary). Text1=2,Text2=1. r1=Text1-Text2=1, c1=Wext1-Text2=2-1=1. E-block 1x1.
# Cgen for k=1: C1 = Bmat1 · chainQ(Nblk1) + u·Rmat1.  Bmat1 = [[x4],[x5]] (2x1). Nblk1=[x1] (1x1).
#   chainQ(Nblk1): t=Text2=1, c=Wext1-Text2=1, M'=Wext1=2 → [I_1 | N] = [1, x1] (1x2).
#   Rmat1 (B_det222) = [[0,0],[0,x6]]. Rmat1 (genBlkFlatLiveR1) = rmatPad(pivotEIndicator) at p=1 = [[0,0],[0,1]] (E(0,0)=1 of the 1x1 residual, padded bottom-right).
u = sp.Symbol('u')
x1,x2,x3,x4,x5,x6,x7 = sp.symbols('x1 x2 x3 x4 x5 x6 x7')
B1 = sp.Matrix([[x4],[x5]]); qN1 = sp.Matrix([[1, x1]])  # 1x2
# B_det222: C1_free = B1·qN1 + u·[[0,0],[0,x6]]
C1_free = B1*qN1 + u*sp.Matrix([[0,0],[0,x6]])
# genBlkFlatLiveR1: C1_fix = B1·qN1 + u·[[0,0],[0,1]]  (E(0,0)=1 padded to bottom-right of 2x2)
C1_fix = B1*qN1 + u*sp.Matrix([[0,0],[0,1]])
print("C1 (B_det222, free x6) =", C1_free.tolist())
print("C1 (genBlkFlatLiveR1, fixed 1) =", C1_fix.tolist())
print("→ differ ONLY at (1,1): free has u·x6, fixed has u·1. So phiFlatLiveR1 = phi222 |_{x6 := 1} ... NO:")
print("  the fixed decoder SETS x6's role to 1 AND frees the leaf Rfin to carry a coord. They are")
print("  DIFFERENT decoders: B_det222 reads x6 at E; genBlkFlatLiveR1 fixes E=1, reads a coord at the leaf.")
# leaf: Rfin 2. B_det222: Rfin2 = [1, x7] (the '1' is the fixed leaf anchor, x7 free). 
# genBlkFlatLiveR1: Rfin2 = the LIVE rfin (a free reader) — carries the rerouted x6 budget.
print()
print("VERDICT: phi222 and phiFlatLiveR1 M222 are NOT literally equal — DIFFERENT decoders")
print("(B_det222 = free-E + fixed-leaf-anchor; genBlkFlatLiveR1 = fixed-E + live-leaf). They are the")
print("SAME family with the gauge-fixed '1' relocated (E-slot ↔ leaf-slot). The det/headline is the")
print("same (both achiever charts for the node) but the MAP differs by which slot is gauge-fixed.")
