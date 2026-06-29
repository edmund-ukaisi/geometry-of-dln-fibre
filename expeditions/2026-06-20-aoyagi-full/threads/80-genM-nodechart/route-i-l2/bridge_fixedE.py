import sympy as sp
print("Does phiFlatLiveR1 M222 (FIXED-E genBlkFlatLiveR1) factor as B ∘ pivotBlowupOn (faithful)?")
# φ = phiGen u (genBlkFlatLiveR1 x) for M222. The chart layers A0,A1 from Cgen/Agen.
# Coords: the slot-readers. Use abstract slot names matching genBlkFlatLiveR1's reads at M222.
# Boundary k=1: Bmat1 = bmatStack(K,X) where K=readK(1) (Text2×Text2 = 1x1 = [k]), X=readX (r1×Text2=1x1=[xx]).
#   bmatStack = [K ; X·K] = [[k],[xx·k]] (2x1). Nblk1 = readN = [n] (1x1). Wblk1 = readW... but L=2 so k+1=2 not <L → Wblk1=0? 
# Hmm at L=2, boundary 1 is the LAST genuine boundary; Wblk reads only for k+1<L. L=2 ⟹ k=1: 1+1=2 NOT <2 ⟹ Wblk1=0.
# Wait that can't be right for a 2x2 chart. Let me reconsider: M222: Fin 3, L=2. Boundaries k∈{0,1}. k=0 identity, k=1 genuine.
# Agen 0 = chainA(Nblk0,Wblk0,Cgen1); Agen 1 = chainA(Nblk1,Wblk1,Cgen2=leaf). 
# Cgen2 = u·Rfin2 (leaf, live). Agen1 = chainA(Nblk1, Wblk1, u·Rfin2).
# This matches the B_det222 structure (W1 = [x2,x3] = Wblk1, Rfin2 = live leaf). So Wblk1 is NOT 0 — readW(1) needs 1+1<L?
# At L=2: readW k needs k+1<L i.e. k<1, so k=0 only. Boundary 1 has NO readW ⟹ Wblk1 from genBlkFlatStruct = 0??
# But B_det222 HAS Wblk1=[x2,x3]. So B_det222 ≠ genBlkFlatLiveR1 structurally at Wblk too?! Let me just compare the CHARTS.
# Simplest: compute Agen for genBlkFlatLiveR1 M222 symbolically using the Cgen/Agen recursion + the genBlkFlatStruct reads.
# genBlkFlatStruct M222 blocks at the slot-reader coords (k=1): Bmat1=bmatStack(K,X), Nblk1=readN, Wblk1=readW(=0 at L=2!), Rmat1=rmatPad(readE).
# genBlkFlatLiveR1: Rmat1 → rmatPad(pivotEIndicator)=fixed; Rfin2 → live rfin.
# KEY uncertainty: is Wblk1=0 at L=2 (no readW)? If so the chart is DEGENERATE vs B_det222 (which has W1≠0).
print("CRITICAL: at L=2, readW k needs k+1<L (k<1), so boundary k=1 has Wblk1=0 (no lift).")
print("But B_det222 has Wblk1=[x2,x3]≠0. So B_det222 and genBlkFlatLiveR1 DIFFER STRUCTURALLY (Wblk),")
print("not just the gauge-slot. → phi222 ≠ phiFlatLiveR1 M222 even up to relabeling. BRIDGE = they are")
print("DIFFERENT charts; the (2,2,2) pack/T template is for B_det222, NOT phiFlatLiveR1 M222.")
