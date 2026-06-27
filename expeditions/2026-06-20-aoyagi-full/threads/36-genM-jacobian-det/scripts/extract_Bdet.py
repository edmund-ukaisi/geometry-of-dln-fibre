# Extract the parametric B_det M pattern from B_det222 (L=2) and B_det3333 (L=3).
# Convention: chain t = tach, Text(0)=M_0, Text(k+1)=tach(k). The achiever descent strictly decreasing.
# At boundary k (1..L-1 interior, k=L leaf): r_k = Text(k)-Text(k+1) (rows dropped), c_k = Wext(k)-Text(k+1)
#   = M_k - Text(k+1) (residual cols). The Schur frame C_k = Bmat_k·chainQ(N_k) + u·Rmat_k.
#   Bmat_k : Text(k) x Text(k+1) (the kept K-rows + X-shear), Rmat_k : Text(k) x Wext(k) (the E-block, u-carrier).
#   The leaf C_L = u·Rfin_L : Text(L) x Wext(L).

# --- B_det222 (M=(2,2,2), tach=(2,1,0), Text=[2,2,1], Wext=[2,2,2]) ---
# boundary k=1: Text1=2,Text2=1 -> r_1=1, c_1=Wext1-Text2=2-1=1. 
#   Bmat 1 = !![x4;x5] (2x1, the kept col), Rmat 1 = !![0,0;0,x6] (2x2, E in bottom-right 1x1=x6).
#   Nblk 1 = !![x1] (1x1), Wblk 1 = !![x2,x3] (1x2).
# leaf k=2: Text2=1, Wext2=2. Rfin 2 = !![1, x7] (1x2): entry (0,0)=FIXED 1, (0,1)=x7.
# So 222: pivot fixed-1 is in the LEAF Rfin 2 at (0,0). The active normals: the E-block x6 (Rmat1), and the
#   leaf x7 (Rfin2 (0,1)), plus the pivot itself. minAdm=3 = 1(E-block) + 2(leaf Rfin 1x2). 
#   Wait: Rfin 2 is 1x2 = 2 entries: (0,0)=1 [pivot], (0,1)=x7 [active]. Plus Rmat1 E-block 1x1=x6 [active].
#   active = {pivot at Rfin(0,0), x7 at Rfin(0,1), x6 at Rmat1 E} -> card 3 = minAdm. radial det |x_p|^{3-1}=|x_p|^2. ✓

# --- B_det3333 (M=(3,3,3,3), tach=(3,2,1,0), Text=[3,3,2,1,0], Wext=[3,3,3,3]) ---
# boundary k=1: Text1=3,Text2=2 -> r_1=1, c_1=Wext1-Text2=3-2=1. Rmat 1 = e_{22} (3x3, bottom-right (2,2)=1 FIXED).
#   So 3333: pivot fixed-1 is in INTERIOR Rmat 1 at (2,2) (the r_1 x c_1 = 1x1 E-block = the FIXED 1).
# boundary k=2: Text2=2,Text3=1 -> r_2=1, c_2=Wext2-Text3=3-1=2. Rmat 2 = !![0,0,0;0,x13,x14] (2x3),
#   E-block bottom-right r_2 x c_2 = 1x2 = (x13,x14) [active].
# leaf k=3: Text3=1, Wext3=3. Rfin 3 = !![x24,x25,x26] (1x3) [all 3 active].
# Aoyagi blocks: j=0:(1,1)→1, j=1:(1,2)→2, j=2:(1,3)→3, sum=6=minAdm. 
#   BUT the chain boundaries: k=1 E-block 1x1 (=fixed 1 pivot), k=2 E-block 1x2 (x13,x14), leaf 1x3 (x24,x25,x26).
#   active = {pivot @ Rmat1 E(2,2)=1, x13,x14 @ Rmat2 E, x24,x25,x26 @ Rfin3} -> 1+2+3 = 6 = minAdm. radial |x_p|^5. ✓
print("=== PATTERN EXTRACTED ===")
print("The active residual normals = the per-boundary E-blocks (Rmat_k bottom-right r_k x c_k) for interior k,")
print("PLUS the leaf Rfin_L (Text(L) x Wext(L)). Total = sum_k r_k*c_k + Text(L)*Wext(L).")
print()
# CHECK: does sum (interior E-blocks r_k c_k) + leaf (Text(L)*Wext(L)) = minAdm = sum Aoyagi r_j c_j?
def check(M, tach):
    L=len(M)-1
    Text=[M[0]]+[tach[k] for k in range(L)]  # Text(0)=M0, Text(k+1)=tach(k)
    Wext=list(M)
    interior = sum((Text[k]-Text[k+1])*(Wext[k]-Text[k+1]) for k in range(1,L))  # k=1..L-1
    # leaf: Text(L) x Wext(L)
    leaf = Text[L]*Wext[L]
    # boundary k=0 is identity (Text0=Text1, r_0=0)
    return Text, interior, leaf, interior+leaf
for M,tach in [((2,2,2),(2,1,0)),((3,3,3,3),(3,2,1,0)),((2,2,1),(2,1,0)),((4,4,2,2),(4,2,2,0)),((3,3,4),(3,1,0))]:
    Text,interior,leaf,tot = check(M,tach)
    print(f"M={M} tach={tach} Text={Text}: interior-E-sum={interior} + leaf(Text_L*Wext_L)={leaf} = {tot}")
