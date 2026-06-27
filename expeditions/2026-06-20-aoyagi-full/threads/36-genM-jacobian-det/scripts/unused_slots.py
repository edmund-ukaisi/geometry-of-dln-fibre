# The structural degeneracy is decoder-level. genBlkFlatStruct reads N flat coords into ChartIdx role slots
# (schurDim k + liftDim k for k in Fin L). The schur slot at k=L-1 feeds readK/X/N/E at k=L-1, which the decoder
# places into Bmat(L), Nblk(L), Rmat(L). But Cgen/Agen only read indices k < L. So Bmat(L)/Nblk(L)/Rmat(L) are
# NEVER used. Therefore schurDim(L-1) flat coords are DEAD (don't appear in output).
# schurDim(L-1) = tDesc(L-1)*Wext(L) = Text(L)*Wext(L) = Text(L)*M(L).
# These are >0 whenever Text(L)>=1 and M(L)>=1, i.e. ALWAYS for a genuine chain. So the decoder ALWAYS has
# >= Text(L)*M(L) dead coords => Jacobian always rank-deficient => det=0 identically. GENERIC, not (2,2,2)-specific.
for M,Text in [((2,2,2),[2,2,1,1]),((4,4,2,2),[4,3,2,2,2]),((3,3,4),None),((3,3,3,3),None)]:
    if Text:
        L=len(M)-1
        dead = Text[L]*M[L]
        print(f"M={M}, Text={Text}: dead leaf coords = Text(L)*M(L) = {Text[L]}*{M[L]} = {dead} (>0 => det=0)")
print()
print("Also: Rfin:=0 means C_L = u*Rfin(L) = 0 (leaf transition zero). The leaf factor of the chain is 0,")
print("which is consistent with the dead slots. The decoder genuinely cannot produce a full-rank chart.")
