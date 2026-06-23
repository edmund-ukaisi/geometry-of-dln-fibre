import sympy as sp
# fm3's 3 questions — my cert-author read on the certified-recursion ruling.
#
# Q1: ROOT-ANCHORING confirm — codim = Mval(root M, T), T root-admissible, all down the path. Is the
# geometric codim INVARIANT under the det-1 reduced reindex (so root-anchoring is faithful)?
print("Q1 ROOT-ANCHORING (confirm codim = Mval(root M, T) invariant under the reduced reindex):")
print("  The codim a C1 node contributes = the geometric codim of its blow-up CENTER in the ORIGINAL ambient.")
print("  The Schur-descent reindex (redEmbed: the det-1 reduced reparametrization) is a measure-preserving")
print("  coordinate change — it does NOT move the geometric codim (codim is a c-o-v INVARIANT under det-1 /")
print("  diffeomorphism). So the center's codim, computed in the root ambient, = Mval(root M, T) for the")
print("  rank pattern T the center resolves — INDEPENDENT of how deep in the recursion we are. CONFIRM ✓:")
print("  root-anchoring is faithful BECAUSE geometric codim is reindex-invariant. (My §2/§4 always used")
print("  Mval(root M, T) — the original-ambient geometric codim, NOT Mval(reduced chain).) g207 confirmed.")
print()
# Q2: is schurState a clean PRODUCER DEF? schurState M pivot : ChainDimSplit M = ⟨drop, red, hsum, hdrops⟩.
# My g194 C1 (3,3,2) + g195 (2,2,2): the C1 node = pivotBlowupOn + det-1 Schur peel ⟹ (drop, red).
# The reduced widths: red = schurState's M' = (M_0-1, M_1-1, M_{≥2}) [the ΣM-2 descent]. drop = M - red.
def schurState_split(M, r=None):
    # the C1 reduced-width split: drop_0=drop_1=1 (the ΣM-2 Schur descent), rest 0. red = M - drop.
    L = len(M)-1
    drop = [0]*(L+1); 
    if M[0]>=1 and M[1]>=1: drop[0]=1; drop[1]=1
    red = [M[i]-drop[i] for i in range(L+1)]
    return drop, red
print("Q2 schurState as a clean PRODUCER DEF:")
for M in [(2,2,2),(3,3,2),(3,2,3),(2,2,2,2),(4,3,2)]:
    drop, red = schurState_split(M)
    hsum_ok = all(drop[i]+red[i]==M[i] for i in range(len(M)))
    hdrops_ok = sum(drop)>0
    red_nonneg = all(x>=0 for x in red)
    print(f"  M={M}: drop={tuple(drop)}, red={tuple(red)}; hsum(drop+red=M)={hsum_ok}, hdrops(Σdrop>0)={hdrops_ok}, red≥0={red_nonneg}, Σred<ΣM={sum(red)<sum(M)}")
print()
print("  ⟹ schurState M = ⟨drop=(1,1,0,...), red=(M_0-1,M_1-1,M_{≥2}), hsum, hdrops⟩ IS a clean ChainDimSplit")
print("  M DEF — drop+red=M (hsum), Σdrop=2>0 (hdrops), Σred<ΣM (termination). PRECONDITION M_0,M_1≥1 (the C1")
print("  node; M_0,M_1≥2 for the genuine coupled-defect, else C4/leaf). So YES, definable. BUT (the key):")
print("  the DEF gives the WIDTH split; the SOUNDNESS (Codex g206 item 2) is that split.red MUST equal what")
print("  the pivot blow-up's RESIDUAL actually produces — that's the per-cell DATUM (b), not the width def alone.")
