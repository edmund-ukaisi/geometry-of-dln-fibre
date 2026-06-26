import numpy as np

# Config: L=2, r=1, H0=1, Hmid=1, H2=H_last=2, pivot J maps 0 -> column 1 (non-front).
# We test the claim: does reindex(rThr, pivotThr J)(prod framedParamsPivot) have the SAME
# residual blocks as reindex(rThr, pivotThr J)(P0 (prod symm w) QL)?  (conjunct b of hproducer)
#
# We model the LAST-layer fact established by hS1' (verdict):
#   F_1 = Pf_1 deepest_1 Qf_1 + Pf_1 colPerm_J(deviation_1) Qf_1
# and the non-last layer F_0 = Pf_0 A_0 Qf_0 exactly.
# For L=2 prod = A_0 (first, H0 x Hmid) * A_1 (last, Hmid x H2). Repo `prod` = ordered product.
# Endpoint telescope (clean) gives prod(framedParamsPivot) = P0 * (A_0 * colPerm_J(A_1)) * QL... but
# the colPerm acts on A_1's H2 (output) columns. Let's just build it concretely.

r = 1
H0, Hmid, H2 = 1, 1, 2

# rThr split off first r columns. pivotThr J: left block = sorted pivot columns (here {1}), right = {0}.
# So pivotThr.symm(inl 0) = column 1, pivotThr.symm(inr 0) = column 0.
# pi_J(j) = rThr.symm(pivotThr(j)).  rThr.symm(inl 0)=col0, rThr.symm(inr 0)=col1.
# pivotThr(col0)=inr0 -> rThr.symm(inr0)=col1 ; pivotThr(col1)=inl0 -> rThr.symm(inl0)=col0.
# So pi_J = swap (0<->1).
piJ = [1, 0]   # pi_J(0)=1, pi_J(1)=0

def colPerm(M, perm):
    # colPerm(M)(i,j) = M(i, perm[j])
    return M[:, perm]

# permutation matrix P_pi with colPerm(M)=M @ Ppi : (M@Ppi)[i,j] = sum_k M[i,k] Ppi[k,j] = M[i, perm[j]]
# => Ppi[k,j] = 1 iff k = perm[j].
Ppi = np.zeros((H2, H2))
for j in range(H2):
    Ppi[piJ[j], j] = 1
# check colPerm(M) == M @ Ppi
Mtest = np.array([[3.0, 7.0]])
assert np.allclose(colPerm(Mtest, piJ), Mtest @ Ppi)

# reindex(rThr, eCol)(M): row reindex by rThr (identity here since H0=1, r=1 trivial),
# col reindex eCol: result[:, inl/inr] reads source col eCol.symm(.).
# We represent a reindex on columns as a column permutation matrix applied on the right's INVERSE...
# reindex eCol M (i, c) = M(i, eCol.symm(c)). In block order [inl(0..r-1), inr(0..)], column slot:
# pivotThr: slot0 -> col1, slot1 -> col0.   threshold rThr: slot0 -> col0, slot1 -> col1.
def reindex_cols(M, colmap):
    # colmap[slot] = source column index. result columns in slot order.
    return M[:, colmap]

pivot_colmap = [1, 0]   # slot0<-col1 (the pivot), slot1<-col0
thr_colmap   = [0, 1]

# Build a generic clean product Mclean = P0 (A0 A1) QL  (H0 x H2). Use generic numbers.
np.random.seed(1)
Mclean = np.random.randn(H0, H2)   # the "P0 prod(symm w) QL" minus B already handled abstractly; generic.

# deepestEFull reads reindex(rThr, pivotThr J)( prod(framedParamsPivot) ).
# prod(framedParamsPivot) = clean product but with the LAST layer's H2 columns colPerm'd by pi_J,
# THEN right-multiplied by QL. Model: Mfull_preQL = colPerm_J(Mbase) where Mbase is the product with
# clean last layer; but QL is applied after colPerm inside the last factor.
# Simplify to the essential structure Codex flagged: Mfull = colPerm_J(Mclean_noQL) @ QL, with QL nontrivial.
QL = np.array([[2.0, 1.0],[0.0, 3.0]])   # nontrivial unit on H2
Mclean_noQL = np.random.randn(H0, H2)
Mclean = Mclean_noQL @ QL
Mfull  = colPerm(Mclean_noQL, piJ) @ QL

# Now compare residual blocks under pivot reindex.
Mfull_pivot  = reindex_cols(Mfull,  pivot_colmap)
Mconj_pivot  = reindex_cols(Mclean, pivot_colmap)

print("Mfull  pivot-reindexed:", Mfull_pivot)
print("Mconj  pivot-reindexed:", Mconj_pivot)
# residual energy: r=1, H0=1 so toBlocks11 is (1x1), toBlocks12 is (1 x (H2-r)=1), toBlocks21 empty (H0-r=0).
# Sreg(full) = (toBlocks11 - 1)^2 + toBlocks12^2 ; Sreg(conj) likewise.
def sreg(M):
    b11 = M[0,0]; b12 = M[0,1]
    return (b11-1)**2 + b12**2
print("Sreg from deepestEFull (pivot reindex of Mfull) :", sreg(Mfull_pivot))
print("Sreg from hconj blocks  (pivot reindex of Mconj):", sreg(Mconj_pivot))
print("MATCH (conjunct b holds)?", np.isclose(sreg(Mfull_pivot), sreg(Mconj_pivot)))

# Codex's identity: reindex(rThr,pivotThr)(colPerm M) = reindex(rThr,rThr)(M). Check WITHOUT QL:
lhs = reindex_cols(colPerm(Mclean_noQL, piJ), pivot_colmap)
rhs = reindex_cols(Mclean_noQL, thr_colmap)
print("Codex identity (no QL): reindex(pivot)(colPerm M) == reindex(thr)(M)?", np.allclose(lhs, rhs))
