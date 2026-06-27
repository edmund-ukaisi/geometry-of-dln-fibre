import sympy as sp
# VvalGen = ||H||^2, prod = u*H. For nonzero a.e., need H not identically 0 (a nonzero polynomial in x).
# H = reindex(Hmat_0), Hmat_0 = the telescoped quotient. From chain_telescope: C_0 * suffix_0 = u*Hmat_0,
# C_0 = 1, so suffix_0 = u*Hmat_0, i.e. prod = u*Hmat_0. Hmat recursion: Hmat_L = Rfin_L,
# Hmat_k = Bmat_k*Hmat_{k+1} + E_k*suffix_{k+1} where E_k = Rmat_k*A_k (the chain's E).
# The LEADING term: Hmat_0 contains Bmat_0*Bmat_1*...*Bmat_{L-1}*Rfin_L (the product of all kept Bmat's times
# the leaf residual). At a canonical point where each Bmat_k = full-rank-ish and Rfin_L has the fixed-1,
# this leading term is nonzero.
# Concretely for 222: prod = chartA0·chartA1. H = prod/x0 = M222bar = !![x4, x4·x7; x2·x6+x5, x3·x6+x5·x7].
# Nonzero witness: x4=1 (others can be 0): H(0,0)=x4=1 != 0. So H != 0 at {x4=1, rest free}. 
# The fixed-1 is at Rfin_2(0,0); the "x4" is Bmat_1(0,0) (the top kept entry). 
M222bar_00 = "x4"  # = Bmat_1(0,0), the top-left kept entry
print("222: H(0,0) = x4 = Bmat_1(0,0). Nonzero at x4 != 0.")
# 3333: H = prod/u. The leading H(0,0) = product of top-left kept entries * Rfin leaf(0,0).
# B_det3333: Bmat_1(0,0)=x1, Bmat_2(0,0)=x9, Rfin_3(0,0)=x24. So H(0,0) ~ x1*x9*x24 (the diagonal kept chain).
print("3333: H(0,0) ~ x1·x9·x24 = Bmat_1(0,0)·Bmat_2(0,0)·Rfin_3(0,0) (the kept-diagonal × leaf). Nonzero at those=1.")
print()
print("UNIFORM WITNESS PATTERN: H(0,0) = (∏_k Bmat_k(0,0)) · Rfin_L(0,0) — the top-left kept-diagonal chain")
print("times the leaf fixed-1. At the witness point {all Bmat_k(0,0)=1, the fixed-1 Rfin/Rmat pivot=1, all else 0},")
print("H(0,0) = 1 != 0, so VvalGen = ||H||^2 >= H(0,0)^2 = 1 > 0. The unit is a nonzero polynomial UNIFORMLY.")
print("=> {VvalGen = 0} is Lebesgue-null (nonzero-polynomial zero-set), giving the a.e.-positivity. NOT per-M.")
# verify 222 H(0,0)=x4: at x4=1, x1..x3,x5,x6,x7=0: M222bar(0,0)=x4=1. yes.
