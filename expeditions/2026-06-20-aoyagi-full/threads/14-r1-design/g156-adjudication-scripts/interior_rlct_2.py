import sympy as sp, itertools
def admissible(M):
    Ln=len(M)-1
    bounds=[min(M[0],M[1]) if j==1 else M[j] for j in range(1,Ln+1)]
    rngs=[range(b+1) for b in bounds[:-1]]+[[0]]
    for T in itertools.product(*rngs):
        if all(T[i]>=T[i+1] for i in range(Ln-1)): yield T
def mval(M,T):
    tot=0; prev=M[0]
    for j,t in enumerate(T,1): tot+=(prev-t)*(M[j]-t); prev=t
    return tot
def minAdm(M): return min(mval(M,T) for T in admissible(M))

print("="*78)
print("Does the deepest point STRICTLY beat interior strata, and never reverse?")
print("Local rlct at a rank-rho point of dlnLoss(M) = (1/2)·minAdm of the rank-rho-reduced problem.")
print("The rank-rho stratum: product has rank rho; the reduced problem fixes rho units, reduces widths.")
print("="*78)
# Aoyagi/LR rank-stratification: at a point where the product B=A0...AL has rank exactly rho,
# the loss ||A0...AL - B0||^2 locally looks like the rank-rho slice; the local minAdm is the
# minAdm of the chain with the FIRST rho 'units' pinned (T_1 >= rho forced). Concretely the local
# codim at a rank-rho point is min over admissible T with the rho already-achieved units.
# The DEEPEST point = rank 0 (B=0): T ranges over ALL admissible (no forced units) => the FULL min.
# A rank-rho>0 point: the relevant codim is the minAdm of the residual after rho ranks resolved,
# which is the minAdm of the (M0-rho, M1-rho, ..., reduced) chain -- a SMALLER, less-constrained
# problem => its minAdm-as-local-codim is >= the rank-0 minAdm? Let's TEST numerically:
# local codim at rank-rho = minAdm with t_1 starting from rho (the running profile pinned >= rho).
def mval_pinned(M, T):  # T is the full profile incl. the pinned first entry
    tot=0; prev=M[0]
    for j,t in enumerate(T,1): tot+=(prev-t)*(M[j]-t); prev=t
    return tot
def local_codim_rank(M, rho):
    # admissible profiles with t_1 = rho EXACTLY pinned at the deepest layer? 
    # Actually the cleaner model: a rank-rho point of the product means rho 'diagonal' units are
    # already nonzero/resolved; the residual singular block is the (M0-rho,M1-rho,...,M_{L+1}) chain
    # at its OWN deepest (all-zero) point. So local codim = minAdm of the rho-reduced chain.
    Mred = [max(m-rho,0) for m in M[:-1]] + [M[-1]]  # reduce all but tail by rho? 
    # NB: only the rank flows; tail width M_{L+1} is fixed. Reduce M0..M_L by rho (rank can't exceed widths).
    Mred = [max(M[i]-rho,0) for i in range(len(M)-1)] + [M[-1]]
    return minAdm(Mred)

for M in [[2,2,1],[2,2,2],[3,3,2],[3,3,3],[2,2,4],[3,2,5]]:
    base = minAdm(M)
    maxrho = min(M[:-1])
    locs = [(rho, local_codim_rank(M,rho)) for rho in range(maxrho+1)]
    worst = min(c for _,c in locs)
    print(f"M={M}: minAdm(deepest,rho=0)={base}; rank-strata codims {locs}; "
          f"global-min over strata={worst}; deepest-is-min? {base==worst}")
