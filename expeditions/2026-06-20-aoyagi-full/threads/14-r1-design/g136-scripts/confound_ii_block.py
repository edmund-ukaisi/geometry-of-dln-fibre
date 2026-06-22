# SHARPEST undershoot: the terminal residual smooth-block. g34-g35 caveat (B): n_block must = Mval(t_leaf),
# the FULL transverse block. If an implementation counts only a LAST LOCAL summand (a sub-block), n_block
# could be < minAdm => ratio n_block/2 < ½·minAdm => UNDERSHOOT. Is the full block always >= minAdm,
# and can a partial-block reading actually occur (the real trap)?
from fractions import Fraction as F
def adm(M):
    L=len(M)-1; out=[]
    def rec(j,prev,cur):
        if j==L+1:
            if cur[-1]==0: out.append(tuple(cur[1:]))
            return
        for v in range(0,min(prev,M[j])+1): rec(j+1,v,cur+[v])
    rec(1,M[0],[M[0]]); return out
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); s=0
    for j in range(1,L+1): s+=(tt[j-1]-tt[j])*(M[j]-tt[j])
    return s

# The terminal block for a branch reaching stratum t_leaf is the L=1 base case ‖reduced C‖^2, a smooth
# block of (reduced M^1 · reduced M^2) squares. For the DEEPEST branch (t=0..0), the base case is the
# bottom reduced chain. n_block = its #entries = Mval(t_leaf) (g34-g35 (B)). Verify n_block >= minAdm
# by checking the base-case block dim equals the FULL terminal Mval, which >= minAdm by definition.
# The trap is ONLY if n_block is read as a sub-block. The MATH fact: full block = Mval(t_leaf) >= minAdm.
print("=== terminal smooth-block dim = Mval(t_leaf) >= minAdm (full block); sub-block reading = the trap ===")
for M in [[2,2,2],[3,3,3],[4,3,2],[3,1,3],[2,2,2,2],[5,4,3,2]]:
    advs=adm(M); minAdm=min(Mval(M,t) for t in advs)
    # terminal blocks: for each leaf branch, n_block = Mval(terminal t). The smallest terminal Mval >= minAdm.
    block_dims=sorted(set(Mval(M,t) for t in advs))
    print(f"M={M}: minAdm={minAdm}  terminal-block-dims(=Mval(t))={block_dims}  "
          f"min-block={min(block_dims)} >= minAdm? {min(block_dims)>=minAdm}")
print("\n=> FULL terminal block always >= minAdm (it IS some Mval(t), and minAdm = min). NO undershoot")
print("   IF the full block is taken. The trap is an IMPLEMENTATION reading a sub-block (scoped condition).")

# But is there a case where a smooth-block ratio EQUALS minAdm but is NOT the binding stratum-divisor,
# i.e. the block is the binding object? On (2,2,2) the δ-block (n=4) has ratio 2 > 3/2 (binding is the
# s-exceptional stratum divisor). When would a block BIND (be the min)? Only if minAdm is achieved by a
# terminal block rather than a stratum divisor -- which is fine (still = minAdm/2). No undershoot either way.
