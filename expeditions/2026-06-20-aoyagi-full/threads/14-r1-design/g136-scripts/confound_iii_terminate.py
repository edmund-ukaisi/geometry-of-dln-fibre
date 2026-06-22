# CONFOUND (iii): does ΣM strictly drop at every non-terminal Schur step, for ALL chain shapes?
# The Schur step: first factor M^1 x M^2 with a hard-1 pivot -> reduced first factor (M^1-1)x(M^2-1),
# the next factor restricted to (M^2-1) rows. Reduced chain widths M' = (M^1-1, M^2-1, M^3, ..., M^{L+1}).
# ΣM' = ΣM - 2. So ΣM drops by EXACTLY 2 each Schur step. Termination = clear... UNLESS a width hits 0
# or 1 pathologically, or the chain can't peel. Hunt the stuck cases.
def schur_reduce(M):
    # one Schur step: requires M^1>=1, M^2>=1 with a nonzero pivot (rank>=1). Reduced: (M1-1,M2-1,M3,..).
    if len(M)<2: return None
    M1,M2=M[0],M[1]
    if M1<1 or M2<1: return None
    Mp=[M1-1, M2-1]+list(M[2:])
    return Mp

# Hunt: chains where reduction produces a 0-width (collapse) or fails to reduce sum.
print("=== ΣM drop per Schur step (should be -2) + termination over chain shapes ===")
bad=[]
for M in [[2,2,2],[3,3,3],[1,3,1],[1,1,1],[5,1,5],[2,1,2],[1,5,1],[3,1,1,3],[1,2,1,2,1],[2,2,1]]:
    chain=[tuple(M)]
    cur=list(M); steps=0; stuck=False
    # descend: each step peels first factor while L>=2 (more than 2 widths) and ranks allow
    while len(cur)>2 and steps<50:
        nxt=schur_reduce(cur)
        if nxt is None or sum(nxt)>=sum(cur): stuck=True; break
        # if a width hit 0, the layer collapses -> the chain terminates (that factor is rank 0)
        if 0 in nxt[:-1] or 0 in nxt[1:]:
            # a 0 interior width means the product is forced 0 / chain degenerates -> terminal
            chain.append(tuple(nxt)); break
        cur=nxt; chain.append(tuple(cur)); steps+=1
    dropok = all(sum(chain[i+1])<sum(chain[i]) for i in range(len(chain)-1))
    if stuck or not dropok: bad.append(M)
    print(f"M={M}: descent={chain}  ΣM_strictly_drops={dropok}  stuck={stuck}")
print("\nSTUCK or NON-DROPPING chains:", bad or "NONE")

# The KEY edge: a width-1 layer. (1,3,1): first factor 1x3 (a row), hard pivot at (0,0)=1, Schur is
# 0x2 (empty!). So the reduced first factor is EMPTY -> the chain TERMINATES (no more rank to drop).
# Is that sound? (1,3,1): product is 1x1 scalar = sum of 3 products; {prod=0} is a hypersurface, codim 1.
# minAdm Mval(1,3,1)=1, rlct=1/2. The L=1 base case ‖C1‖^2 with C1 1x3 = 3 squares => but that's the
# WRONG base if we peeled. Check: does the recursion bottom correctly for width-1 chains?
print("\n(1,3,1) edge: first factor 1x3, hard-1 pivot => Schur 0x2 EMPTY => chain terminates immediately.")
print("  minAdm Mval(1,3,1) = 1 => rlct should be 1/2. The single blow-up of {C1=0}? C1 is 1x3...")
