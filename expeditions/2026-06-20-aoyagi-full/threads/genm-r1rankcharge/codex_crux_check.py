#!/usr/bin/env python3
"""Independent re-check of the two crux sub-claims in the decorrelated Codex answer
   (codex/rankcharge-answer.md). Never trust Codex's argument without running it."""
import io, contextlib
_b=io.StringIO()
with contextlib.redirect_stdout(_b):
    import rankcharge as R
from itertools import product, permutations
minAdm=R.minAdmRec; redChain=R.redChain

# CLAIM 1: the 3-width min  min_{0<=t<=min(A,B)} (A-t)(B-t)+C*t  is SYMMETRIC in A,B,C
#          (basis of Codex's operator-commutation permutation-invariance proof).
def three(A,B,C):
    return min((A-t)*(B-t)+C*t for t in range(min(A,B)+1))
bad1=[(A,B,C,{three(*p) for p in permutations((A,B,C))})
      for A,B,C in product(range(0,8),repeat=3)
      if len({three(*p) for p in permutations((A,B,C))})>1]
bad1b=[(A,B,C) for A,B,C in product(range(0,6),repeat=3) if three(A,B,C)!=minAdm((A,B,C))]
print(f"CLAIM1 3-width symmetric in A,B,C: fails={len(bad1)};  ==minAdm(A,B,C): fails={len(bad1b)}")

# CLAIM 2: Codex's cleaner Q2 chain on cap-active cuts (reference cut u=min(M0,M1) + upper Lipschitz).
bad2=[]
for M in product(range(0,6),repeat=4):
    if len(M)<3: continue
    W=M[2:]; n=min(W); u=min(M[0],M[1]); m=minAdm(M)
    for t in range(u+1):
        if M[1]-t>n:  # cap active
            ok = (minAdm(M) <= minAdm((u,)+W)                       # block charge 0 at t=u
                  and minAdm((u,)+W) <= minAdm((t,)+W)+(u-t)*n      # upper Lipschitz, u>=t
                  and (u-t)*n <= (M[0]-t)*n                          # u<=M0
                  and (M[0]-t)*n + minAdm((t,)+W) >= m)              # => GATE>=
            if not ok: bad2.append((M,t))
print(f"CLAIM2 Codex u-reference Q2 chain on cap-active cuts: fails={len(bad2)}")
