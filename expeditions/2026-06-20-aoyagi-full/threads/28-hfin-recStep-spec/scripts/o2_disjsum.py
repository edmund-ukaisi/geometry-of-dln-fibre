import sympy as sp
import numpy as np
from numpy.random import default_rng

# ============================================================
# The DISJOINT-SUM mechanism: how the recursion realizes jp/2 + lambda_{r-j,p}.
# D(R,S) = frobSq((R*S)_top) + frobSq(Sc*S_bot)   -- a SUM of two terms.
# After the det-1 S-reparam, (R*S)_top depends on S_top (j*p Morse vars, AFFINE in S_top) and S_bot;
# Sc*S_bot depends ONLY on S_bot.  The disjoint groups: S_top (Morse) | S_bot (Sc-core).
#
# Watanabe disjoint-sum additivity: rlct(f(x)+g(y)) = rlct(f)+rlct(g)  for disjoint x,y.
# At the FINITENESS level (what hfin needs), the mechanism is:
#   ∫_{S_top,S_bot} (A(S_top,S_bot) + W(S_bot))^{-c'} dS  where A = frobSq((R*S)_top) is a nondeg
#   quadratic in S_top (the Morse block), W = frobSq(Sc*S_bot) the Sc-core.
# This is NOT a pure product. The threshold of the SUM is rlct(A)+rlct(W) = jp/2 + lambda(Sc-core).
# Realized by: integrate S_top FIRST (Morse, gives ~ W^{(jp/2 - c')}-ish weight? NO).
# Actually the clean realization (the L1.1 radial_morse_dominates does the UPPER bound only up to
# the Morse threshold, dropping W -- that's the r=2 case where lambda(Sc-core)=lambda_{0}=0!).
# For r=2: Sc is SCALAR (1x1), lambda_{1,p}=... wait r-j=1, lambda_{1,p}=min(1/2, p/2)=1/2.
# Hmm but depth2 proof DROPS W=Sc00^2*sum(S_bot^2) using W>=0, giving threshold jp/2=4/2=2 (=lambda_{2,4}).
# Let me recompute: r=2,p=4,j=1: jp/2 = 1*4/2 = 2 = lambda_{2,4}. And lambda_{1,4}=1/2.
# ADD = jp/2 + lambda_{1,4} = 2 + 1/2 = 5/2.  But lambda_{2,4}=2 (a-div binds!). So at (2,4) the
# a-divisor r^2/2=2 binds, NOT the ADD 5/2. The depth2 Sc-core is NOT binding -> can be DROPPED. THAT's
# why depth2 works by dropping W. Let me check: is the Sc-core EVER binding at the corank where it first
# appears as a non-scalar (r=3)?
print("=== When is the Sc-core (the recursion) actually BINDING (not droppable)? ===")
from functools import lru_cache
@lru_cache(maxsize=None)
def lam(r,p):
    if r==0: return sp.Rational(0)
    return min([sp.Rational(r*r,2)] + [sp.Rational(j*p,2)+lam(r-j,p) for j in range(1,r+1)])

for (r,p) in [(2,4),(3,4),(3,3),(3,5),(4,4)]:
    L = lam(r,p)
    adiv = sp.Rational(r*r,2)
    # the binding j and whether the SC-CORE (lambda_{r-j,p}) part is nonzero
    print(f" (r={r},p={p}): lambda={L}, a-div={adiv}", end="  ")
    for j in range(1,r+1):
        add = sp.Rational(j*p,2)+lam(r-j,p)
        if add == L and lam(r-j,p) > 0:
            print(f"-> j={j} BINDS with NONZERO Sc-core lambda_{{{r-j},{p}}}={lam(r-j,p)} (ADD load-bearing, Morse can't drop core)", end="")
    print()

print()
print("So at (3,4): j=1 binds, ADD = jp/2(=2) + lambda_{2,4}(=2) = 4 = lambda_{3,4}.")
print("The Sc-core lambda_{2,4}=2 is NONZERO and BINDING. Dropping it (Morse-only, threshold jp/2=2)")
print("UNDERSHOOTS lambda_{3,4}=4. So at corank-3 the recursion GENUINELY fires: the Sc-core must be")
print("integrated, not dropped. This is the FIRST corank where O2 has real content. CONFIRMED.")
