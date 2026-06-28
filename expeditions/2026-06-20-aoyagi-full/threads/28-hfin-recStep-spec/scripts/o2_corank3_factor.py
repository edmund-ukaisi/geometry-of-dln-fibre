import sympy as sp
import numpy as np

# ============================================================
# corank-3, r=3, j=1. The CRUCIAL recursion step at the FIRST non-trivial corank.
# Verify the inner-S integral factorises (Fubini) into:
#   ∫_S D^{-c'} dS  where D = frobSq((R*S)_top) + frobSq(Sc*S_bot),  (R*S)_top = row-0 (1xp),
#   Sc = 2x2.   The top block is 1 row (j=1), Sc-core is 2 rows (r-j=2).
# Threshold split:  jp/2 + lambda_{2,p}.   For p columns: jp/2 = p/2, lambda_{2,p}=min(4/2, ...).
# Question O2: when we recurse on ∫_{S_bot} frobSq(Sc*S_bot)^{-c'} dS_bot, is the bound
#   UNIFORM in the spectators (M12,M21) and does the R-integral of it stay finite?
# ============================================================

# THE KEY DISTINCTION (the resolution of O2):
# The recursion does NOT integrate over Sc. It integrates over S_bot at a FIXED Sc=Sc(R).
# The IH (corank r-j=2) says: for a corank-2 matrix Sc on a SUITABLE chart,
#   ∫_{S_bot in box} frobSq(Sc*S_bot)^{-c'} dS_bot < inf  for c' < lambda_{2,p}.
# But the IH's chart hypotheses require Sc to be on a pivot-normalized bounded chart.
# Sc(R) as R ranges over the chart is a 2x2 matrix in the box [-2,2]^4 (verified). To apply the IH
# we must RE-COVER the Sc-image by corank-2 charts (re-blowup, R4). That re-cover is a NESTED
# argmax over Sc's entries -- a FRESH corank-2 problem in the variable S_bot, with Sc a PARAMETER.
#
# CRITICAL: the recursion variable at the next level is S_bot (the free block), NOT R or Sc.
# Sc is a fixed coefficient matrix. So there is NO change-of-variables R->Sc at all.
# The IH is a statement about ∫_{S_bot} frobSq(Sc*S_bot)^{-c'} as a function of the COEFFICIENT Sc,
# and the question is whether that integral is BOUNDED UNIFORMLY in Sc over Sc's range.

# Let's TEST: is sup_{Sc in [-2,2]^{2x2}} ∫_{S_bot in box} frobSq(Sc*S_bot)^{-c'} dS_bot  FINITE?
# (If yes, then ∫_R [that integral] <= (R-box vol) * sup < inf, trivially -- NO R-integral subtlety!)
# The danger: as Sc -> singular (det Sc -> 0, or Sc -> 0), the integral can BLOW UP.
# At Sc=0: frobSq(0*S_bot)=0, integral = ∫ 0^{-c'} = +inf.  So sup is NOT finite naively!
# THIS is the real content: the {Sc=0} / {det Sc small} locus. The recursion handles it by
# the RE-BLOWUP: Sc = a'*R', pulling the scale a' out (a SEPARATE radial divisor on the Sc-scale),
# which couples to... what? Sc is a function of R, so a' = (scale of Sc) is a function of R.

print("=== O2 RESOLVED: the recursion variable is S_bot, NOT Sc. No pushforward R->Sc. ===")
print()
print("BUT: the Sc-core integral ∫_{S_bot} frobSq(Sc*S_bot)^{-c'} dS_bot is NOT uniformly bounded")
print("in Sc (blows up as Sc -> 0 / det Sc -> 0). So we CANNOT just take sup over Sc and multiply")
print("by R-box volume. The {Sc near singular} locus in R-space must be resolved -- and Sc IS a")
print("function of R, so this re-enters the R-integration. THIS is the genuine recursion coupling.")
print()
# So the honest structure: ∫_R [∫_{S_bot} frobSq(Sc(R)*S_bot)^{-c'} dS_bot] dR  must be finite.
# This is NOT a product (Sc depends on R). The inner integral is a function g(Sc(R)) and we need
# ∫_R g(Sc(R)) dR < inf.  The {Sc(R) singular} locus contributes. Let's check whether Sc(R)
# being singular is a POSITIVE-codimension event in R-space, and whether g(Sc(R)) is R-integrable.

# Use det R = det M11 * det Sc = 1 * det Sc (j=1, M11=1). So det Sc = det R.
# {Sc singular} = {det Sc = 0} = {det R = 0}. In R-space (8 free coords), {det R=0} is codim-1.
# Near {det R = 0}, frobSq(Sc*S_bot) ~ (det Sc-related) and the inner integral ~ |det Sc|^{-something}.
# The recursion's claim: this is exactly the corank-(r-j)=corank-2 core RE-blown-up, contributing
# lambda_{2,p}, and the R-integral of g(Sc(R)) over the chart is finite for c' < jp/2 + lambda_{2,p}.

print("=== The honest recursion: ∫_R g(Sc(R)) dR with g(Sc)=∫_{S_bot} frobSq(Sc*S_bot)^{-c'} ===")
print("det Sc = det R (j=1, M11=1).  {Sc singular} = {det R=0}, codim-1 in R-space.")
print("The recursion re-covers {Sc near singular} by RE-BLOWING UP Sc = a'*R' AS A FUNCTION OF R,")
print("which is the SAME radial-Delta blowup one level down -- BUT now Sc(R) is the residual, so")
print("the next-level cover is over the ENTRIES OF Sc, which are POLYNOMIAL (degree-2) in R-coords.")
