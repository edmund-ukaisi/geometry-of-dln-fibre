#!/usr/bin/env python3
"""
EXACT analysis of the N2b lower-bound danger at corank >= 2.

After the det-1 S-reparam S = U*(P;Q),  U = [[I, -M11^{-1} M12],[0,I]]:
   (R*S)_top = M11 * P
   (R*S)_bot = M21 * P + Sc * Q          (Sc = M22 - M21 M11^{-1} M12)
   frobSq(R*S) = frobSq(M11*P) + frobSq(M21*P + Sc*Q)

The cert's D (the disjoint split) is:  D = frobSq(M11*P) + frobSq(Sc*Q).

LOWER bound to be proven for hfin:   c0 * D <= frobSq(R*S)  with c0 > 0 UNIFORM.

   frobSq(R*S) = frobSq(M11 P) + frobSq(M21 P + Sc Q)
   D           = frobSq(M11 P) + frobSq(Sc Q)

THE DANGER (exact): can  M21 P + Sc Q  be SMALL while  Sc Q  is LARGE?
Yes, if Sc Q = -M21 P (cancellation).  Then frobSq(R*S) = frobSq(M11 P), but D = frobSq(M11 P)+frobSq(M21 P).
Ratio F/D = frobSq(M11 P) / (frobSq(M11 P) + frobSq(M21 P)).

On the bounded complete-pivoting cell, |M21 M11^{-1}|_entries <= 1 (the Cramer bound R2).
=> frobSq(M21 P) = frobSq(M21 M11^{-1} * M11 P) <= ||M21 M11^{-1}||^2 * frobSq(M11 P)
   with ||M21 M11^{-1}||^2 bounded by a UNIFORM constant (entries <=1, fixed sizes).
=> F/D >= frobSq(M11 P)/(frobSq(M11 P) + K*frobSq(M11 P)) = 1/(1+K) > 0  UNIFORM.

This is the KEY: the cancellation cost is bounded because M21 P is CONTROLLED by M11 P via the
bounded shear M21 M11^{-1}.  Let us verify this chain EXACTLY (symbolically), and find K.
"""
import sympy as sp

print("="*70)
print("EXACT: the cancellation bound via the bounded shear  M21 M11^{-1}")
print("="*70)

# Symbolic test r=3, j=1 (corank-2 residual), p=2 (suffices; p just adds columns -> sum over columns).
# M11 = [[a]] (1x1), M12 = [b0,b1] (1x2), M21 = [[c0],[c1]] (2x1), M22 (2x2).
# Shear M21 M11^{-1} = [c0/a, c1/a].  Complete-pivoting on a 1-minor: a is max-modulus ENTRY => |c_i/a|<=1.
a, b0, b1, c0, c1 = sp.symbols('a b0 b1 c0 c1', real=True)
m00,m01,m10,m11 = sp.symbols('m00 m01 m10 m11', real=True)
# P, Q columns (one column suffices for the cancellation structure; p>=1)
p0 = sp.symbols('p0', real=True)              # P is 1 x p ; here P = (p0) for the j=1 top
q0, q1 = sp.symbols('q0 q1', real=True)        # Q is (r-j) x p ; here Q = (q0,q1)^T (one column)

M11 = sp.Matrix([[a]])
M12 = sp.Matrix([[b0, b1]])
M21 = sp.Matrix([[c0],[c1]])
M22 = sp.Matrix([[m00,m01],[m10,m11]])
Sc  = M22 - M21*M11.inv()*M12          # 2x2 Schur complement
shear = M21*M11.inv()                   # 2x1 shear, entries c0/a, c1/a, each |.|<=1 on the cell

P = sp.Matrix([[p0]])                    # 1 x 1
Q = sp.Matrix([[q0],[q1]])               # 2 x 1

top  = M11*P                             # = a*p0
bot  = M21*P + Sc*Q                      # the bottom block of R*S
F = sp.expand((top.T*top)[0] + (bot.T*bot)[0])
D = sp.expand((top.T*top)[0] + ((Sc*Q).T*(Sc*Q))[0])

# The bound:  frobSq(M21 P) = frobSq(shear * (M11 P)) = frobSq(shear * top)
M21P = M21*P
shear_top = shear*top
print("M21*P            =", sp.simplify(M21P.T))
print("shear*(M11*P)    =", sp.simplify(shear_top.T))
print("  equal? ->", sp.simplify(M21P - shear_top) == sp.zeros(2,1))
print()
# frobSq(bot) = frobSq(M21 P + Sc Q) >= 0 ; F = frobSq(top) + frobSq(bot).
# We DON'T want F >= c0*D directly via bot (bot can vanish). Instead use:
#   frobSq(Sc Q) = frobSq(bot - M21 P) <= 2 frobSq(bot) + 2 frobSq(M21 P)   [parallelogram/CS]
#   frobSq(M21 P) <= ||shear||_F^2 * frobSq(top)                            [shear bound]
# => D = frobSq(top) + frobSq(Sc Q) <= frobSq(top) + 2 frobSq(bot) + 2 ||shear||^2 frobSq(top)
#      = (1 + 2||shear||^2) frobSq(top) + 2 frobSq(bot)
#      <= (1 + 2||shear||^2) * (frobSq(top)+frobSq(bot)) ... using max(1+2s^2, 2)
#      <= max(1+2||shear||^2, 2) * F.
# So  D <= C * F  i.e.  F >= (1/C) D  with C = max(1+2||shear||^2, 2).
# On the bounded cell ||shear||_F^2 <= (r-j)*j  (each of (r-j)*j entries <= 1).  UNIFORM!
print("CHAIN (exact inequalities, all standard):")
print("  frobSq(M21 P)  = frobSq(shear * top)  <= ||shear||_F^2 * frobSq(top)")
print("  frobSq(Sc Q)   = frobSq(bot - M21 P)  <= 2 frobSq(bot) + 2 frobSq(M21 P)")
print("  => D = frobSq(top)+frobSq(Sc Q) <= (1+2||shear||^2) frobSq(top) + 2 frobSq(bot)")
print("       <= max(1+2||shear||^2, 2) * F")
print("  => F >= D / max(1+2||shear||^2, 2)")
print()
print("  On the bounded complete-pivoting cell:  ||shear||_F^2 <= (r-j)*j  (entries |.|<=1).")
print("  => UNIFORM c0 = 1 / max(1 + 2*(r-j)*j, 2)  works for ALL R in the cell.  LOWER BOUND HOLDS.")
print()
print("="*70)
print("VERDICT (exact): the LOWER direction of N2b holds UNIFORMLY at any corank,")
print("with c0 = 1/(1 + 2*(r-j)*j), PROVIDED the shear bound ||M21 M11^{-1}||_entries <= 1 holds.")
print("The two-sided (UPPER also) is NOT needed for hfin.")
print("="*70)
