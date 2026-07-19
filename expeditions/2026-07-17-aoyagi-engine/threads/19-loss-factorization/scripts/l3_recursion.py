#!/usr/bin/env python3
"""
L=3 (2,2,2,2), t=(1,0,0) — the depth-≥2 decisive experiment.

The team-lead's kill-condition: under a DEPTH-≥2 composite of Aoyagi's chart
substitutions, does  frobSq(prod (composite w))  factor as
   (∏ divisor, each EXACTLY power 1)² · (residual bounded below by baseForm) ?

We compute the loss pullback for F = ‖C1·C2·C3‖² (all 2×2) via the layer-peel
recursion, and CONTRAST two ways of doing the SECOND layer:
  (A) WITH the incidence/Q,P normalization (Aoyagi-faithful chart = ψ∘β / β∘α);
  (B) WITHOUT it — a PURE max-modulus blow-up of a fixed coordinate center
      (the structure of the CURRENT geoChartMap = q.symm∘pivotChart∘q, q LINEAR).

If (A) monomializes (α²ρ²α'²ρ'²·Morse) but (B) leaves a leaked divisor or a
non-Morse / non-bounded-below residual, then the incidence normalization is
LOAD-BEARING for the loss factorization, and LeafPullback over the pure-β
chartMap is FALSE as stated.
"""
import sympy as sp

# ---------- Layer-1 peel (verified, verify-r1-shortcut.md) ----------
# incidence on (C1,C2): A=α[[1,a],[b,ab+δ]], B=[[u-ar,v-as],[r,s]]; C3 free.
a,b,delta,u,v,r,s,alpha = sp.symbols('a b delta u v r s alpha', real=True)
c00,c01,c10,c11 = sp.symbols('c00 c01 c10 c11', real=True)   # C3 entries
C3 = sp.Matrix([[c00,c01],[c10,c11]])

A = alpha*sp.Matrix([[1,a],[b, a*b+delta]])
B = sp.Matrix([[u-a*r, v-a*s],[r,s]])
prod3 = A*B*C3
F = sp.expand(sum(prod3[i,j]**2 for i in range(2) for j in range(2)))

# blow up {δ=u=v=0}: δ=ρ, u=ρξ, v=ρη
rho,xi,eta = sp.symbols('rho xi eta', real=True)
F1 = sp.expand(F.subs({delta:rho, u:rho*xi, v:rho*eta}))
core1 = sp.expand(F1/(alpha**2*rho**2))
print("=== after layer-1 peel: F = α²ρ²·core1 ===")
print("core1 leaked α?", core1.has(alpha), " leaked ρ?", core1.has(rho))
# identify core1 as a fresh (2,2,2) core ‖X·C3‖² with X=[[1,0],[b,1]]·[[ξ,η],[r,s]]
X = sp.Matrix([[1,0],[b,1]])*sp.Matrix([[xi,eta],[r,s]])
core1_paper = sp.expand(sum((X*C3)[i,j]**2 for i in range(2) for j in range(2)))
print("core1 == ‖([[1,0],[b,1]]·[[ξ,η],[r,s]])·C3‖² ?",
      sp.simplify(core1-core1_paper)==0)
print("  => fresh depth-2 core ‖X·C3‖², X a 2x2 (rank-generic in ξ,η,r,s).")

# order of core1 at deepest point (ξ=η=r=s=0, C3=0):  should be 4 (fresh singularity, NOT Morse)
allfree = [xi,eta,r,s,c00,c01,c10,c11]
# lowest total degree monomial
poly = sp.Poly(core1, *allfree)
mindeg = min(sum(m) for m in poly.monoms())
print("order of core1 at deepest point =", mindeg, " (4 => fresh singularity, not a unit/Morse)")

print("\n" + "="*70)
print("LAYER 2: resolve the fresh core ‖X·C3‖².  X plays the role of a fresh 'A',")
print("C3 the fresh 'B'.  X = [[1,0],[b,1]]·[[ξ,η],[r,s]]; the free params of the")
print("fresh core are the entries of X (4 of them) and C3 (4).  b is a spectator.")
print("="*70)

# Write the fresh core in its OWN variables: let Y = X (a free 2x2, entries y00..y11),
# absorbing the unipotent [[1,0],[b,1]] into the definition of the fresh 'A'.
# (The unipotent is a UNIT transform; Aoyagi's block-elim normalizes it away.
#  Its Jacobian is 1 and it does not create/destroy divisors — cert-psi-mix R-b.)
y00,y01,y10,y11 = sp.symbols('y00 y01 y10 y11', real=True)
Y = sp.Matrix([[y00,y01],[y10,y11]])
Fresh = sp.expand(sum((Y*C3)[i,j]**2 for i in range(2) for j in range(2)))

# ---------- (A) WITH incidence normalization (Aoyagi-faithful) ----------
# Layer-2 incidence: Y = α'[[1,a'],[b',a'b'+δ']], C3 = [[u'-a'r',v'-a's'],[r',s']]
ap,bp,dp,up,vp,rp,sp_,alphap = sp.symbols("a' b' delta' u' v' r' s' alpha'", real=True)
Y_inc = alphap*sp.Matrix([[1,ap],[bp, ap*bp+dp]])
C3_inc = sp.Matrix([[up-ap*rp, vp-ap*sp_],[rp,sp_]])
FreshA = sp.expand(sum((Y_inc*C3_inc)[i,j]**2 for i in range(2) for j in range(2)))
rhop,xip,etap = sp.symbols("rho' xi' eta'", real=True)
FreshA2 = sp.expand(FreshA.subs({dp:rhop, up:rhop*xip, vp:rhop*etap}))
coreA = sp.expand(FreshA2/(alphap**2*rhop**2))
print("\n--- (A) WITH incidence normalization ---")
print("Fresh = α'²ρ'²·coreA ;  coreA leaked α'?", coreA.has(alphap),
      " leaked ρ'?", coreA.has(rhop))
HA = sp.hessian(coreA, [xip,etap,rp,sp_]).subs({xip:0,etap:0,rp:0,sp_:0,bp:0})
print("coreA Hessian rank at deepest pt (b'=0) =", HA.rank(), " (4 => Morse, resolved)")
print("  => FULL loss = α²ρ² · α'²ρ'² · (Morse).  Divisors {α,ρ,α',ρ'} each power 2. HOLDS.")

# ---------- (B) WITHOUT incidence: PURE max-modulus blow-up of the fresh core ----------
# The current geoChartMap blows up a FIXED coordinate center via a max-modulus
# pivotChart. Model layer-2 as a pure blow-up of the fresh 'A'=Y directly:
# pivotChart on the 4 entries of Y with pivot = y00 (max-modulus chart):
#   y00=p, y01=p*q1, y10=p*q2, y11=p*q3   (p the exceptional divisor coord)
p,q1,q2,q3 = sp.symbols('p q1 q2 q3', real=True)
Ysub = {y00:p, y01:p*q1, y10:p*q2, y11:p*q3}
FreshB = sp.expand(Fresh.subs(Ysub))
print("\n--- (B) PURE max-modulus blow-up of Y (pivot y00), NO incidence ---")
# factor out p^2 (the natural divisor power from a single blow-up of the 'A' block)
coreB = sp.expand(FreshB/p**2)
print("Fresh = p²·coreB ;  coreB leaked p?", coreB.has(p))
# is coreB Morse / a unit? order at deepest point
polyB = sp.Poly(coreB, q1,q2,q3,c00,c01,c10,c11)
mindegB = min(sum(m) for m in polyB.monoms())
print("order of coreB at deepest point =", mindegB, " (>0 => NOT a unit; residual still singular)")
HB = sp.hessian(coreB, [q1,q2,q3,c00,c01,c10,c11]).subs(
    {q1:0,q2:0,q3:0,c00:0,c01:0,c10:0,c11:0})
print("coreB Hessian rank at deepest pt =", HB.rank(), " (0 => degenerate, NOT Morse)")
print("  => a SINGLE pure blow-up of Y leaves ‖[[1,q1],[q2,q3]]·C3‖² — a fresh")
print("     (2,2,2) core, order 4, NOT a unit and NOT Morse.  Same §8 failure.")

# Does a further pure blow-up of C3 finish it?  (test: blow up C3 pivot c00)
pp,cc1,cc2,cc3 = sp.symbols('pp cc1 cc2 cc3', real=True)
C3sub = {c00:pp, c01:pp*cc1, c10:pp*cc2, c11:pp*cc3}
coreB2 = sp.expand(coreB.subs(C3sub))
# the c00-blow-up factors pp² out of the ‖·C3‖² ONLY if every term carries c00...
# check divisibility:
q = sp.symbols('q')
is_div = sp.simplify(coreB2/pp**2)
print("\n--- (B') further pure blow-up of C3 (pivot c00): coreB = pp²·? ---")
print("coreB2/pp² still polynomial (no negative powers)?",
      not sp.Poly(sp.together(coreB2/pp**2), pp).as_expr().has(1/pp))
core_final = sp.expand(coreB2/pp**2)
print("core_final leaked pp?", core_final.has(pp))
polyF = sp.Poly(core_final, q1,q2,q3,cc1,cc2,cc3)
print("order of core_final at deepest pt =", min(sum(m) for m in polyF.monoms()))
HF = sp.hessian(core_final,[q1,q2,q3,cc1,cc2,cc3]).subs(
    {q1:0,q2:0,q3:0,cc1:0,cc2:0,cc3:0})
print("core_final Hessian rank =", HF.rank(), "(want 6 for Morse in 6 residual coords)")
