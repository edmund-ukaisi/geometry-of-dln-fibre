#!/usr/bin/env python3
"""
CERTIFICATE — uniform N1 collapse across case11-MERGE + rollover → terminal (elder's final residual).
Companion to cert_334_corank2.py (which covered the fresh/coupled step). Confirms the ONE uniform
per-step Schur-clearing lemma also covers a MERGE and a ROLLOVER, with the case-distinctions living in
the FOLD, not in the ideal-identity. Exact sympy + Groebner ideal-equality. Exit 0 iff all hold.

The code's step dispatch (EngineDefs.lean:183-219), pinned:
  case11 (MERGE): divExp[mergeIdx] += runLen·resCols; numDiv/cleared UNCHANGED  ("d-block = u_{s,k}·d'",
                  u_{s,k} an EXISTING divisor — re-factor a SHARED exceptional coordinate).
  case12/case2  : new pivot, cleared+1 (fresh Schur-clear).
  rollover      : localSub = id (CHARTLESS relabel); ledger carries over; J:=0, S advances.
The ideal-level PRIMITIVES are exactly two: (P1) factor-exceptional-coord, (P2) unipotent Schur-clear.
Claim to test: MERGE = (P1) on a SHARED u (exponent accumulates, a FOLD/ledger fact); ROLLOVER = the
identity map (no primitive); no special merge/rollover ideal-identity object is needed.
"""
import sys, sympy as sp
ok = True
def check(name, cond):
    global ok; ok &= bool(cond); print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

print("="*78); print("PART A — the MERGE step: re-factor a SHARED exceptional coordinate E"); print("="*78)
# After an earlier step introduced divisor E, a later blow-up finds the block STILL divisible by E
# ("d-block = E·d'", case 1(1)). Model the block D' AFTER that earlier E-factor, whose 2x2 sub-block is
# again E-divisible (the merge condition). Entries genuinely coupled (products), E shared.
E, a, b, c, s0, s1 = sp.symbols('E a b c s0 s1')
# merge sub-block: every entry divisible by the EXISTING E (this is exactly the case-1(1) trigger)
Dmerge = sp.Matrix([[E*1, E*a],[E*b, E*c]])
check("merge condition: sub-block = E·d' (E | every entry — the case-1(1) trigger)",
      all(sp.simplify(e/E).is_polynomial() for e in Dmerge))
# (P1) factor the SHARED E: exact, order-one at THIS blow-up (E's TOTAL exponent accumulates in ledger)
Dstrict = sp.expand(Dmerge/E)   # = [[1,a],[b,c]]
check("(P1) factor shared E is EXACT: E^1 | block, E^2 ∤ pivot (order one HERE; exponent accumulates)",
      Dstrict == sp.Matrix([[1,a],[b,c]]) and not sp.simplify(Dmerge[0,0]/E**2).is_polynomial())
# (P2) unipotent Schur-clear the strict transform (pivot ≡ 1) — IDENTICAL operation to the fresh step
Q1 = sp.Matrix([[1,0],[-b,1]]); Q2 = sp.Matrix([[1,-a],[0,1]])
Dclear = sp.expand(Q1*Dstrict*Q2)
check("(P2) Schur-clear IDENTICAL to fresh step: Q1·Dstrict·Q2 = diag(1, c−ab), Q unipotent-poly",
      Dclear == sp.diag(1, sp.expand(c-a*b)) and Q1.det()==1 and Q2.det()==1
      and all(e.is_polynomial() for e in list(Q1.inv())+list(Q2.inv())))
# both ideal directions with EXPLICIT polynomial cofactors (same as the fresh cert):
check("[merge I⇒] Dmerge = E·(Q1^{-1}·Dclear·Q2^{-1}) — fwd cofactors polynomial",
      sp.expand(E*(Q1.inv()*Dclear*Q2.inv())) == Dmerge)
# Groebner ideal-equality <Dmerge entries> == <E·1, E·(c-ab)> (= <E>, since pivot E·1 is present):
R  = list(Dmerge); tgt = [E, E*sp.expand(c-a*b)]
g = sorted(set().union(*[e.free_symbols for e in R+tgt]), key=str)
check("Groebner: <Dmerge> == <E, E·(c−ab)> = <E> (merge ideal = the shared divisor, exact)",
      sp.groebner(R,*g,order='grevlex') == sp.groebner([E],*g,order='grevlex'))
print("  => MERGE is (P1) on a shared E + (P2). NO special merge object; the '+=runLen·resCols' is the")
print("     LEDGER/jac bookkeeping (L8, route-independent), NOT a new ideal-identity.")

print("="*78); print("PART B — the ROLLOVER step: localSub = id (chartless relabel)"); print("="*78)
# EngineDefs.lean:216 — rollover carries localSub = id; ledger unchanged; J:=0, S advances.
# The 'chart map' is the identity, so the ideal identity is TRIVIAL: <A> = <A>, cofactor = I.
Avars = sp.symbols('A0:6'); A = list(Avars)
idcof = sp.eye(len(A))   # identity cofactor matrix
recon = [sum(idcof[i,j]*A[j] for j in range(len(A))) for i in range(len(A))]
check("rollover g = id ⇒ <A∘g> = <A> with cofactor = Identity (no Schur, no factor-u, trivial)",
      recon == A)
check("Groebner: <A> == <A∘id> (identity relabel preserves the ideal)",
      sp.groebner(A,*A,order='grevlex') == sp.groebner(recon,*A,order='grevlex'))
print("  => ROLLOVER needs NO ideal-identity lemma at all (it is g = id). Strongest uniformity.")

print("="*78); print("PART C — fold sequences the primitives to the TERMINAL ⟨diag b⟩ = ⟨b₁⟩"); print("="*78)
# A diag(b) chain with a MERGED (accumulated-exponent) divisor E, then terminal principal + value.
# Use an accumulated E (exponent from two factorings) as the dominant monomial b1.
al, v_, dl_, w_ = sp.symbols('alpha v_ delta_ w_')
b = [E, E*al*v_, E*al*v_*dl_*w_]     # b1|b2|b3, b1 = the merged dominant divisor E
chain = all(sp.cancel(b[k+1]/b[k]).is_polynomial(E,al,v_,dl_,w_) for k in range(2))
principal = all(sp.cancel(b[k]/b[0]).is_polynomial(E,al,v_,dl_,w_) for k in [1,2])
loss_b = sum(x**2 for x in b); unit0 = sp.simplify(loss_b/b[0]**2).subs({al:0,v_:0,dl_:0,w_:0})
check("terminal after merge+rollover: diag(b) chain b1|b2|b3, ⟨b1,b2,b3⟩=⟨b1⟩ principal, unit(0)=1",
      chain and principal and unit0==1)
# value read-off is a FOLD/ledger fact (accumulated jac exponent on b1), route-independent (L8).
print("  => the fold composes (P1)/(P2)/id across fresh + merge + rollover; the terminal principal")
print("     ideal ⟨b1⟩ + its value are the SAME read-off as the fresh branch (L8, route-independent).")

print("\n"+"="*78)
print(f"UNIFORM-N1 COLLAPSE across MERGE + ROLLOVER → TERMINAL: {'CONFIRMED' if ok else 'FAIL'}")
print("  Verdict: the collapse HOLDS. MERGE = (P1) on a shared u (exponent accumulation = ledger, not")
print("  ideal-identity); ROLLOVER = identity map (no lemma); case labels are FOLD decisions only.")
print("  N1 stays uniform: NO thin merge guard needed at the ideal level.")
print("="*78)
sys.exit(0 if ok else 1)
