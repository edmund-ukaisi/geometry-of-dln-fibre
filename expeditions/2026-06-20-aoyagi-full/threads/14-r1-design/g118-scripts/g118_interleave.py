import sympy as sp
# Verify the ACTUAL interleaving in the (2,2,2) ladder: blow-up (B) FIRST makes a pivot a unit, THEN
# det-1 Schur (A) peels the residual. So the recursion node is (B);(A) interleaved, not pure-A or pure-B.
#
# (2,2,2) resolution (from r1-general-atlas lines 186-204):
#  Step 1: BLOW UP {A1=0}. Chart A1 = x*Ahat, Ahat[0,0]=1 (UNIT now). Jacobian x^? (nontrivial). [(B)]
#          F = x^2 * ||Ahat A2||^2.
#  Lemma-2 split: NOW Ahat[0,0]=1 is a unit, so the det-1 Schur clear applies: ||Ahat A2||^2 splits
#          into [pivot-row/col regular block] + [residual 2x2-ish core]. UNIT Jacobian. [(A)]
#  Step 2: the residual core {E=F0=δ=0} is STILL singular (a smaller zero-core) -> BLOW UP again. [(B)]
#  ... recurse.
print("=== The (2,2,2) recursion node = (B) blow-up THEN (A) det-1 Schur, interleaved ===")
print("Step 1 (B): blow up {A1=0}, chart A1=x*Ahat (Ahat[0,0]=1 unit), Jac nontrivial (x^k) -> x-divisor.")
print("Lemma-2 (A): NOW a minor is a unit, det-1 Schur clears the pivot row/col (UNIT Jac), splitting off")
print("            the regular block + smaller residual core. THIS is the det-1 step (my #109).")
print("Step 2 (B): the residual is STILL a singular zero-core -> blow up again -> s-divisor.")
print("recurse...")
print()
print("=> EACH recursion node = (B) blow-up [makes a minor a unit, contributes a monomial divisor]")
print("   THEN (A) det-1 Schur [peels the regular block CLEANLY, reduces the chain]. INTERLEAVED.")
print()
print("So the answer to fm-2 is: BOTH, IN SEQUENCE PER NODE, NOT either-or.")
print("  - The MONOMIAL weights (the headline ⨅ monomialThreshold) come from the (B) blow-up Jacobians.")
print("  - The det-1 (A) Schur is the UNIT-Jacobian regular-peel WITHIN the chart (reduces the chain,")
print("    contributes NO monomial weight -- it's measure-preserving).")
print("  - My #109 cert validated the (A) Schur substitution (the chain reduction is exact). It did NOT")
print("    validate that (A) ALONE resolves the core -- it does NOT. The (B) blow-up is needed at each")
print("    node to expose the unit minor that (A) then uses. My cert's 'unimodular Q' was the (A) part;")
print("    the 'leading minor is a UNIT' HYPOTHESIS is exactly what (B) provides.")
print()
print("TERMINAL LEAF: after all blow-ups + Schur peels, the leaf is monomial x (smooth block or unit).")
print("(2,2,2) had: 8 unit-leaves (pure monomial x^2 s^2) + 16 block-leaves (monomial x^2 s^2 u^2 * smooth).")
print("So the leaf is MONOMIAL (x (B)-blowup divisors) possibly times a residual smooth block. NOT a")
print("clean nReg/2-only chain. The headline IS ⨅ monomialThreshold (B-flavored), matching #113's cover.")
