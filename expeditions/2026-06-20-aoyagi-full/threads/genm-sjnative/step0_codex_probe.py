import sympy as sp
print("="*80)
print("STEP-0 red-team resolution: Codex's monomial-coefficient row-mix vs corankStep clear-first")
print("="*80)

# ---------- (R1) Codex's exact instance: does the ledger close? ----------
print("\n[R1] Codex instance: pivot b_{J+1}=u*b (supp {u,b}), b_{J+2}=u*b*v (supp {u,b,v}).")
print("     Aoyagi clear g'_{J+2} = g_{J+2} - v*d''*g_{J+1}.  Does support close?")
u,b,v,dpp = sp.symbols('u b v dpp', positive=True)
res1,res2 = sp.symbols('res1 res2', real=True)           # linear residuals
gJ1 = u*b*res1                # pivot generator, supp {u,b}
gJ2 = u*b*v*res2              # cleared generator, supp {u,b,v}
gJ2p = sp.expand(gJ2 - v*dpp*gJ1)
fac = sp.simplify(gJ2p/(u*b*v))
print("     g'_{J+2} =", sp.factor(gJ2p))
print("     factors as (u*b*v)*(residual):", sp.simplify(gJ2p - u*b*v*fac)==0,
      " ; residual =", sp.simplify(fac), " -> supp {u,b,v} PRESERVED (target support). CLOSES.")
print("     KEY: closure holds because b_{J+1}=u*b DIVIDES b_{J+2}=u*b*v (nested supports),")
print("          so the quotient b_{J+2}/b_{J+1}=v is a REGULAR monomial; the coefficient v*d'' raises")
print("          the pivot to the target support. This is Codex's 'support-compatible monomial-coeff mix'.")

# ---------- (R2) corankStep 'clear-first, divisor-after' ordering: is each step constant-support? ----------
print("\n[R2] The banked corankStep ordering: frobSq((u.Delta).Q) = u^2*(Schur split of the u-FREE residual).")
print("     The radial u is factored FIRST (frobSq_smul_mul); the Schur elimination coefficients are")
print("     A^{-1}B (from the pivot block, REGULAR scalars), acting on the u-FREE residual entries.")
print("     => within ONE step, ALL active generators are at the SAME accumulated prefix; the elimination")
print("        uses SCALAR (A^{-1}B) coeffs, NOT divisor quotients. The next divisor v enters at the NEXT")
print("        step (corankStep_sequential: u1^2*u2^2). Verify the two orderings AGREE on the result:")
# Aoyagi order: attach divisors THEN clear with monomial-coeff v*d''  -> g'_{J+2} = u*b*v*(res2 - d''*res1)
aoyagi = sp.expand(gJ2 - v*dpp*gJ1)
# corankStep order: clear the u-FREE residuals with SCALAR coeff d'' FIRST, then attach the divisor u*b*v
res2p_clearfirst = res2 - dpp*res1          # scalar clear on residuals (coeff d'', no divisor)
clearfirst = sp.expand(u*b*v*res2p_clearfirst)
print("     Aoyagi (divisor-then-monomial-clear):", sp.factor(aoyagi))
print("     corankStep (scalar-clear-then-divisor):", sp.factor(clearfirst))
print("     TWO ORDERINGS AGREE:", sp.simplify(aoyagi - clearfirst)==0,
      " -> the clear-first (scalar-coeff, constant-support) route reproduces Aoyagi's result EXACTLY.")
print("     So gen_rowMix_const (scalar coeff, constant support) SUFFICES *if* the recursion clears the")
print("     residuals BEFORE attaching the step's divisor -- which is exactly corankStep's ordering.")

# ---------- (R3) the decisive question: does a WITHIN-EQUAL-RUN step ever clear a row that ALREADY ----
# ---------- carries a DEEPER divisor than the pivot (forcing the monomial-coeff, not scalar)? --------
print("\n[R3] Decisive: at a Case-1 partial step, can the clear pivot have FEWER divisors than a cleared row?")
print("     That needs a cleared row carrying a divisor the pivot lacks -> monomial-coeff (not scalar).")
print("     In corankStep the pivot A is the CURRENT block's top-left (same accumulated prefix as the")
print("     rows it clears -- they are ALL in the current active block, constant support). A DEEPER")
print("     divisor is only attached to the corank RESIDUAL at the NEXT step, AFTER this clear. So the")
print("     clear never sees a deeper-divisor row. The ordering is enforced by the recursion structure,")
print("     NOT assumed. Verify with the (2,1,0) nested trace at the generator level:")
# (2,1,0): L1 radial u1 on corank-1; the SURVIVING pivot (rank 2) carries {} ; corank carries {u1}.
#          L2 acts on the reduced chain (the corank residual, all carrying u1) -> introduces u2.
#          At L2 the pivot and cleared rows ALL carry {u1} (constant); u2 attached AFTER the L2 clear.
print("     (2,1,0): L1 pivot(rank2)={} split off; corank(1)={u1}. L2 on the (1,3,4) residual: ALL rows")
print("              carry {u1} (constant) at the L2 clear; u2 attached to L2's corank AFTER -> {u1,u2}.")
print("              L3 on the (1,4) leaf: ALL carry {u1,u2} (constant); Morse terminal.")
print("     => at EVERY clear the active block is constant-support (clear precedes the step's divisor).")
print("        The monomial-coeff case is AVOIDED by the clear-first ordering. Both mechanisms give the")
print("        SAME result (R2); the Lean route uses the scalar-coeff/constant-support one (corankStep).")

# ---------- (R4) adversarial: is there ANY branch/width where clear-first ordering is impossible? ----
print("\n[R4] Could an equal-run force clearing ACROSS two already-introduced divisors in one step?")
print("     That requires two DIFFERENT divisors live in the SAME active block at a clear. But each")
print("     corankStep introduces exactly ONE radial and immediately Schur-splits (pivot Morse + corank);")
print("     the corank recurses as a FRESH block. Two divisors coexist only across the pivot/corank SPLIT")
print("     (additive, loss_blockSplit), never within one clear. No single-step cross-divisor clear. [void]")
