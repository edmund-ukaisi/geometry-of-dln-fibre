import sympy as sp

# ============================================================
# O2 — the ACTUAL recursion mechanism (per L32a-cover-cert + RouteMSchurDepth2).
# Does the corank-3 recursion NEED a pushforward R -> Sc, or does it factorise via
# the two-sided sandwich + Fubini, keeping R as the integration variable?
# ============================================================

# The recursion at corank r (here r=3), after radial Delta=a*R and the a-axis Tonelli split,
# must bound:  INNER(R-chart) = ∫_{R on M11-dominant chart} ∫_{S} frobSq(R*S)^{-c'} dS dR
#
# N2b gives, ON the chart (|R_ij|<=1, M11=max-modulus j-minor, det M11 != 0), the UNIFORM sandwich:
#   c0 * D(R,S) <= frobSq(R*S) <= c1 * D(R,S),   D(R,S) = frobSq((R*S)_top) + frobSq(Sc*S_bot)
# with c0,c1 = (1/(2+2 j (r-j)), 2+2 j (r-j))  -- ABSOLUTE constants (indep of R,S).
#
# So:  frobSq(R*S)^{-c'} <= c0^{-c'} * D(R,S)^{-c'}   (for c'>0, the upper bound on integrand).
# Hence INNER(R) <= c0^{-c'} ∫_R ∫_S D(R,S)^{-c'} dS dR.
#
# Now D = frobSq((R*S)_top) + frobSq(Sc*S_bot) is a DISJOINT-variable-group sum IN S
# after the det-1 S-reparam S = U*(P;Q) (P = top j rows feeding (R*S)_top, Q = S_bot feeding Sc).
# The KEY structural claim to check: in the recursion we hold R FIXED, integrate over S first
# (the Morse-peel of the top block + the Sc*Q core), THEN integrate over R.
# We do NOT change variables R -> Sc.  Let's verify the inner-S integral is bounded by a
# function of R that is itself integrable over the R-chart.

# Concretely the inner-S integral at FIXED R splits (Tonelli, disjoint P,Q):
#   ∫_S D^{-c'} dS  ~  [∫_P (frobSq((R*S)_top))^{...}] couples? Let's see if it factorises.
# D = frobSq((R*S)_top) + frobSq(Sc*S_bot). The top block (R*S)_top = M11*P + M12*Q-ish...
# Actually from the schur_key_identity:  (R*S)_bot = (M21*M11^{-1})*(R*S)_top + Sc*S_bot.
# And (R*S)_top = M11*S_top + M12*S_bot.  The natural normal-form: P-block = (R*S)_top, Q=S_bot.

# Let's just verify the central claim numerically/symbolically:
# The Sc-core ∫_{S_bot} frobSq(Sc*S_bot)^{-c'} dS_bot at FIXED R (fixed Sc) is a
# (r-j)-dim core integral that the IH (induction hypothesis at corank r-j) handles --
# IF Sc satisfies the IH's chart hypotheses. THAT is the real O2 question:
#   does Sc, as R ranges over the chart, land in (a finite cover of) corank-(r-j) chart cells
#   on which the IH applies, with the R-integral of the IH-bound staying finite?

# Verify: Sc entries are BOUNDED on the chart (|R_ij|<=1)?
r = sp.symbols('r01 r02 r10 r11 r12 r20 r21 r22', real=True)
r01,r02,r10,r11,r12,r20,r21,r22 = r
Sc = sp.Matrix([[ -r01*r10+r11, -r02*r10+r12],
                [ -r01*r20+r21, -r02*r20+r22]])
print("=== Sc entry bounds on the chart |r_ij| <= 1 ===")
for a in range(2):
    for b in range(2):
        e = Sc[a,b]
        # each entry = -prod + single, both factors in [-1,1] => entry in [-2,2]
        print(f"  Sc[{a},{b}] = {e}   range on chart: [-2, 2] (|spectator*spectator|<=1, |M22 entry|<=1)")

# So Sc lives in the box [-2,2]^{(r-j)x(r-j)}. BOUNDED. Good -- but the IH needs Sc to ALSO
# satisfy: (a) a corank-(r-j) chart pivot normalization (some entry = max-modulus, !=0), and
# (b) the M11-dominant-style bound for the NEXT level. These come from the recursion's
# RE-BLOWUP (R4 in minorpivot-cert): Sc is radially blown up afresh Sc = a'*R', R' re-pinned.
# The {Sc=0} set is the a'=0 null divisor. So the IH is applied to ‖Sc * S_bot‖^2 as a FRESH
# corank-(r-j) core, NOT via a pushforward of R.

print()
print("=== CRITICAL: does the recursion change variables R->Sc, or hold R and recurse on the CORE? ===")
print("The cert/Lean route: HOLD R, sandwich frobSq(R*S) ~ D(R,S), Fubini-split S into")
print("(top Morse block P) DISJOINT (Sc-core Q=S_bot). The Sc-core ∫_Q frobSq(Sc*Q)^{-c'} is")
print("a corank-(r-j) integral in Q at FIXED Sc(R). The recursion is on the CORE INTEGRAND")
print("(a function of (Sc, Q)), with Sc a fixed matrix per R. NO pushforward R->Sc needed for")
print("the S-integral. The R-integral is then handled by the OUTER radial cover at corank r.")
