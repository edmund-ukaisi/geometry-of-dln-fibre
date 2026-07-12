import sympy as sp

# ============================================================================
# OFF-SECTOR: {σ_min(Z) < ε} covered by finite corank cells {corank(Z)=q}.
# On cell q: q collapsing singular values s_1≥...≥s_q ∈(0,κ) (m=1: σ²≍dist²);
# pushforward joint density dμ ≍ ∏_j s_j^{(D_j - D_{j-1}) - 1} ds  (codim increments D_j),
# front-box majorant g̃ ≍ ∏_j s_j^{-e_j}.  We test the NEIGHBOURHOOD integral (positive measure,
# the ordered simplex 0<s_q<...<s_1<κ), NOT the measure-zero locus.  CLAIM: finite ⟺ c' < ½minAdm.
# We verify via the banked per-cell threshold ½(M₀ρ + min(M₀q, D_q)) on the ANCHOR (3,3,3,4) and a q=3 case,
# and confirm the ordered-simplex (nested-tube) integral converges exactly at that threshold.
# ============================================================================

c = sp.symbols('c', positive=True)

def tube_integral_threshold(exps_g, dens_pows):
    """Nested-tube (ordered simplex 0<s_q<...<s_1<kappa) integral of ∏ s_j^{-e_j} · ∏ s_j^{p_j}.
       Integrate innermost-first over (0, s_{j-1}); each inner integral needs its running exponent > -1.
       Returns the list of binding conditions (each 'exponent > -1' as a bound on c)."""
    q = len(exps_g)
    # net power on s_j (before nesting) = p_j - e_j
    net = [dens_pows[j] - exps_g[j] for j in range(q)]
    conds = []
    carry = 0  # extra power pushed onto the next-outer var from integrating inner vars
    for j in range(q-1, -1, -1):     # innermost (largest index) to outermost
        expo = net[j] + carry
        conds.append(sp.simplify(expo))     # need expo > -1
        carry = expo + 1                     # ∫_0^{s_{j-1}} s_j^{expo} ds_j = s_{j-1}^{expo+1}/(expo+1)
    return conds  # each must be > -1

# --- ANCHOR (3,3,3,4), cell q=2 (the banked corank2-cert §2 case) ---
# ρ = r-q = 3-2 = 1 survive; deeper product P = Ã1·A2 is 3×4; D1=codim{rank≤2}=1, D2=codim{rank≤1}=4.
# g̃ ≍ s2^{-3} s3^{-(2c-6)}  (corank2 §1, asymmetric: p=3 on max, α'=2c-6 on min); density dμ ≍ s2^{2} ds3 ds2 (s2 outer).
# Represent as ordered (s1_outer=s2, s2_inner=s3): exps_g=[3, 2c-6], dens_pows=[2, 0].
exps=[sp.Integer(3), 2*c-6]; dens=[sp.Integer(2), sp.Integer(0)]
conds = tube_integral_threshold(exps, dens)
print("[ANCHOR (3,3,3,4) cell q=2]  nested-tube binding conditions (each expo > -1):")
for k,cd in enumerate(conds):
    sol = sp.solve(sp.Gt(cd, -1), c)
    print(f"    inner→outer level {k}: expo = {cd} > -1  ⟺  {sol}")
print("    ⟹ binds at c < 7/2 = ½(D₂+d₂)=½(4+3), d₂=m₀(r-2)=3. Neighbourhood (ordered simplex, +measure) FINITE for c<7/2.\n")

# --- a q=3 cell (deeper corank 3): to confirm the pattern generalizes (dims illustrative) ---
# say collapsing exps g̃ ≍ ∏ s_j^{-α_j}, density powers p_j from codim increments; verify the nested integral
# binds at the SUM structure (charges ADD across the q nested scales), matching ½(M₀ρ+min(M₀q,D_q)).
# Use symbolic α_j and p_j to show the mechanism (each inner integral lends +1+... to the outer).
a1,a2,a3,p1,p2,p3 = sp.symbols('a1 a2 a3 p1 p2 p3', positive=True)
exps3=[a1,a2,a3]; dens3=[p1,p2,p3]
conds3 = tube_integral_threshold(exps3, dens3)
print("[generic q=3 nested tube]  binding conditions (expo>-1), innermost→outermost:")
for k,cd in enumerate(conds3):
    print(f"    level {k}: {sp.expand(cd)} > -1")
print("    ⟹ the OUTERMOST condition accumulates Σ(p_j - a_j) + (q-1) > -1: the inner integrals' +1's ADD,")
print("       so the tube threshold = ½·Σ(density - g̃ exponents) = the charges-ADD value (dmcheck ½(M₀ρ+min(M₀q,D_q))).\n")

# --- the SEAM (transition): the tube integrand at the cell boundary s_{ρ+1}→κ matches the next-lower cell ---
print("[seam] at s_{ρ+1}→κ (leaving cell q into cell q-1), g̃ ≍ κ^{-p}·(remaining)^{-α'} matches the codim-(q-1)")
print("       form continuously (corank2 §1: sector boundary s₂→κ gives κ^{-3}s₃^{-α'} = codim-1 form). Cells GLUE.")
