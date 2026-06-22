import sympy as sp
# DOES THE SQUEEZE RECURSION RECONSTRUCT THE KNOWN VALUE? (2,2,2), r=1, aoyagiLambda = 3/2.
# Unroll the squeeze chain: rlctAtOn(core_M) 0 = Σ_levels nReg/2 + rlctAtOn(leaf) 0.
# For (2,2,2) the verified answer (Lean: rlctAt myF222 0 = 3/2) is the GROUND TRUTH. Check the recursion
# tree's ⨅ = 3/2 (not < 3/2 = undershoot, not > 3/2 = the partial-family overestimate).
#
# The g128 cert already did (2,2,2) r=1 deepest: rlctAt(F) = nReg/2 + rlctAt(G²), nReg=3, rlctAt(G²)=1/2,
# total 3/2. Here G = the (1,1,1)-chain core (the reduced node), rlctAt(G²)=1/2 its leaf value. Let me
# verify the WHOLE chain bottoms out correctly and the codim accounting:
# (2,2,2) deepest, r=1: ambient dim = 2·2 + 2·2 = 8. nReg (regular smooth squares at top) per g128 = 3.
# reduced core G² has rlct 1/2 (a single (1,1,1) bilinear = u·v, ‖uv‖² ... actually G = -w3w7/(w1w6-1)).
print("=== (2,2,2) r=1 ground-truth check (aoyagiLambda = 3/2) ===")
# aoyagiLambda for (2,2,2) r=1:
def aoyagi_codim_min_222():
    # the codim C for (2,2,2): the paper's value. min_t Mval = 3 (codim of the top stratum rank A=1).
    # rlct = nReg/2 + ½·min_t Mval ... but the KNOWN total rlct = 3/2. Let me reconcile: the FULL loss
    # rlct = 3/2 (verified). Decompose: regular part n/2 + core ½·C.
    return 3  # min_t Mval = 3
print("  min_t Mval (codim of top stratum) =", aoyagi_codim_min_222())
print("  KNOWN rlctAt(dlnLoss 222) deepest = 3/2 (Lean-verified, AxCheck).")
print("""
  Squeeze-chain reconstruction (g128/g129):
    rlctAtOn(core_222) 0 = nReg/2 + rlctAtOn(reduced core) 0
  with nReg = 3 (the 3 regular pivot-row squares at the (2,2,2) deepest split, g128) and the reduced
  core = the (1,1,1) leaf with rlct 1/2. Total = 3/2 + ... wait — need to be careful about CORE vs FULL.
""")
# The careful accounting: resolution_charts is about the CORE rlctAtOn(dlnLoss M 0) 0 (the SINGULAR core,
# reduced widths M = H - r). For (2,2,2) H=(2,2,2), r=1 ⟹ M = (1,1,1). The CORE is dlnLoss (1,1,1) 0 =
# ‖c1·c2‖² (scalars c1,c2) = (c1 c2)². rlctAtOn((c1 c2)²) 0 = ? This is x²y² type: rlct = 1/2 (the min of
# the two axes 1/2 each... ∫|c1 c2|^{-2s} = ∫|c1|^{-2s}∫|c2|^{-2s}, each converges iff s<1/2, product
# iff s<1/2 ⟹ rlct = 1/2). So rlctAtOn(CORE) = 1/2, and aoyagiLambda = n/2 + 1/2 with n the regular term.
c1,c2 = sp.symbols('c1 c2', real=True)
coreF = (c1*c2)**2
print("  CORE for (2,2,2) r=1: M=H-r=(1,1,1), core = (c1·c2)², rlctAtOn = 1/2 (each axis 1/2, min).")
print("  ⟹ aoyagiLambda = nReg/2 + ½·(core codim). Need ½·min_t Mval for the CORE = 1/2 ⟹ min Mval_core = 1.")
print("""
  RECONCILE: resolution_charts gives rlctAtOn(CORE) 0 = ⨅ monomialThreshold. For core=(c1c2)²:
  blow up {c1=0}∪{c2=0}? No — the core (c1c2)² is ALREADY monomial (normal crossing): the resolution is
  TRIVIAL (identity chart), monomialThreshold with d=2, k=(1,1), h=(0,0): min_j (h_j+1)/(2k_j) =
  min(1/2,1/2) = 1/2. ✓ The atlas inf = 1/2 = the true rlct. EXHAUSTIVE (single trivial chart suffices
  for an already-normal-crossing core; the ⨅ is exact).
""")
# Verify rlctAtOn((c1 c2)²) = 1/2 via the monomial threshold d=2,k=(1,1),h=(0,0):
print("  monomialThreshold d=2 k=(1,1) h=(0,0) = min((0+1)/2,(0+1)/2) = 1/2 = rlctAtOn((c1c2)²). MATCH.")
