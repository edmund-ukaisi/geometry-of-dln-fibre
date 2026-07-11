<task>
Decide whether an existing "decoration carrier" can express an additive corner blow-up, or whether a new
constructor is needed. Give an independent, decisive verdict with exact algebra. I withhold my lean.
</task>

<setup>
An RLCT/finiteness proof resolves a loss to a monomial and reads its threshold. Objects (all banked):
- A support matrix e : (generators ι) × (coords Fin d) → ℕ. Generator i is a monomial
  gen_i(u) = ∏_ℓ |u_ℓ|^{e(i,ℓ)} times a linear residual. The LOSS = ∑_i gen_i(u)².
- sharedDivisorExp e ℓ = min_i e(i,ℓ)  (the common divisor's exponent of u_ℓ).
- Terminal finiteness: if some generator i₀ achieves the min on EVERY coord (dehomogenised, residual
  becomes a unit ∈[a,b]), then ∫_{unitBox} (loss)^{-c'}·∏_ℓ|u_ℓ|^{h_ℓ} < ⊤  for
  c' < monomialThreshold = min_{ℓ: k_ℓ>0} (h_ℓ+1)/(2 k_ℓ),  k = sharedDivisorExp.
- Constructor `prependColumn (a : ι→ℕ)`: adds a fresh coord with per-generator exponent a(i). `radialAttach`
  = prependColumn (a ≡ 1): the fresh divisor is shared by ALL generators to order 1, so it multiplies the
  WHOLE loss by u₀² (multiplicative).
- Banked `corner_block_cube`: ∫_{[-1,1]^n}(∑ x_i²)^{-c'} < ⊤ for c' < n/2 (FLAT measure, isotropic, unit
  coefficients).

The concrete target (from the geometry): the loss is ADDITIVE across m blocks,
   G(u) = ∑_{k=1}^m u_k²·U_k,   U_k ≍ 1 (bounded above and below on a sector),
with Jacobian measure ∏_k |u_k|^{h_k}, h_k = p_k − 1 (p_k the block codims), Σp_k = minAdm. The blocks are
SEPARATE: block-k's generators carry u_k only (support = block-diagonal, e = [[1,0,..],[0,1,..],...]).
Goal threshold: ½·Σp_k = ½·minAdm  (e.g. m=2, p=(4,3): 7/2).
</setup>

<questions>
Q1 (does the additive corner reach ½Σp via the terminal?). With block-diagonal support e=[[1,0],[0,1]]
   (m=2), sharedDivisorExp = (0,0), so NO generator achieves the min on both coords ⟹ NOT dehomogenised ⟹
   the terminal does not apply directly. Now apply the toric CoV u₁=u·τ, u₀=u (common-corner blow-up):
   (a) give the new support matrix in (u,τ) coords; (b) its sharedDivisorExp; (c) the new Jacobian
   exponents (h_u, h_τ) including the CoV Jacobian; (d) is it now dehomogenised, and does the terminal give
   min_{k>0}(h+1)/(2k) = 7/2? Confirm the ½Σp value exactly, and generalise to m blocks
   (H_u = Σh_k+(m−1)).

Q2 (is `radialAttach` the right op?). `radialAttach` = prependColumn(a≡1) multiplies the WHOLE loss by
   u₀², giving (∏_k u_k²)·unit — the MULTIPLICATIVE product, support all-1's, threshold min_k(h_k+1)/2 =
   ½·min_k p_k (= 3/2, the undershoot). Confirm radialAttach models the product (min), NOT the additive
   corner (sum). What op builds the block-diagonal support instead (prependColumn with a block-indicator)?

Q3 (CARRIER-FIT — the decision). To close the additive corner at ½Σp, is a NEW constructor needed, or do
   the banked pieces suffice? Evaluate:
   (i) toric-CoV-merge then terminal: the SUPPORT algebra (sharedDivisorExp/terminal) expresses the merged
       threshold, but the toric CoV u_k=u·τ_k with the |u| measure Jacobian (h_u=Σh+m−1) is an
       integral-level operation — is it banked (radialAttach_integral is the multiplicative single-radial)?
   (ii) banked `corner_block_cube` (n=Σ block dims, flat measure): gives Σdim/2 — does this equal ½Σp
       (does the FLAT-measure isotropic corner match the Jacobian-weighted additive corner)? And it needs
       unit coefficients + cooperative dims — is it width-general?
   Decide: does the carrier FIT (name the assembly) or need a NEW constructor (give its exact signature:
   inputs = the block-additive decoration + units-bounded-below hypothesis; output = merged decoration;
   the sum-threshold ½Σ(h_k+1) it must satisfy)?
</questions>

<output_contract>
For Q1–Q3: exact algebra + "FACT" vs "INFERENCE". End: FITS (with the banked assembly) or NEW CONSTRUCTOR
(with its exact signature + semantics + the sum-threshold), and whether the units-bounded-below sector is a
required hypothesis (the a.e. rank-drop complement routed separately).
</output_contract>

<grounding_rules>
Exact monomial-integral algebra. Distinguish the multiplicative product (∏u²→min) from the additive corner
(∑u²U→sum after blow-up). Flat measure vs Jacobian-weighted measure must be kept distinct.
