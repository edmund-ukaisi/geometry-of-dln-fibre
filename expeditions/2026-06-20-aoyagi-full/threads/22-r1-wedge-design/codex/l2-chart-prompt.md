<task>
Lean 4 + Mathlib v4.29. I'm formalising an RLCT lower-bound box-divergence for deep linear nets, L=2,
concrete (3,3,4). I found a soundness obstruction in the proposed "single pivotBlowupOn" chart and need
the correct chart construction.

SETUP:
- F(x) = ‖A·C‖²_Frobenius where A (3×3), C (3×4) read off flat coords x ∈ Fin 21 → ℝ.
- minAdm = 8 (achiever rank t=1: codim = (3−1)(3−1) + 1·4 = 4+4 = 8).
- Want: ∫⁻_{cubeBox 21 ε} |F|^{−c'} = ⊤ for c' ≥ 4, every ε>0.
- The leaf atom (EXISTING, reusable): `monomialIntegrand_lintegral_box_eq_top` gives ∫_{[0,δ]^d} (Π|uⱼ|^{hⱼ})·(Π|uⱼ|^{2kⱼ})^{−c'} = ⊤ when the binding axis has h−2k·c' ≤ −1. Binding axis here: pivot u with (k,h)=(1,7), so 7−2·4=−1 at c'=4.
- The c-o-v tool: `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (EQUIDIMENSIONAL only — needs a square Jacobian det).
- `pivotBlowupOn active p`: pivot p ↦ x_p; active j≠p ↦ x_p·x_j; spectators fixed; `det = x_p^{|active|−1}`.

THE OBSTRUCTION I found (sympy-verified):
The achiever curve is: A = [1×1 identity pivot block A[0,0]=1; 2×2 residual = u·Dbar; CROSS STRIPS
A[0,1],A[0,2],A[1,0],A[2,0] = 0]; C = [top row = u·Tbar with Tbar[0,0]=u the pivot; bottom 2 rows = S generic].
Then A·C = u·[[Tbar],[Dbar·S]] EXACTLY, F = u²·U, U = ‖Tbar‖²+‖Dbar·S‖² ≥ 1 (u-free).
BUT this requires A[0,0] FIXED to constant 1 and cross strips FIXED to 0 — `pivotBlowupOn` CANNOT fix a
coord to a nonzero constant (it only scales-by-pivot or passes-through).
And I PROVED: no choice of an 8-element `active ⊆ Fin 21` makes a pure `pivotBlowupOn` give F = u²·(u-free)
for ALL x (the constraint "every product entry is homogeneous degree-1 in u" forces, per inner index k,
either all-of-A-col-k active+none-of-C-row-k, or vice versa, giving |active| ∈ {9,10,11,12}, never 8).
If I scale the cross strips by u too (to make pivotBlowupOn applicable), |active| grows to ~10-12, the det
becomes u^{|active|−1} ≠ u^7, AND F = u²·U + O(u³) (U no longer u-free) — the binding axis exponent shifts.

THE TWO CANDIDATE FIXES:
(A) EMBEDDING/TUBE chart: a map from a lower-dim box (the 8 active coords + pivot, the rest FIXED at
    achiever constants 1 and 0) into Fin 21. Gives EXACT F = u²·U, U≥1 u-free, but the map is NOT
    equidimensional → no square Jacobian → can't use `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.
    Would need a Fubini-style: integrate the fixed coords over a small box around (1,...,0,...), the
    achiever-curve coords carry the u-blowup. The fixed coords contribute a positive FINITE measure factor.
(B) FULL pivotBlowupOn with the SLICE handled by domain restriction: use pivotBlowupOn on an 8-element
    active set, accept F = u²·U with U continuous & bounded c₀≤U≤C>0 on a small box [0,δ]^21 (NOT u-free,
    but two-sided-bounded suffices: |F∘φ|^{−c'} ≥ C^{−c'} u^{−2c'}). The det is exactly u^7. The risk:
    proving c₀ ≤ U on a positive-measure box when U is only ≥¼ at u=0 on a Tbar-slice (continuity gives a
    box but maybe not [0,δ]^21 uniformly).

THE (2,2,2) TEMPLATE I'm mirroring used pivotBlowupOn composites and got EXACT F∘φ = monomial·Uval with
Uval u-free and ≥1 — because there the blow-up centers were genuine (the residual after each pivot was a
clean lower-depth product). It did NOT fix any coord to a nonzero constant.
</task>

<output_contract>
1. Which fix (A embedding-tube, B full-blowup-with-bounds, or C something else) is the SOUNDEST + most
   Lean-tractable given the equidimensional-c-o-v constraint? 2-4 sentences.
2. If (A): the precise Fubini factorization — how to split ∫_{cubeBox 21 ε} so the 8+1 blowup coords get
   the exact u^7 Jacobian via an 8-or-9-dim pivotBlowupOn, and the remaining 12 "fixed" coords contribute
   a finite positive measure of a small box around the achiever constants. Does the cross-strip-and-identity
   structure of A even survive if those coords are integrated over a box (not fixed to exact 1,0)?
   I.e. is F = u²·U still valid when A[0,0]∈[1−η,1+η], cross strips ∈[−η,η] rather than exactly 1,0?
3. The cleanest way to reconcile "exact u^7 Jacobian" with "exact F=u²·U factorization" — is there an
   8-or-9-element active set + a coordinate REPARAMETRIZATION (not the raw matrix entries) that makes BOTH
   hold? E.g. does choosing the pivot as a residual-block entry rather than C[0,0] help?
4. Honest fallback: if NO equidimensional chart gives both exact-Jacobian AND exact/two-sided-bounded
   factorization in one tide, what is the minimal HONEST sorry to leave (with the precise remaining
   obligation), vs is the whole (3,3,4) achievable?
</output_contract>

<grounding_rules>
Flag inference vs fact. You don't have the Lean source. The sympy facts (F=u²·U on the exact achiever curve;
no 8-element active set gives global u²·(u-free)) are VERIFIED — treat as given. Reason about the c-o-v /
measure-factorization architecture. If you propose a Mathlib lemma, mark name-uncertain.
</grounding_rules>
