
## ROUTE CORRECTION (from the genm-radsep WITNESS certificate, 2026-06-28) — supersedes the pivotBlowupOn route
The radial-separability WITNESS landed (HOLDS ∀ interior M; exact sympy on anchors + L=4/L=5 multi-t≥2 +
structural proof + Codex). It carries a LOAD-BEARING route correction to §"THE RADIAL-EXTRACTION" above:

**DO NOT use `pivotBlowupOn ∘ normChart`.** Its "u-free normChart" premise is FALSE for general interior M:
`chartParamsGen` is u-dependent in EVERY layer; only the DETERMINANT's u-content collapses. (4,4,2,2) — where
one block carries all u³ — is the MISLEADING special case.

**USE the AFFINE-IN-u COMMON-COLUMN-FACTOR route** (cert, sympy-verified): the chart is AFFINE in u
(degree ≤ 1, NO u²; structural from `Cgen` linear in u: `C k = Bmat·chainQ + u·Rmat`, `C L = u·Rfin`, +
`chainA` affine in C(k+1)). Flattened: `Phi(u,h,z) = P(z) + u·r0 + u·Σ_a h_a·r_a` where `h_a` = the free
angular coords, `r_a` = fixed output directions. So:
  D_z Phi = D_z P(z) [u-free];  D_{h_a} Phi = u·r_a [angular column carries factor u];  D_u Phi = r0 + Σ h_a r_a [u-free].
Factor `u` from each of the `q = minAdm−1` angular columns ⟹ det = u^{minAdm−1}·G(z,h), ∂_u G = 0. The
per-layer u-powers ACCUMULATE to the front (3333: D_0→u^0, D_1→u^2, D_2→u^3 = u^5), NOT one block's prefactor.
The layer-filtration grading (2b) STILL HOLDS — det = ∏_k det D_k; the radial extraction WITHIN it is the
affine-in-u column factor. The `chainA` shear is unipotent (det 1, z-dependent entries only) so the `−N_k W_k`
shear cannot leak u into the cofactor; fixed interior R_k of ANY rank (incl. t≥2 coupling) cannot leak u.

**THE GENUINE 2b-i RESIDUAL (the real risk, per the cert + controller): the BUDGET IDENTITY** —
#free-coords = flatDim, with EXACTLY #angular = minAdm−1 free R_k/Rfin entries (the rest of R_k = fixed pivots;
one pivot = u; one Rfin pivot fixed = 1 → exponent active.card−1). Cert caveats: (i) inert B_0 free coords must
be fixed/discarded (else zero Jacobian columns, non-square); (ii) one Rfin pivot fixed = 1. This is the
dependent-Fin accounting / square-chart well-definedness over opaque widths — NOT the radial math, which is
settled. The sympy engine's `n != NC` (non-square) guard is exactly this budget check.

REVISED 2b-i: realize det J = u^{minAdm−1}·(u-free) via the affine-in-u angular-column factoring, WITHIN the
per-layer det_comp (2b-ii). The budget identity (#angular = minAdm−1, square chart) is the delicate piece —
spec it carefully before the column-factor deep-fill.
