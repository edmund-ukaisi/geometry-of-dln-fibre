<task>
Setting: formalising Aoyagi's iterated-blow-up resolution of the zero-product locus of a
deep linear network. Fix a dimension vector d = (d_0, d_1, ..., d_N) (all d_i > 0). Matrices
A_{ℓ+1} : k^{d_ℓ} → k^{d_{ℓ+1}} for ℓ = 0..N-1 ("layer ℓ" = the matrix A_{ℓ+1}; layer ℓ has
d_{ℓ+1} rows and d_ℓ columns). The core object is

  coreGen_{ij} = ( A_N · A_{N-1} · ... · A_1 )_{ij}
             = Σ_{k_1,...,k_{N-1}} A_N[i,k_{N-1}] · ... · A_2[k_2,k_1] · A_1[k_1, j].

Coordinates u are the matrix entries; "layerCoords ℓ" = ALL entries of A_{ℓ+1} (the full
d_{ℓ+1} × d_ℓ block); "blockCoords ℓ" = the entries of A_{ℓ+1} in columns with (col index) <
widthMinUpto(ℓ), where widthMinUpto(ℓ) = min(d_0, d_1, ..., d_ℓ) (the running-minimum width up
to layer ℓ). So blockCoords ℓ ⊆ layerCoords ℓ, with equality iff widthMinUpto(ℓ) = d_ℓ.

The resolution is a tree of block-center blow-ups. Along a path, foldResid is the strict
transform of coreGen. At a "δ=1" edge (the first clear at a layer S — the running clear-count J=0)
the strict transform DIVIDES OUT the pivot coordinate (dehomogenises the center by the pivot) and
the residual then "descends" to read the deeper block at layer S+1. The step invariant being
formalised claims the residual is, for every layer ℓ at or above the current support layer,
(A) homogeneous of degree exactly 1 in layerCoords ℓ (equivalently: affine in those coords AND
vanishing when they are all 0), AND (B) supported on the CAPPED block blockCoords(S+1) of the
descended layer — i.e. ∃ continuous c_i with residual = Σ_{i ∈ blockCoords(S+1)} c_i · u_i.

Three questions. Reason independently; do not assume my framing is right.

Q1. For d = (1, 2, 1): widthMinUpto(1) = min(1,2) = 1, so blockCoords(1) = {col-0 entries of A_2}
    = {A_2[0,0]}, while layerCoords(1) = {A_2[0,0], A_2[0,1]}. Write coreGen explicitly (it is the
    single entry (A_2 A_1)[0,0]). Is coreGen homogeneous of degree 1 AND vanishing-at-0 in
    layerCoords(1)? In blockCoords(1)? Give the decisive term.

Q2. THE MAIN QUESTION. After a δ=1 clear at layer S (running min widthMinUpto(S+1) =
    min(d_0..d_{S+1})), is the strict-transformed residual at the descended layer S+1 GENUINELY
    supported only on the running-min-capped columns (col < widthMinUpto(S+1)), or can it read the
    full d_{S+1} columns of A_{S+2}? If the cap can FAIL, give the smallest dimension vector d and
    the offending term. If the cap HOLDS, name the structural reason (what forces the residual's
    S+1-dependence into the first widthMinUpto columns).

Q3. Are properties (A) "degree-1 in the full layerCoords ℓ" and (B) "supported on the capped
    blockCoords ℓ" logically independent — i.e. does (A) fail to imply (B), so that (B) needs a
    separate support-tracking argument? Give a one-line proof or counterexample.
</task>

<output_contract>
Three sections, Q1 / Q2 / Q3. For Q1 and Q2, state the explicit polynomial / term you used.
For Q2 lead with a one-word verdict (HOLDS / FAILS) then the witness-or-reason. Be terse.
</output_contract>

<grounding_rules>
Distinguish what you verified by direct computation (mark "COMPUTED") from what is structural
inference about Aoyagi's mechanism (mark "INFERENCE"). If a claim about the strict transform's
support depends on a detail of the blow-up center you cannot pin from the description, say so
explicitly rather than guessing.
</grounding_rules>
