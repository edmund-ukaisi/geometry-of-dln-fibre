# Decorrelated review: does one Case-1 blow-up node's chart family cover factor through a SINGLE gauge?

You are an algebraic geometer red-teaming a formalisation design. Answer from the geometry only;
I am withholding my own hypothesis. Be adversarial and concrete.

## Setup (Aoyagi 2023, DLN resolution, Case 1 blow-up)

Ambient real coordinates near a point: a rectangular block of "residual" entries `d_{ij}`
(i = J+1..J+J1, j = J+1..M', so a J1 x (M'-J) block) together with ONE pre-existing "divisor"
coordinate `u` (call it u_{s,k}). The Case-1 blow-up center is the coordinate subspace
`{ all d_{ij} = 0, u = 0 }`, of codimension `d_center = J1*(M'-J) + 1` (the block entries plus u).

The blow-up of this codim-`d_center` coordinate center is covered by `d_center` standard affine
"pivot" charts, one per center coordinate, in the max-modulus normalization: in chart p, the pivot
coordinate x_p is free, every other center coordinate x_k = x_p * (ratio_k) with |ratio_k| <= 1.
Exactly one chart is the **u-pivot chart** (u is the max-modulus coordinate); the other
`d_center - 1` are **d-entry pivot charts** (some d_{ij} is the max-modulus).

After each pivot chart, the paper "cleans" the residual block to a Morse/normal form by a
variable-dependent unipotent shear: right-multiply the residual by an upper-unipotent Q (clears the
pivot row), left-multiply by a lower-unipotent P (clears the pivot column); net effect on
coordinates is a Schur-complement update `d_{ij} -> d_{ij} - d_{i1} d_{1j}` (indices relative to the
pivot's row/column), with det = 1. Call this per-chart gauge `psi_p`. The final chart map is
`chartMap_p = psi_p ∘ beta_p` where `beta_p` is the pivot blow-up.

## The formalisation lemma under scrutiny

A proven Lean lemma covers a node when ALL its edges share ONE gauge: it assumes there is a single
homeomorphism `psi` (independent of the pivot p) such that for every pivot p,
`chartMap_p = psi ∘ beta_p`, and it concludes the union of chart images equals
`psi '' (union of pure-pivot images) = psi '' (cube)`, hence covers `psi '' (center-slab)`.

## Questions (answer each explicitly, with reasoning)

1. Is the residual-clearing gauge the SAME single map `psi` for all `d_center` charts of ONE Case-1
   node — i.e. does `chartMap_p = psi ∘ beta_p` hold with a p-INDEPENDENT `psi`? Consider the
   **u-pivot chart** specifically: in the u-pivot chart the whole block is `d_{ij} = u * d'_{ij}`;
   does the Schur-complement clean act the same there as in a d-entry pivot chart, or is the u-pivot
   chart's gauge effectively the identity / a different map?

2. If the gauges differ across charts (`psi_p` genuinely depends on p), does the union
   `⋃_p (psi_p ∘ beta_p)(dom_p)` still cover a neighborhood of the node's piece of the zero-locus?
   Does it factor as `psi '' (something)` for any single `psi`? If not, what is the correct cover
   statement (per-edge gauge)?

3. For the d-entry pivot charts alone (ignore u): is the Schur gauge relative to pivot p the same
   map for every d-entry pivot p, or is it relative to each pivot's own row/column (hence p-dependent)?
   Does a "symmetric orbit / post-pivot frame" argument (the family is the symmetry orbit of the
   corner pivot, and in the frame where each beta_p absorbs its pivot the clearing is structurally
   identical) rescue a single shared `psi`? State precisely the condition under which it does.

4. Bottom line for the Lean design: is a single-per-node-gauge cover lemma SUFFICIENT for a Case-1
   node, or is a per-edge-gauge cover lemma required? If it depends on a modelling choice, name the
   choice and the check that decides it.
