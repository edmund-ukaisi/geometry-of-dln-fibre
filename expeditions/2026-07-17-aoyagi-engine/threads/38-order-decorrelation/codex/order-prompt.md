<task>
A resolution-of-singularities bookkeeping question from Aoyagi (2023), "Consideration on
the learning efficiency of multiple-layered neural networks with linear units", the
recursive blow-up proof (paper pp.15-20). I need an INDEPENDENT derivation of one
composition order. Derive it from the substitution facts below; do not assume my answer.

SETUP (transcribed from the page images). At recursion state (S, J) the working object is
  diag(b_1,...,b_M) . D_J . (deeper layers),      D_J = (d_ij) a matrix block.
The equal-run Case-1(2) step introduces ONE new exceptional coordinate u (= u_{S,J+1},
the "pivot") and advances J -> J+1. Two substitutions are written, in this textual order:

  (STEP 1, the "blow-up" B) The whole d-block is factored by the pivot:
      d_ij  =  u * d'_ij       for every entry of the block
     (in the Case-1(2) chart the top-left d'-entry is normalised to 1).
     So this substitution expresses each OLD block coordinate d_ij as u times a NEW
     coordinate d'_ij. Spectator coordinates (outside the block) are untouched.

  (STEP 2, the "shear" S) The d'-block is then reduced by two UNIPOTENT matrices built
     from the d'-entries themselves: a right factor Q (clears the pivot ROW off-diagonal,
     entries -d'_{first-row,j}) and a left factor P (clears the pivot COLUMN, entries
     -(b'-ratio)*d''_{i,first-col}), giving  P . D'_J . Q = [[1, 0],[0, D_{J+1}]].
     D_{J+1} is the child block (Schur complement). This expresses the intermediate d'
     coordinates as functions of the CHILD coordinates D_{J+1} plus the shear parameters.
     The shear leaves the pivot coordinate u fixed.

The paper's composite identity for the step (p.18-19) reads
   P . diag(b) . D_J . C   =   u * diag(b') . (P D'_J Q) . C'
                            =   u * diag(b') . [[1,0],[0,D_{J+1}]] . C'.

CONVENTION. The resolution map g sends resolved/child coordinates to original/parent
coordinates: parent = g(child). The per-step "atom" is the map child -> parent for this
one step. Each written substitution expresses OLD-in-terms-of-NEW. Reversal/substitution
rule: if parent = B(x) and x = S(child), then atom = B ∘ S.
</task>

<output_contract>
1. STATE the atom as a single composition: either  B ∘ S  (blow-up outermost, applied last
   to reach parent) or  S ∘ B  (shear outermost). One line, unambiguous.
2. JUSTIFY from the substitution direction only: which substitution expresses parent-in-terms-of
   -intermediate (outermost) vs intermediate-in-terms-of-child (innermost). 3-6 sentences.
3. DIVISIBILITY consequence: under your derived order, is every parent-frame block ("center")
   coordinate, pulled back through the atom, divisible (as a polynomial) by the child pivot
   coordinate u? Say YES/NO and why in one or two sentences. Then say whether the OTHER order
   would give the same answer, and why/why not.
Keep it under ~250 words. Do not hedge between the two orders — commit.
</output_contract>

<grounding_rules>
- Reason only from the substitution facts and the stated reversal rule. The two substitutions
  are: B multiplies block coords by u (old = u*new); S is the unipotent Q/P Schur reduction
  (intermediate = function of child + shear params), pivot-fixing.
- "Divisible by u as a polynomial" means the pulled-back coordinate, expanded in the child
  coordinates, has u as a factor with a polynomial (not rational/localised) quotient.
- Commit to one order. Do not restate my setup back to me; give the derivation and the answer.
</grounding_rules>
