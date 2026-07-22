<task>
Adjudicate the correct re-design of a resolution-of-singularities ATLAS predicate so that a
composition-of-blow-ups atlas COVERS a neighbourhood of the origin, and determine which per-chart
properties survive the re-design. This is an exact pen-and-paper math question; give an independent
derivation, do not rubber-stamp.
</task>

<objects>
Fix a dimension vector d and let D = flatDim d (a number). Work in R^D with coordinates indexed by a
finite set I of size D. There is a finite rooted COMBINATORIAL tree T (deterministic oracle); a
root->leaf path P is a sequence of STEPS. Each step carries three data, all functions of the
combinatorial state at that node:
  - center: a subset S ⊆ I  (value-pinned: S = canonCenter(state), a fixed finite set of coordinates);
  - pivot: a single coordinate p ∈ S  (currently value-pinned: p = canonPivot(state));
  - shear φ: a unipotent, det-1, origin-fixing polynomial self-map of R^D (value-pinned: φ = canonShear(state)).

The step MAP is  σ = B_{S,p} ∘ shear, where the block-center blow-up is
  B_{S,p}(w)_j = w_p              if j = p
              = w_p · w_j         if j ∈ S \ {p}
              = w_j               if j ∉ S   (spectators, fixed).
Note B_{S,p} is applied OUTERMOST within a step; and the path map g_P = σ_root ∘ σ_1 ∘ ... ∘ σ_m is
composed ROOT-OUTERMOST. So image(g_P) ⊆ image(B_{S_root, p_root}).

Facts already established (exact):
  (F1) For a fixed center S, the |S| maps { B_{S,p} : p ∈ S }, applied to the unit box, cover the unit
       cube in the S-coordinates (argmax / max-modulus: route p = argmax_{q∈S}|x_q|), spectators passing.
       (This is the standard "blow-up of the origin is covered by |S| affine charts".)
  (F2) A unipotent det-1 polynomial shear is a global bijection with polynomial inverse.
  (F3) |det D B_{S,p}| = w_p^{|S|-1} — the Jacobian is a pure monomial of exponent |S|-1 on the pivot axis.

The atlas has one CHART per root->leaf path P; chart P has map g_P and a compact source box dom_P.
There are three families of per-chart properties the full construction requires each chart to satisfy:
  (L6) chart geometry: g_P analytic, origin-fixing, a.e.-injective off the exceptional set, and
       |det D g_P| = a pure squarefree monomial (the accumulated ∑ step exponents);
  (L8) exponent read-off: for each chart, (Jacobian exponent on the binding axis) + 1 equals a divisor
       exponent of the leaf reached; and every relevant leaf-divisor exponent is realised by some chart;
  (Descent/Inv) a per-EDGE algebraic invariant "FoldStepInv" preserved along the path: it involves the
       STRICT TRANSFORM of a residual family, i.e. dividing the pulled-back residual by w_p^k (the pivot
       coordinate). For one class of step ("merge"/case-1(1)), the current proof of this invariant uses
       that p = canonPivot is the IMMUTABLE BIRTH CORNER of a divisor born at an EARLIER layer (a
       "pivot-separation": p lies strictly below the current layer, so setting w_p=1 leaves the current
       layer's support intact). canonCenter for that merge class is { birth-corner } ∪ (current-layer block).
</objects>

<questions>
Q1. The current predicate value-pins pivot = canonPivot (a SINGLE coordinate). Show precisely why the
    resulting single-pivot atlas FAILS to cover a neighbourhood of 0 (identify the escaping set and its
    codimension/measure), and state the minimal change to the predicate that restores the cover.

Q2. If the fix is to let pivot range freely over the center S (keeping center and shear value-pinned),
    determine, property by property, whether each per-chart family (L6, L8, Descent/Inv) is preserved
    when the chart's pivot is an ARBITRARY element of S rather than the single canonPivot:
      - which properties are pivot-INDEPENDENT in VALUE/shape and transfer immediately?
      - which properties are stated at the pivot and require re-proving for a general pivot ∈ S?
    In particular, adjudicate the "merge"/case-1(1) Descent/Inv: does its pivot-separation argument
    survive when the pivot is a CURRENT-layer coordinate of the center (not the earlier birth corner)?
    If it does NOT survive, say so plainly and characterise exactly what breaks.

Q3. Is uniform fanning over ALL steps' centers necessary for the cover, or only at the root / only at
    steps whose center has |S| ≥ 2? Justify via the argmax routing over the composed tree.

Q4. Independent of the above, is there any obstruction to the cover being a FULL cover (empty escape,
    not merely measure-zero) once the pivot is fanned — considering pivot-tie loci, the pivot-zero /
    whole-block-zero locus, and the shear-arising sets?
</questions>

<output_contract>
For each question: a definite verdict, the exact reason, and (where relevant) a concrete small witness.
Distinguish clearly FACTS you derived from INFERENCES/conjectures. If a property does NOT transfer under
fanning, say so explicitly — do not paper over it. Flag any place where you needed an assumption not
given above.
</output_contract>

<grounding_rules>
Exact algebra only. Do not assume the shear is cube-invariant (it can inflate a box by a bounded factor).
Do not assume anything about the oracle beyond determinism and the step data described. The answer must
be independent of any Lean/formalisation concerns.
</grounding_rules>
