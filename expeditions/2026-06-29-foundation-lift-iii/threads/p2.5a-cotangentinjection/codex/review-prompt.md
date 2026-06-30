<task>
I am independently reviewing a Lean 4 / Mathlib formalisation. A "structure as named
hypothesis bundle" encodes the infinitesimal-action input (call it H2) needed to prove an
abstract algebraic-geometry lemma B3:

  finrank k (range δ) ≤ finrank k (cotangent space at the base point)

i.e. "the deformation tangent image injects into the Zariski cotangent space at the base point"
(this is the first inequality of a squeeze A6.1; the matching equality `finrank cotangent = dim`
is a SEPARATE, out-of-scope rung B4 that needs a smooth point).

Setup. There is a carrier G with k-vector spaces C0, C1 and a k-linear δ : C0 → C1. The ambient
polynomial ring is MvPolynomial ρ k; I : Ideal (MvPolynomial ρ k) is the orbit ideal of a concrete
model; A = MvPolynomial ρ k ⧸ I.

The H2 structure `InfinitesimalAction I` bundles these FIELDS (all are hypotheses/data):
  - basePt : MvPolynomial ρ k →ₐ[k] k        (evaluation at a base k-point)
  - dirDeriv : C0 →ₗ[k] (MvPolynomial ρ k →ₗ[k] k)   (directional-derivative functional, k-linear in φ)
  - c1coord : C1 →ₗ[k] (ρ → k)  with  hc1coord : Function.Injective c1coord   (coordinate map)
  - hkill   : ∀ φ f, f ∈ I → dirDeriv φ f = 0          (each dirDeriv φ kills I)
  - hbase   : ∀ f, f ∈ I → basePt f = 0
  - hLeibniz: dirDeriv φ (f*g) = basePt f · dirDeriv φ g + basePt g · dirDeriv φ f
  - hcoord  : dirDeriv φ (X x) = c1coord (δ φ) x       (coordinate test)

The B3 proof from H2 (sketch):
  descend dirDeriv φ and basePt to A (using hkill / hbase); set m = ker(basePt on A);
  build a cotangent functional cot_φ : m.Cotangent → k (Leibniz ⟹ vanishes on m·m, since
  basePt x = basePt y = 0 for x,y ∈ m); assemble the pairing Ψ : C0 → Dual k (m.Cotangent),
  Ψ φ = cot_φ; show Ψ φ on the cotangent class of (X x − C(basePt(X x))) ∈ m equals c1coord(δ φ) x
  (via hcoord); conclude ker Ψ ≤ ker δ (if Ψ φ = 0 then every component c1coord(δ φ) x = 0, so
  c1coord(δ φ) = 0, so δ φ = 0 by injectivity of c1coord); finally rank–nullity for δ and Ψ over
  the common domain C0, plus range Ψ ⊆ Dual k (m.Cotangent) and finrank(Dual V) = finrank V, close
  the bound by omega. The ONLY analytic hypothesis is [FiniteDimensional k m.Cotangent].

The concrete discharge (DLN matrix-tuple model) instantiates basePt = aeval at the orbit point,
dirDeriv = the ε-coefficient of a dual-number evaluation (1+εφ curve), c1coord = the coordinate
embedding (injective), hkill = a dual-number "kills the ideal to first order" lemma, hLeibniz =
the dual-number snd-of-product (Leibniz) lemma, hcoord = "dirDeriv of a coordinate is its δφ
component" — all PRE-EXISTING lemmas, not restatements of the bound.

A sibling lemma B1 (a DIFFERENT inequality, the forward submersion bound) could NOT be discharged
in its naive "forward" shape and required passing to a transpose/adjoint carrier. The claim under
review is that B3's H2, by contrast, IS dischargeable in the forward shape (no transpose), because
dirDeriv + injective c1coord carry the geometric content directly via the coordinate test.
</task>

<output_contract>
Four sections, terse:
1. NAME=CONTENT verdict. Does any H2 field smuggle in the conclusion `range δ ↪ cotangent` (or
   `ker Ψ ≤ ker δ`, or the finrank bound) as a disguised assumption? Examine each field. State
   whether the bundle is an honest INPUT or circular. The sharpest worry to adjudicate: is
   hcoord (`dirDeriv φ (X x) = c1coord (δ φ) x`) + injective c1coord already equivalent to the
   injection it is supposed to prove, or is it a genuinely weaker pointwise/coordinate fact?
2. FORWARD-PINS verdict. Is the mechanism "coordinate test + injective c1coord ⟹ ker Ψ ≤ ker δ"
   genuine and non-circular, or does it hide the transpose B1 needed? Is there a hidden direction
   reversal?
3. HYPOTHESIS SCOPE. Is [FiniteDimensional k m.Cotangent] alone enough for the stated bound, with
   NO smoothness/density/perfect-field/reduced/Noetherian assumption? Flag any step in the sketch
   that would secretly need more.
4. ANY OTHER HOLE. e.g. is cot_φ well-defined on m.Cotangent = m/m² purely from Leibniz +
   basePt-vanishing-on-m (no further input)? Is the rank–nullity + dual-finrank closure valid as
   stated?
</output_contract>

<grounding_rules>
Reason from the given signatures only; you do not have the Lean source. Mark every claim as
[INFERENCE] (from the sketch) vs [GENERAL FACT] (standard algebra). If a step is plausible but you
cannot verify it from the signatures, say so explicitly rather than asserting it holds.
</grounding_rules>
