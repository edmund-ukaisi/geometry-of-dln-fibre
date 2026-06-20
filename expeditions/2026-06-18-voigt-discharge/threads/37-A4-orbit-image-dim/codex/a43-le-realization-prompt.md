# A4.3 ≤-bound: minimal-Lean realization given the matrix-Kähler identity

Lean 4 + Mathlib v4.29. I must prove, char-free (k a field):

```
genericDifferentialRank k B f  ≤  finrank k (LinearMap.range (deformationδ M M))
```

where:
- `B = groupRing d = Localization.Away (groupDenom d)` of `MvPolynomial (GroupCoord d) k`, a domain.
- `K := FractionRing B`, `Ω := Ω[K⁄k]` (KaehlerDifferential.D k K : K → Ω, a k-derivation).
- `genericDifferentialRank k B f := finrank_K (span_K { D k K (algebraMap B K (f x)) : x : RepCoord d })`.
- `f = genericOrbitCoord M : RepCoord d → B`, `f ⟨i,r,c⟩ = (genericUnit (i.succ) * genericFactor M i * genericUnitInv (i.castSucc))_{r,c}`.
- Over K: `V_v := (genericUnit d v).map (algebraMap B K)` is invertible, inverse `Vinv_v := (genericUnitInv d v).map (algebraMap B K)` (we have `genericUnit_mul_genericUnitInv` over B, push to K). `F_i := M_i` lifted to K via algebraMap k K (constant; D kills it).
- `deformationδ M M : cochain0 d d →ₗ[k] cochain1 d d`, `φ ↦ (φ_{i.succ} M_i − M_i φ_{i.castSucc})_i`.
  `cochain0 d d = ∀ v, Matrix (Fin d_v) (Fin d_v) k`; `cochain1 d d = ∀ i, Matrix (Fin d_{i+1}) (Fin d_i) k`.

## The matrix-Kähler identity I have / will prove (the gate)
Entrywise differential `dA : Matrix m n Ω`, `(dA)_{rc} = D(A_{rc})`. Leibniz: `d(AB) = (dA)·B + A·(dB)` (Ω-K bimodule products). `d(V⁻¹) = −V⁻¹ (dV) V⁻¹`. With `Θ_v := Vinv_v · (dV_v) : Matrix (Fin d_v)(Fin d_v) Ω`,
```
d(V_{i+1} M_i Vinv_i) = V_{i+1} · ( Θ_{i+1} M_i − M_i Θ_i ) · Vinv_i      (★)
```
(M_i constant ⇒ dF=0; factor V_{i+1} left, Vinv_i right). So `D(f ⟨i,r,c⟩) = ( V_{i+1} (Θ_{i+1}M_i − M_iΘ_i) Vinv_i )_{rc}`.

## THE QUESTION — cleanest Lean realization of the rank bound

I want `finrank_K S ≤ finrank_k (range δ⁰)`, S = span_K{D(f x)}. The bracket `Θ_{i+1}M_i − M_iΘ_i` is "δ⁰ applied to the Ω-valued family Θ". I need to convert this into the bound by `finrank_k(range δ⁰)` (the RANK of δ⁰, not dim cochain0). Naively bounding by entries of Θ gives Σ d_v² = dim cochain0, which is too big — I must keep the δ⁰-structure.

Candidate A (surjection from K ⊗_k range δ⁰):
Build a K-linear surjection `Ψ : K ⊗[k] (range (deformationδ M M)) →ₗ[K] S`. Then
`finrank_K S ≤ finrank_K (K ⊗[k] range δ⁰) = finrank_k (range δ⁰)` (Module.finrank_baseChange + Submodule.finrank_map_le / LinearMap.finrank_range_le).
- How to honestly DEFINE Ψ on K ⊗ range δ⁰ so that it hits D(f x)? The bracket lives in cochain1 ⊗ Ω, not directly range δ⁰ ⊗ K. What's the precise factoring? Is there a "contraction" using the entries of V, Vinv as the K-coefficients, applied to a pure tensor `c ⊗ (δ⁰ φ)`?

Candidate B (span ⊆ image of a single K-linear map evaluated on range δ⁰):
Define K-linear `Φ : cochain1(d,d) →ₗ[k] Ω` ... but Φ must be K-linear to bound K-finrank; cochain1 is a k-space. Use `K ⊗_k cochain1 → Ω` instead, with range δ⁰ ⊗ K mapping onto S?

KEY ASK:
1. Give the EXACT Lean-level definition of the bounding K-linear map and its (co)domain so that (i) its range ⊇ S, (ii) its domain has finrank_K = finrank_k(range δ⁰). Resolve the "Ω is K-module but Θ entries are arbitrary D-values, while range δ⁰ is over k" tension precisely. Pure-tensor formula for the map on `c ⊗ w`, `w ∈ range δ⁰`.
2. Confirm the right Mathlib bricks: `Module.finrank_baseChange`, `Submodule.finrank_map_le`, `LinearMap.finrank_range_le`, `Submodule.span_le`, `Submodule.map_span`. Is there a clean "span_K {Φ(b_j)} ≤ span over image" lemma so I avoid defining a TensorProduct map explicitly?
3. Is there a SHORTER path: e.g. show S = (K-span of D(f x)) equals `(span_K {entries of Θ_{i+1}M_i − M_iΘ_i})` (the V,Vinv conjugation is by INVERTIBLE K-matrices, so it preserves the K-span — state this), and then bound THAT span by exhibiting it as the K-linear image of `range δ⁰` under the "evaluate δ⁰ at the Θ basis"? i.e. is the cleanest statement: `span_K {(δ⁰-bracket of Θ) entries} = K-span of {D(V_v entries)} pushed through δ⁰`, dimension ≤ finrank_k(range δ⁰)?

Give concrete Lean lemma signatures (definitions to make + the 4-6 lemmas), favoring the LEAST infrastructure. Do NOT assume a cotangent-duality / dualMap route — I want the direct surjection/image route if it is shorter. Flag any step where Ω being infinite-dimensional over k breaks a finrank lemma.
