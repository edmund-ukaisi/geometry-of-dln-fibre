<task>
A local-diffeomorphism / strict-Fréchet-derivative invertibility question, from a real-log-canonical
-threshold reduction. I need an independent check of whether a specific map's strict derivative at the
origin is an invertible isomorphism.

Setup. Coordinate space M = R × (C × S) (reg ⊕ core ⊕ spec, finite-dim real). Maps at the origin 0:

- E : M → R  ("reg residual read"), C^∞, E(0)=0, with strict derivative D_E := D(E)(0) : M → R.
  KEY FACT (call it the atom): the CORE-block of D_E is ZERO, i.e. D_E(0,δc,0) = 0 for all δc
  (E is core-independent to first order at 0).  The reg-block of D_E (the map δr ↦ D_E(δr,0,0))
  is the IDENTITY R→R (verified: it's I).

- A : M ≃ M a "core-shear" homeomorphism: A(r,c,s) = (r, c + g(r,s), s) with g continuous, g(0)=0.
  Its inverse A⁻¹(r,c,s) = (r, c − g(r,s), s).  When g is differentiable at 0, D(A⁻¹)(0) is the
  unipotent block map (r,c,s) ↦ (r, c − Dg(0)(r,s), s) (block lower-triangular, identity diagonal).

- The map of interest: π̃ := (regStraightenOf2 E_full) ∘ A⁻¹, where E_full := E ∘ A⁻¹, and
  regStraightenOf2(f)(q) := (f(q), q.2)  (replace the reg slot by f(q), carry core⊕spec identically).
  So π̃(q) = ( E(A⁻¹ q), (A⁻¹ q).2 ).  Strict derivative Dπ̃(0) = regStraightenTotalCLM2(D_{E_full}) ∘ D(A⁻¹)(0),
  where regStraightenTotalCLM2(L) is the CLM δ ↦ (L δ, δ.2), and D_{E_full} = D_E ∘ D(A⁻¹)(0).
</task>

<output_contract>
1. Is regStraightenTotalCLM2(L) : M→M invertible, in terms of L : M→R? Give the exact criterion
   (which block of L must be invertible) and why the other blocks of L are irrelevant to its det.
2. Compute D_{E_full}|reg (the reg-block of D_E ∘ D(A⁻¹)(0)) USING the atom (core-block of D_E = 0).
   Does the core-shear's reg→core mixing in D(A⁻¹)(0) corrupt the reg-block, or does the atom kill it?
3. Net: is Dπ̃(0) an invertible isomorphism at 0? State the exact remaining condition(s) it reduces to.
4. Does π̃ being a genuine C^∞ local diffeomorphism (needed to peel rlctAtOn via right-equivalence)
   require g (the shear function) to be C^∞ at 0, or only the strict-deriv invertibility above?
   Distinguish "strict-deriv is an iso" from "π̃ is ContDiff".
</output_contract>

<grounding_rules>
- Reason from the block structure of the linear maps only. Keep "strict derivative is an iso"
  distinct from "the nonlinear map is ContDiff / a genuine diffeo".
- The atom (core-block of D_E = 0) is a GIVEN fact; use it. Flag inference vs computation.
</grounding_rules>
