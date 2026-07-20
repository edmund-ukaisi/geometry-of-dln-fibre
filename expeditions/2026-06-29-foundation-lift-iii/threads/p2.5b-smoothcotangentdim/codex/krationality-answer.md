1. **Yes, the core claim is sound.**  
If `S` is dense in `Spec A` and every point of `S` is a genuine `k`-rational closed point, then any nonempty open subset, in particular the smooth locus, meets `S`. Choosing the smooth point from `S` indeed gives residue field `k`, not just some finite extension of `k`. The key is exactly that the point is taken from the dense set of orbit points, not from an arbitrary closed point of the smooth locus.

2. **Yes, `κ(m) ≃ₐ[k] k` is the right formalisation.**  
For an affine `k`-scheme of finite type, a `k`-rational point is equivalently a `k`-morphism `Spec k → X`, equivalently a maximal ideal `m` with residue field `κ(m)` isomorphic to `k` as a `k`-algebra. No separability subtlety appears here: if the residue field is literally `k`, separability is automatic. Over nonclosed fields, “closed point” alone is weaker, since closed points may have residue fields finite over `k`.

3. **Step 4 is airtight.**  
A `k`-algebra map `eval_P : A → k` is automatically surjective because it splits the structure map `k → A → k`. Its kernel is maximal, and the first isomorphism theorem gives
`A ⧸ ker(eval_P) ≃ₐ[k] k`. For a maximal ideal `m`, the residue field of `A_m` is
`A_m / mA_m ≃ Frac(A ⧸ m)`, and since `A ⧸ m` is already a field, this is just `A ⧸ m`. No algebraic-closedness is involved.

4. **Yes, the finrank conversion is exactly where rationality matters numerically.**  
For a regular local ring,  
`dim_κ(m/m²) = dim A_m`.  
As a `k`-vector space,
`dim_k(m/m²) = [κ(m) : k] · dim_κ(m/m²)`.  
So if `κ(m)/k` has degree `e > 1` and `dim A_m > 0`, the equality over `k` fails by the factor `e`. Thus `κ(m) ≃ₐ[k] k` is not decorative.

5. **No algebraic-closedness is secretly needed, given the stated hypotheses.**  
Generic smoothness/density of the smooth locus holds for finite-type reduced schemes over a perfect field. Algebraic closedness is unnecessary. The real hypotheses to check are: the orbit-point set is genuinely Zariski dense in `Spec A`, the evaluations really descend to `A`, and the group action preserves `I` so the transport automorphism descends to `A`. Infinite `k` is typically used to prove orbit-density statements for `G(k)`, but once density of `S` is established, the discharge is valid over `ℝ`, `ℚ`, etc.