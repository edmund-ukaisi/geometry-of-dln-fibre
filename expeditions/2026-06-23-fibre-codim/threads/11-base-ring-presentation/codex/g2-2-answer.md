**Verdict**
(a) **GO, but not from point-bijection alone.** You do **not** need `I(Σ̄^r)=I_{r+1}`.  
(b) **NO-GO as currently stated from only the listed Lean ingredients.** The chain needs at least one missing height-additivity theorem, or a stronger direct local-coordinate computation.

**(a) Localized Base Presentation**
You can avoid determinantal generators by using a one-sided containment plus height.

Let `d = det Δ`, `S = k[Δ,B12,B21]`, and in `A_d = S_d[B22]` define the Schur graph ideal
```text
J = ( B22_ab - (B21 adj(Δ) B12)_ab / d ).
```
Then `A_d / J ≅ S_d`, and `J` is prime of height `(p-r)(q-r)=C`.

To prove `(I(Σ̄^r))_d = J`, it is enough to show `J ⊆ I_d` and compare heights:

- On `Σ̄^r ∩ D(d)`, the matrix has rank exactly `r`, so G2-1 gives the Schur equations.
- For each polynomial numerator `g_ab = d B22_ab - (B21 adj(Δ) B12)_ab`, the product `d*g_ab` vanishes on all of `Σ̄^r`: on `D(d)` by G2-1, and on `V(d)` trivially.
- Since `I(Σ̄^r)` is the vanishing ideal, `d*g_ab ∈ I`; after localizing at `d`, `g_ab ∈ I_d`, so `J ⊆ I_d`.
- Both `J` and `I_d` are prime of height `C`; strict inclusion of finite-height primes strictly raises height. Hence equality.

This is generator-free and avoids Nullstellensatz if you use the height comparison. It uses your landed height of `I`, localization height transport, and an explicit height computation for `J`.

But: a bijection on `k`-points plus irreducibility plus equal dimension is **not** enough. Standard counterexample: normalization `A¹ → Spec k[x,y]/(y²-x³)` is bijective over algebraically closed `k` of characteristic `0`, source and target are reduced irreducible curves, but it is not an isomorphism. To upgrade a bijective morphism abstractly you would need something like “finite birational to a normal target” or “quasi-finite birational to a normal target” via Zariski’s Main Theorem. You do not need that here.

Mathlib status: no determinantal generator theorem needed. You still need to formalize the explicit Schur ideal `J`, its quotient `A_d/J ≅ S_d`, and its height `C`. Those are local polynomial/localization facts, not determinantal theory.

**(b) Height Composition**
As written, **NO-GO with only** primality/dimension of `R_base`, the polynomial bridge, flat implies going-down, and height transport.

Step 1 is genuinely a codimension-additivity statement:
```text
ht_R Q = ht_R I_X + ht_{R/I_X}(Q/I_X)
```
for `I_X ⊂ Q` in the polynomial representation ring. That is the catenary additivity of codimension. The polynomial-ring bridge `ht(P)+dim(R/P)=N` applied to `I_X` and `Q` does not by itself identify `ht_{R/I_X}(Q/I_X)` with the dimension drop inside `R/I_X`.

Step 2 is true under standard hypotheses, but not from going-down alone. The theorem you need is the **dimension formula for flat local homomorphisms**: for a noetherian flat local map `A_p → B_P`,
```text
ht_B P = ht_A p + ht_{B/pB}(P/pB).
```
No Cohen-Macaulay or equidimensional-fibre hypothesis is needed for this local flat formula. If `P` is minimal over `m_E B`, the fibre term is `0`, so `ht_B P = ht_A m_E`. Mathlib having `HasGoingDown.of_flat` is not enough; going-down gives the chain-lifting direction, not the full additive identity.

Also, `ht_A m_E = δ` is true for a closed point on an irreducible affine `δ`-fold, by the affine dimension theorem/Noether normalization plus Nullstellensatz. In Lean, the clean way to avoid global catenary is to use the chart equivalence from (a): if `d(E) ≠ 0`, transport `m_E` to a maximal ideal in the polynomial localization `S_d`, where its height is `δ`.

Chart localization is sound **only if `E` lies in the chart**. If `d(E) ≠ 0`, then every prime over `m_E B` avoids `d`, because `d` becomes the nonzero scalar `d(E)` in the fibre. So no fibre component is missed. If `E` has rank `r`, choose a nonzero `r×r` minor as pivot. If `rank E < r`, no such chart exists; the argument breaks, and fibre dimension jumping is exactly the obstruction.

**Simpler Architecture**
Avoid the abstract catenary step by proving a stronger local coordinate theorem in the localized representation ring: normal Schur coordinates cut out `mult⁻¹(Σ̄^r)`, and the `δ` base coordinates cut out `E`. Then the fibre is locally defined by `C+δ=pq` coordinate equations, and height follows directly by polynomial/localization height transport. This avoids determinantal generators and general catenary, but it requires that explicit total-space local product/coordinate presentation.