Recommendation: use a deterministic exponent ledger and existential “clean” coefficients.

```lean
abbrev Coord := Fin D → ℝ

-- Inferred: every outgoing center is contained here.
def ledgerCenter (p) : Finset (Fin D) :=
  supportAt p ∪ couplingCoords p

-- Path-combinatorial data, not existential witnesses.
def μ (p) (r : Row) : Fin D →₀ ℕ := ...
def b (p) (r) (u : Coord) : ℝ :=
  (μ p r).prod fun k m => (u k)^m

def INV (p : TreePath d) : Prop :=
  ∃ q : Fin (nR p) → Fin D → Coord → ℝ,
    -- DECOMPOSITION
    (∀ j u,
      sourceClearedResid d p j u =
        ∑ i ∈ supportAt p, b p (rowOf i) u * q j i u * u i) ∧

    -- REGULARITY
    (∀ j i, Continuous (q j i)) ∧

    -- CLEAN-DEPENDENCY
    (∀ j i,
      IgnoresCoords (q j i) (ledgerCenter p) Set.univ)
```

Global continuity/ignoring is the safest inductive form; use `ContinuousOn ... V` only if every shear and blow-up substitution preserves `V`.

The key IgnoresCoords target is the path-dependent ambient set
`ledgerCenter p = supportAt p ∪ couplingCoords p`, not the particular next `ed.center`. One proves the combinatorial lemma

```lean
ed.center ⊆ ledgerCenter p
```

for every admissible outgoing edge. Thus clean coefficients ignore any subsequently selected center. This containment is an inference from your description; if centers contain further coordinates, `ledgerCenter` must be enlarged to the smallest path-defined, transport-stable set covering every outgoing center.

Use an explicit `Finsupp` exponent ledger, with case-1(1) laws:

```lean
i ∈ part  → (μ p (rowOf i)).restrict ed.center = 0
i ∈ extra → (μ p (rowOf i)).restrict ed.center = single e₂ 1
```

Hence, for `i ∈ part`, take `α i = bᵢ*qᵢ`; for `i ∈ extra`,
`bᵢ = u e₂ * bᵢ.erase e₂`, so take `β i = (bᵢ.erase e₂)*qᵢ`.
The restricted-exponent laws and clean-dependency imply both normalized coefficients ignore `ed.center`.

Induction obligations:

- Root: expand the relevant matrix-product entry linearly in its active-layer coordinates; its cofactors ignore that whole layer, and `μ = 0`.
- δ=1: strict-transform cancellation subtracts the guaranteed pivot exponent and transports the clean coefficient through the shear.
- δ=0: blow-up substitution adds the pivot exponent to precisely the affected ledger rows and preserves the updated clean-dependency set.

Trap: the raw extra coefficient `cᵢ = u e₂ * βᵢ` cannot itself ignore `ed.center` when `e₂ ∈ ed.center`; only `βᵢ` and the clean factor do. Also, bare divisibility witnesses are too weak for strict-transform cancellation. Ranking: explicit exponent ledger first; explicit arbitrary `b` witnesses second; per-coordinate divisibility certificates last.