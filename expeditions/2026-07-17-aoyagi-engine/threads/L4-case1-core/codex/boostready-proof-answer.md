## 1. Verdict: needs a stronger invariant, not merely a proof lemma

The theorem does not follow from the present hypotheses. The formal `CanonicalSchurStep` is too weak:

```lean
CanonicalSchurStep d s shearφ :=
  ∀ u k, shearφ u k ≠ 0 → k lies in the strict carve
```

In particular, `shearφ := 0` satisfies it vacuously. It also satisfies `ShearWithinCarveRaw`; `blockShear 0 = id`. Thus an omitted Schur preparation is still admitted by the current [`IsRealBranch`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4wire/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:833).

This is precisely the bad branch: the identity/unprepared earlier shear leaves an untouched coefficient without the reused-pivot factor. It can still satisfy `hslot`, because it remains affine in the full layer block.

Two further points make the gap exact:

- The projected `CanonicalSchurStep` concerns `ed.shearφ`, but case11 uses `edgeShearRaw = id`; the current shear is irrelevant to `foldResid p`.
- Although `hbranch` recursively contains canonicality predicates for earlier edges, those predicates record only support, not the equation
  `shearφ = canonShearOf ...`. Hence [`canonShearOf_apply_interior`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4wire/lean/DLNFibre/DLN/Aoyagi/CanonShear.lean:244) cannot rewrite any stored shear.

The branch pin should retain, at least for case12/case2,

```lean
shearφ = canonShearOf d p.conState
```

The producer already works from exactly this equality in [`canonShearOf_shearWithinCarve`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4wire/lean/DLNFibre/DLN/Aoyagi/CanonShear.lean:160); it is currently forgotten when `IsRealBranch` is constructed.

After that repair, the missing path-induction lemma should existentially produce prepared coefficients. It must not claim divisibility of an arbitrary `hslot` witness, since support decompositions are non-unique.

```lean
def Case11BChainCoeffs {D : ℕ}
    (F : (Fin D → ℝ) → ℝ) (S C : Finset (Fin D)) (q : Fin D) : Prop :=
  q ∈ C ∧ q ∉ S ∧
  ∃ a b : Fin D → (Fin D → ℝ) → ℝ,
    (∀ i, Continuous (a i)) ∧
    (∀ i, Continuous (b i)) ∧
    (∀ u, F u = ∑ i ∈ S, a i u * u i) ∧
    (∀ i ∈ S ∩ C, IgnoresCoords (a i) C Set.univ) ∧
    (∀ i ∈ S \ C,
      (∀ u, a i u = u q * b i u) ∧
      IgnoresCoords (b i) C Set.univ)
```

The deep missing theorem is then:

```lean
theorem realBranch_case11_bChainCoeffs
    (hδ : edgeδ d p = true) (hc11 : ed.case = .case11)
    (hbranch : (p.extend ed).IsRealBranch e) -- with exact recursive shear pin
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    ∀ j, Case11BChainCoeffs
      (foldResid d e p j)
      (supportAt d p.conState.layer p.conState.cleared)
      ed.center ed.pivot
```

This is the path induction over the earlier canonical Q/Schur shears. Alternatively, `Case11BChainCoeffs` must be carried as an additional fold invariant.

A small combinatorial helper will also be needed:

```lean
ed.pivot ∉ supportAt d p.conState.layer p.conState.cleared
```

for real δ=1 case11 edges.

## 2. Conditional final assembly

Let `S := supportAt ...`, `C := ed.center`, `q := ed.pivot`, and obtain `a,b` from the missing lemma. Define

```lean
let c' := fun i u =>
  if i = q then
    ∑ k ∈ S \ C, b k u * u k
  else if i ∈ S then
    a i u
  else
    0
```

Then:

- Continuity at `q` is a finite sum of `(b k) * continuous_apply k`.
- At a partial-block index it is continuity of `a i`.
- Else it is constant zero.
- Splitting the sum over `C` at `q` gives
  \[
  \sum_{i\in S\cap C}a_i(u)u_i
  +u_q\sum_{i\in S\setminus C}b_i(u)u_i
  =F(u).
  \]
- For `c' q`, updating `m ∈ C` leaves every `b k` fixed, and `k ∈ S \ C` gives `k ≠ m`, so `u k` is unchanged.
- Partial coefficients ignore `C` by the prepared-coefficient lemma; zero coefficients are immediate.

After `rw [foldRegion_eq_univ e p]`, these give the required `ContinuousOn`, representation, and `IgnoresCoords` clauses.

## 3. Drop-test: `hslot` is genuinely consumed

No: `hbranch + CanonicalSchurStep` alone does not imply center factoring.

`hslot` supplies the continuous full-support decomposition and the affine grade. The branch predicates only constrain coordinate changes; they do not supply root linearity or even membership of `foldResid p j` in the full support ideal. The repository already records that root linearity is anchored through the carried slot invariant, not through branchhood ([MonumentAtlas.lean:1107](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4wire/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:1107)).

Therefore the weakest honest leaf retains `hslot` plus a separate b-chain compatibility fact. If `BChainCompatible` is defined to include the entire support decomposition, it may subsume `hslot`, but that merely moves the hypothesis into the stronger invariant.