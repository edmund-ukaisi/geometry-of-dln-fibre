# Design review: the concrete IFT chart Φ + invertible f' + germ for the DLN D1 hchart

I am formalising in Lean 4 + Mathlib v4.29. I have a banked abstract chart-transfer theorem and need
to construct its concrete inputs for a deep-linear-network (DLN) loss. I want a decorrelated sanity
pass on the cleanest CONSTRUCTION before I spend multi-tide compute. Pure math design question; no
Lean syntax needed in your answer (prose + the key linear-algebra identities is ideal).

## The setting

- `L = 2`. Widths `H : Fin 3 → ℕ`. Params `= Mat_{H0×H1} × Mat_{H1×H2}` (layer matrices `A¹, A²`).
- Loss `dlnLoss H B A = ∑_{i,j} g_ij(A)²` where `g_ij = (A¹·A² − B)_ij`, summed over ALL
  `i ∈ Fin H0, j ∈ Fin H2` (so `H0·H2` terms total).
- I flatten Params to `ℝ^N` (`N = flatDim H = H0·H1 + H1·H2`) via a measure-preserving linear
  coordinate reindex, and translate the optimal point `v` to the origin. Call the flat origin-centred
  loss `f : ℝ^N → ℝ`, `f(w) = dlnLoss(flatSymm(w + flat v))`. So `f(0) = dlnLoss(v) = 0` (v optimal,
  `A¹_v · A²_v = B`, `rank B = r`).
- `f` is `C^∞` (built, entry-wise). Each `g_ij` in flat coords is a polynomial; `∇g_ij(0)` acts on a
  flat tangent `(δ¹, δ²)` by `(δ¹ A²_v + A¹_v δ²)_ij`.

## What I have banked (all sorry-free, axiom-clean)

The abstract chart-transfer:
> `rlctAtOn_eq_of_contDiff_chart (f F : ℝ^N → ℝ) (Φ : ℝ^N → ℝ^N) (wstar : ℝ^N)`
> `(f' : ℝ^N ≃L[ℝ] ℝ^N) (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ f' wstar)`
> `(hfix : Φ wstar = wstar) (hgerm : f =ᶠ[𝓝 wstar] F∘Φ) : rlctAtOn f wstar = rlctAtOn F wstar`.

So I supply `f'` as a genuine `ContinuousLinearEquiv` (invertibility is already encoded), construct
`Φ`, and discharge `hΦ`, `hΦ'`, `hfix`, `hgerm`.

## The DOWNSTREAM consumer (the exact target shape)

The engine slot I must hit (`hchart`) is, with `nReg := nRegL2 H r = r(H0+H2−r)` and `Y` a free
finite-dim real normed/measure space I get to CHOOSE:
> `rlctAt H (dlnLoss H B) v = rlctAtOn (fun p : (ℝ^nReg) × Y => (∑_i p.1 i² ) + (∑_i q(p) i²)) (0, t0)`
> where `q : (ℝ^nReg) × Y → ℝ^n` is `ContDiff ℝ 1`, `t0 : Y`.

So the post-chart loss must split as `∑ (nReg selected square-coords) + ‖residual q‖²`, with q only
C¹. My flatten bridge already gives `rlctAt(dlnLoss)(v) = rlctAtOn f 0` and a banked
`dln_hchart_flat` that, GIVEN `(F, Φ, f', hΦ, hΦ', hfix, hgerm)`, yields `rlctAt(dlnLoss)(v) =
rlctAtOn F 0` on ℝ^N. A final MP reindex `ℝ^N ≅ ℝ^nReg × Y` (with `Y = ℝ^(N−nReg)`) carries
`rlctAtOn F 0` to the product form.

## The verified rank fact (H_indep, BOUNDED, general-v)

At every optimal `v`: `dim {δ¹ A²_v + A¹_v δ²} = nReg_v ≥ nReg`. So an independent nReg-subfamily of
`{∇g_ij(0)}` always exists. I have, per loss entry, the explicit strict-derivative functional
`∇g_ij(0) : ℝ^N →L[ℝ] ℝ` (banked Leibniz gradient).

## My proposed construction (please critique / improve)

1. Pick the nReg "selected" index pairs `S ⊆ {(i,j)}` so that `{∇g_k(0) : k ∈ S}` is linearly
   independent (extract via `exists_linearIndependent'` from the nReg-dim image). Define the selected
   map `G : ℝ^N → ℝ^nReg`, `G(w)_k = g_k(w)`, so `DG(0) = (∇g_k(0))_{k∈S} : ℝ^N → ℝ^nReg` is
   SURJECTIVE (rank nReg).
2. Complete to a chart: choose a complement projection `P : ℝ^N → ℝ^(N−nReg)` (a coordinate
   projection onto N−nReg flat coords whose differentials complete the `∇g_k(0)` to a basis of
   `(ℝ^N)*`). Set `Φ(w) = (G(w) − G(0), P w) ∈ ℝ^nReg × ℝ^(N−nReg) ≅ ℝ^N`. Then `Φ(0) = 0` and
   `DΦ(0) = (DG(0), P)` is a linear ISO (the differentials form a basis) → `f'` the CLE.
3. `F := f ∘ Ψsymm` where `Ψ = Φ` locally (pull the loss back through the chart inverse). Then `hgerm:
   f =ᶠ F∘Φ` is automatic near 0. The CONTENT is showing `F(s, y) = ∑_{k∈S} s_k² + ‖q(s,y)‖²` with q
   C¹: because the selected coords ARE the selected `g_k` (Φ's first block), `∑_{k∈S} g_k² ∘ Ψsymm =
   ∑ s_k²`, and the non-selected `g_α² ∘ Ψsymm` collect into `‖q‖²`, q = (non-selected g) ∘ Ψsymm,
   which is C¹ (actually C^∞, but C¹ suffices) since Ψsymm is C¹ (IFT) and g is C^∞.

## Questions

Q1. Is route (3) — DEFINE `F := f∘Ψsymm`, making the germ trivial, content shifts to F's form — the
    cleanest? Or is it better to define `F` explicitly as `∑ s_k² + ‖q‖²` with an independently-built
    `q` and PROVE the germ? The risk with (3): `Ψsymm` is only defined/`C¹` on a NEIGHBOURHOOD (IFT
    local inverse), and `rlctAtOn F 0` needs F defined globally-ish or at least the germ to make
    sense. Does the banked transfer (which already produces a bounded-unit local diffeo Ψ on an open
    V∋0) make `F := f∘Ψsymm` legitimate, or do I hit a "F not defined off V" snag?

Q2. The selected-coordinate identity `g_k ∘ Ψsymm = π_k` (k-th coordinate) on the image — is that
    EXACTLY right? Φ's first block is `w ↦ G(w) − G(0)`, so `(Φ w).1 k = g_k(w) − g_k(0)`. Since
    `g_k(0) = (prod v − B)_k = 0` (v optimal!), `(Φ w).1 k = g_k(w)`. So `Ψ(w).1 = G(w)`, hence on
    the image `g_k(Ψsymm(p)) = p.1 k`. Confirm `g_k(0) = 0` ∀k (all loss entries vanish at an optimal
    v, not just selected) — I believe yes since `prod v = B` exactly. This is what makes
    `∑_{k∈S} g_k² ∘ Ψsymm = ∑ s_k²` clean. Any trap?

Q3. The residual q in the consumer is over `ℝ^nReg × Y`. Under (3), `q(s,y) = (non-selected
    g)(Ψsymm(reindex⁻¹(s,y)))`. The consumer needs q `ContDiff ℝ 1` GLOBALLY (its signature is a
    total function `ℝ^nReg × Y → ℝ^n`), but Ψsymm is only local. How is this normally reconciled —
    does `rlctAtOn` only see the germ at 0 so a global C¹ extension (e.g. via a cutoff, or by noting
    rlctAtOn depends only on the germ) is fine? Is there a cleaner global-q construction that avoids
    extending Ψsymm?

Q4. Biggest risk to flag: which of steps {independent-family selection, the iso f', the germ, the
    global-C¹ residual, the MP product reindex} is most likely to be the multi-tide grind or hide a
    false statement? Where would you put the 3-attempt-then-surface watch?

Please be concrete and adversarial — I would rather hear "route (3) breaks at Q3 because rlctAtOn
needs a global function and you cannot extend Ψsymm cheaply" now than discover it after two tides.
