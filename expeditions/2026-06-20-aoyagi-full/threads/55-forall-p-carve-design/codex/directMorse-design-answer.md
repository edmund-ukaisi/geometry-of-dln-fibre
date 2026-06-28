**1. Direct Bound**
Use the one-pivot Schur/Morse bound, not `‖R S‖ ≥ c‖S‖`.

Normalize the angular chart so the pivot is `R₀₀ = 1`, write
`S = (S₀, Sbot)` and `b_a = R₀,1+a`. The load-bearing lower bound is:

```text
c₀ * ( ∑ q, (S₀ q + ∑ a, b_a * Sbot a q)^2
       + frobSq(Sc * Sbot) )
  ≤ frobSq(R * S)
```

Then in cap-B, drop the residual term:

```text
frobSq(R*S)^(-c')
 ≤ c₀^(-c') *
   (∑ q, (S₀ q + ∑ a, b_a*Sbot a q)^2)^(-c')
```

Shear `S₀ ↦ T = S₀ + b*Sbot`; the shifted box is contained in `morseBox p (r*T)` (or `max 1 (r*T)`). Hence

```text
∫_{S₀} (...) ≤ ∫_{T∈morseBox p K} (∑q Tq^2)^(-c') < ⊤
```

for `c' < p/2` by the existing generic Morse leaf (`sumSqND_box_lt_top`). The remaining `Sbot` and angular-ratio variables are bounded boxes.

So the direct branch proves:

```text
angular finite for c' < p/2
radial finite for c' < r^2/2
⇒ SchurCore p r c' T for c' < min(p,r^2)/2.
```

Thus it proves the stated `c' < lam(r,p)` whenever you also have `lam(r,p) ≤ p/2` and the radial cap `lam(r,p) ≤ r²/2`. If you mean only “`t=0` binds” (`p ≥ 2r-1`), this is not enough above `p/2`.

**2. Kernel Subtlety**
No, `frobSq(R*S) ≥ c₀*frobSq(S)` is false. Example: `R = diag(1,0,...)`; any `S` with top row zero and nonzero lower rows gives `R*S = 0`.

The fix is transverse control: the pivot controls only the sheared top row `S₀ + b*Sbot`. Kernel directions remain, but in cap-B they are harmless finite-volume spectator variables.

**3. Decomposition**
Do not use `radial_loss_chart_lt_top` with a fixed-`S` lemma. Fixed-`S` finiteness fails at `S=0` and low-rank `S`, and even a.e. fixed-`S` finiteness loses the codimension in `S` needed for joint integrability.

Recommended lemmas:

- `frobSqTopRow_eq_shearP` [LOW]: p-general version of existing `Fin 4` top-row identity.
- `stepShearP_r` [MED]: p-general version of `stepShearG_r`, using `morseBox p`.
- `innerSGenP_directMorse_le_const` [MED]: N2b `j=1` lower bound + shear + drop residual; uniform in angular `z`.
- `schurRatioResidP_capB_lt_top` [LOW]: integrate the uniform inner bound over the bounded ratio box.
- `schurCoreP_directMorse` [MED]: p-parametric radial cover + radial axis + previous angular lemma.

Known in repo: `schur_minorPivot_split` is already p-parametric; `sumSqND_box_lt_top` is generic. INFERENCE: current `gFlatG`/`innerSGen`/row-permutation/shear wrappers are still mostly `p=4`, so p-parametric wrappers must be added.

**4. Likely Bite**
The main Lean bite is not the math; it is p-generalizing the existing `Fin 4` chart plumbing cleanly: `matBox r 4`, `morseBox 4`, row splits, row permutations, and shifted-box containment all need `Fin p` versions without breaking the existing p=4 firing.