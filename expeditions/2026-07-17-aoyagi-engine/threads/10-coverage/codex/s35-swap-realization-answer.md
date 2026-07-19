### 1. RECOMMENDED OPTION

**Option A.** It works for every `d`, avoids the unproved condition `d ∈ range (cNodeOf …)`, and preserves each chart image—not merely the union.

Option B is correct only after proving that range condition. Option C destroys the pivot-indexed tiling used by the cover proof.

### 2. COMPOSITION ORDER

Let `E := paramsEquivFlatCLE M` and
\[
(P_{p,d}x)(c):=x(\operatorname{swap}(p,d)(c)),\qquad
S_{p,d}:=E^{-1}\circ P_{p,d}\circ E.
\]

Use
\[
\boxed{\beta_p\circ S_{p,d}}
\]
and, with gauge `γ`,
\[
(\beta_p\circ S_{p,d})\circ\gamma ,
\qquad \gamma=\mathrm{id}\text{ currently}.
\]

Indeed,
\[
z_p(S_{p,d}w)
 =(P_{p,d}(Ew))(p)
 =(Ew)(d)
 =z_d(w).
\]

Thus the swap is on the **source immediately before** `β`. Using `S ∘ β` would leave the Jacobian atom reading `z_p`.

### 3. (C1)/(C2)/(C3) DISCHARGE

**(C1).**
\[
|\det D(\beta_p\circ S)(w)|
 =|\det D\beta_p(Sw)|\,|\det S|
 =|z_p(Sw)|^{dCN-1}
 =|z_d(w)|^{dCN-1}.
\]

Use:

- `clm_involutive_abs_det_one` for `|det S| = 1`;
- `clm_det_comp` plus the banked per-edge determinant atom;
- or `abs_det_fderiv_comp_det_one_gauge` only if its hypothesis is **absolute** determinant one.

New lemmas are needed showing `S` is involutive and `z_p (S w) = z_d w`. A genuine transposition has determinant `-1` when `p ≠ d`, so a theorem requiring `det S = 1` literally does not apply.

**(C2).** Prove the new cube lemma
\[
S_{p,d}''\mathrm{cube}=\mathrm{cube}.
\]
Uniform bounds are preserved because `S` merely permutes flat coordinates; involutivity gives equality from forward preservation. Hence, separately for every pivot,
\[
(\beta_p\circ S_{p,d})''\mathrm{cube}
 =\beta_p''\mathrm{cube}.
\]
The existing cover is therefore unchanged chart-by-chart.

Option B would have the same property, but only after producing a center index mapping to `d`.

**(C3).** Keep `S` inside the modified chart, not in the gauge slot. With `γ = id`,
\[
\gamma^{-1}(\mathrm{cube})=\mathrm{cube}.
\]
Even if the domain is viewed through `S`, cube invariance gives the same set.

### 4. BIGGEST CORRECTNESS RISK

Placing the swap on the target—`S ∘ β`—instead of the source—`β ∘ S`. Target swapping is determinant-neutral but does **not** change the exceptional factor: it remains `|z_p(w)|^{dCN-1}`.