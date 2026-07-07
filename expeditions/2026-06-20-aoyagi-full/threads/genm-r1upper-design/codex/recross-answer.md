**1. Soundness**

Bounded, with explicit assumptions.

The fix is sound: after enlarging the post-Schur `Γ` domain from the translated box to all of `R^{p×q}`, the shift term `S = C · Q̃_p` is handled by full-space translation invariance, and the anisotropy `R = Q_b` is handled by the right-multiplication Gram Jacobian.

One precision point: translation removes only the component of `S` in `row(R)`. The perpendicular component survives, giving exactly

```text
w + ‖S(I - P_R)‖²
```

not just `w`. Your residual keeps that term, so the cross-coupling is correctly retained.

The assumptions that must be named are:

```text
rank Q_b = M1 - t
c' > ((M0 - t)(M1 - t))/2
w + ‖S(I - P_R)‖² > 0   a.e.
```

With `w = ‖A Q̃_p‖²` and `A` invertible, positivity reduces to `Q̃_p ≠ 0`; `A` invertible alone does not prove that a.e.

**2. Split**

Yes, the split is the right one.

`sjBoundaryPeel` piece 3 should stop after:

```text
cover + Schur measure-preserving reparametrisation
```

and reduce the original box integral to a sum of `gammaPeelIntegral`s carrying the true integrand

```text
(‖A Q̃_p‖² + ‖C Q̃_p + Γ Q_b‖²)^(-c')
```

or equivalently the same expression with named `w,S,R`.

Then `gammaPeelIntegral` finiteness owns the analytic work:

```text
box Γ-domain ≤ full Γ-space
full-space shifted anisotropic atom
rank Q_b full-row-rank branch
rank-drop/null/recursive branch
```

So piece 3 is genuinely plumbing only if `gammaPeelIntegral` preserves the cross-coupled integrand. If piece 3 tries to replace it by `‖Γ Q_b‖²` or by an unshifted residual, the old error returns.

**3. Corrected Lemmas 5–7**

5. `gammaBox_le_fullSpace` — plumbing, but essential.

```text
∫_{Γ ∈ box/chartDomain} (w + ‖Γ R + S‖²)^(-c')
  ≤
∫_{Γ ∈ R^{p×q}} (w + ‖Γ R + S‖²)^(-c')
```

No rank assumption needed. This is the monotone box-to-full-space bound. The order matters: enlarge first, then use translation invariance.

6. `fullSpace_anisotropic_shifted_gamma_atom` — load-bearing analytic core.

For `R : q×n` full row rank, `c' > pq/2`, and positive core,

```text
∫_{Γ ∈ R^{p×q}} (w + ‖Γ R + S‖²)^(-c') dΓ
 =
Cinf(pq,c') · det(R Rᵀ)^(-p/2)
· (w + ‖S(I - P_R)‖²)^(-(c' - pq/2)).
```

This supersedes `matBox_corank_residual_le`: that old lemma is only the `R = I`, `S = 0`, box-bounded special case. Internally this lemma depends on the Gram Jacobian for `Γ ↦ ΓR` and full-space translation.

7. `gammaPeelIntegral_rankBranch_finite` — load-bearing assembly.

Apply 5 and 6 on the stratum

```text
det(Q_b Q_bᵀ) ≠ 0
```

and handle

```text
det(Q_b Q_bᵀ) = 0
```

explicitly: either prove it is null by a nonzero-polynomial certificate, or route it to the recursive deeper-boundary case. Do not globally assert nullity; in bottleneck architectures the determinant may be identically zero. Also handle the a.e. positivity of the core, not just invertibility of `A`.

**4. Remaining Risk**

The biggest risk is the full-row-rank/a.e. claim for the actual tail product `Q_b`, not the Gamma atom.

Cheapest exact check: for every chart `(t, κ)`, exhibit one concrete tail configuration with

```text
rank Q_b = M1 - t
Q̃_p ≠ 0
```

or prove the corresponding determinant polynomial is nonzero. If no such witness exists, that chart is not an atom chart; it must enter the recursive rank-drop branch.