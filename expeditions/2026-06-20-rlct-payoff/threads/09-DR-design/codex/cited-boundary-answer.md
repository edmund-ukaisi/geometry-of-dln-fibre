**FACT:** The analytic content in the paper is not derived from the codimension calculation alone. Section 8 defines `rlct`, states the general upper bound `rlct(F) ≤ codim F⁻¹(0)/2`, defines the DLN loss with zero set the fibre, and then imports Aoyagi’s computation to state Theorem 8.6: `rlct(K_B^DLN) = codim mult⁻¹(B)/2`. ([arxiv.org](https://arxiv.org/pdf/2411.19920))

**INFERENCE: minimal cited interface**

Design A, recommended:

- Opaque external invariant: `dlnRLCT(d, B)`, documented as “the real log-canonical threshold of `K_B^DLN` in the sense of Definition 8.1.”
- One cited theorem/axiom, schematically:
  `cited_LR_Aoyagi_8_6(d, B, r): rank(B)=r, r≤min(d) -> dlnRLCT(d,B) = fibreCodim(d,B)/2`.

Then your in-engine theorem proves:
`dlnRLCT(d,B) = (C_geom(d,r) + r(d₀+d_N-r))/2`
using your formalised fibre-codim shift.

Do **not** include the general bound in the minimal interface. It is true and cited, but it is not needed to prove the equality once Theorem 8.6 is the imported analytic theorem.

Design B, only if you want to expose the “saturates the general bound” narrative:

- Opaque `rlct`.
- Cited global bound:
  `rlct_upper_bound_global(F): rlct(F) ≤ codim(F⁻¹(0))/2`.
- Cited DLN lower bound:
  `aoyagi_dln_lower_bound(d,B): fibreCodim(d,B)/2 ≤ rlct(K_B^DLN)`.

Then equality follows in-engine by antisymmetry. But the lower bound is essentially the Aoyagi analytic computation; do not present it as coming from the codimension formalisation.

More faithful to “name = content”: **Design A**, provided the axiom is named after LR Theorem 8.6 / Aoyagi, not as a generic codimension-to-rlct principle. Design B is more modular, but it can misleadingly make the equality look assembled from a general theorem plus geometry, when the decisive lower bound is still external analytic content.

**What Is Proved**

After plugging in your geometric `C`, the Lean theorem proves nontrivial algebraic transport only if the cited axiom stops at `fibreCodim(d,B)/2`. The analytic statement `rlct = half codim` is imported.

If instead the cited axiom already says `dlnRLCT(d,B) = (C_geom + shift)/2`, the final theorem is a pure restatement. That is still honest if clearly named `cited_...`, but it contributes no additional formal verification beyond bookkeeping.

**Main Guard**

The biggest misleading version would be a theorem named/scoped like `rlct_eq_half_codim` for arbitrary nonnegative analytic functions, or a theorem suggesting the codimension proof implies the RLCT equality. Guard against this by restricting the cited theorem to the DLN loss, feasible rank assumptions, and a name such as `cited_LR_Aoyagi_dln_rlct_eq_half_fibreCodim`.

**θ**

No. The component count `θ` is not the RLCT and is not the RLCT multiplicity; the paper explicitly says there is no simple relationship between the RLCT multiplicity and the number of irreducible components. ([arxiv.org](https://arxiv.org/pdf/2411.19920))