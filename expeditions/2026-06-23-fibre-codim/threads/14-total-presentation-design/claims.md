# Claim cards — thread 14 (G2-3 total-presentation design)

## Claim G2-3-A — the chart trivialization `S ≅ R ⊗_k F_E` is the genuine object, via endpoint normalization

**Statement.** On the pivot chart of `Σ̄^r ⊆ Rep_d` (where the target pivot `r×r` minor `detΔ` of the
product is invertible), the total chart ring `S = O(Σ̄^r ∩ chart)` is, as an `R`-algebra (with
`R := Sd = O(target rank-locus chart)`, a regular ring of dim `δ = r(d_0+d_N−r)`), isomorphic to the
base change `S ≅ₐ[R] R ⊗_k F_E`, where `F_E = O(mult⁻¹(E))` is the fibre algebra over the normal form
`E = diag(I_r,0)`. The iso is built by **endpoint normalization**: write the chart target as
`B = L·E·H` (`L = [[Δ,0],[Q,I]]`, `H = [[I,Δ⁻¹P],[0,I]]` from the target Schur blocks), normalize the
first/last factors `Ã₁ = A₁H⁻¹`, `Ã_N = L⁻¹A_N` (middle factors unchanged); then `mult(A)=B ⇔
mult(Ã)=E`, transporting the cut ideal `(mult(A)−B_univ)` to `(mult(Ã)−E)`. Consequence: `R ⊗_k F_E`
is free over `R` (F_E free over the field k) ⟹ `S` flat over `R` ⟹ `HasGoingDown` ⟹
`height_eq_height_add_of_liesOver_of_hasGoingDown` gives `codim_{Σ̄^r}(fibre) = δ`.

**Hypotheses.** `k` alg. closed, char 0; `B` exact rank `r`; `r ≤ d k'` ∀k'; on the chart (pivot
minor invertible); `0 < N` (genuine product). The `+C` to reach `codim_{Rep}(fibre)=C+δ` needs a
separate minimal-prime/catenary assembly (NOT automatic from Brick A).

**Kill-condition (stated before confirming).** (i) The endpoint-normalization map fails to transport
`mult(A)=B` to `mult(Ã)=E` on some chart (e.g. middle factors must move, or `L,H` not invertible on
the chart). (ii) `S ≅ R ⊗_k F_E` fails to be FREE over R (F_E not free over k, or the tensor is not
the right object — e.g. the bundle is non-trivial on the chart). (iii) The "P minimal over fibre ideal
⟹ relative height 0 in `S/m_B S ≅ F_E`" step is unsound.

**Status:** stress-tested → survived (on the anchor). **Tier:** new.

**Evidence.** Endpoint normalization verified exact on `(2,2,2) r=1` (`L E H = B`; `Ã₂Ã₁ =
L⁻¹(A₂A₁)H⁻¹` ⟹ `mult(A)=B ⇔ mult(Ã)=E`). Dimension count `dim Σ̄^1(7) = dim R(3) + dim F_E(4)`
consistent with a trivial bundle. Going-down chain pinned to the LANDED
`height_eq_height_add_of_liesOver_of_hasGoingDown` (used in `FlatQuasiFiniteHeight`). Decorrelated
Codex (xhigh) independently proposed the SAME endpoint construction + flatness chain and confirmed the
minimal-prime step sound (`codex/q1q2-answer.md`). NOT YET stress-tested: F_E's own structure for N>2
(reducibility / freeness over k beyond the anchor's `ℓm=0`); whether the chart covers ALL fibre
components (it covers one pivot config — the `+C` assembly must range over all Σ̄^r-components).

---

## Claim G2-3-B (REFUTED) — the "complete-intersection / d_N·d_0" reserve route

**Statement (refuted).** `codim_{Rep_d}(mult⁻¹ B) = d_N·d_0` for B of exact rank r (the fibre is a
complete intersection cut by its `d_N·d_0` product equations), giving `codim = C+δ` directly without
flatness.

**Kill-condition (stated before confirming).** A target rank `r` where the fibre has a component of
codim `< d_N·d_0` (so `d_N·d_0` is not the true codim), or where `d_N·d_0 ≠ cCodim_{Rep}(Σ̄^r) + δ`.

**Status:** REFUTED. **Tier:** new.

**Evidence (refutation).** `d_N·d_0 = (d_N−r)(d_0−r) + δ` is an algebraic IDENTITY, but
`(d_N−r)(d_0−r) = C_single` is the codim of the TARGET `Mat^{rk≤r}` in `Mat`, NOT the BundleShift
target's `C = cCodim_{Rep}(Σ̄^r)` (the type-A quiver combinatorial codim in `Rep_d`). These agree only
when `Σ̄^r` has the same codim in `Rep_d` as the target rank locus has in `Mat`. **This FAILS at r=0**:
for `(2,2,2)`, the repo's LANDED `codimRepCanonical (fibre d222 0) = 3` (dim Σ̄^0 = 5), while
`d_N·d_0 = 4`. So `mult⁻¹(0)` is NOT a complete intersection and `d_N·d_0` is the wrong codim.
Generic-Jacobian evidence for r≥1 is a CONFOUND: a full-rank Jacobian at one smooth point certifies
only ONE component locally (Krull gives the wrong-direction bound; the lower bound IS the content), and
cannot rule out lower-codim components — exactly the r=0 failure mode. Decorrelated Codex (Q3)
independently rejected this route for the same reasons. **Do not re-explore.**
