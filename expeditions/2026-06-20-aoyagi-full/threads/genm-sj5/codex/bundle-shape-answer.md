1. **FACT:** An existential matrix \(Z\) unconnected to `D`, `decLoss`, or `ctx` imposes no constraint on the decoration. For matrices \(Z:n\times D_{\mathrm{col}}\), such a positive lower bound exists whenever the dimensions permit full row rank—for example, using an identity embedding—and is impossible when they do not. Thus it detects only an ambient dimension inequality, not faithfulness of the residuals. **JUDGEMENT:** It is vacuous for this invariant and should be dropped unless accompanied by an equation identifying \(Z\) with the actual tail factor in `decLoss`.

2. **FACT:** A single fixed \(Z\) is not faithful at intermediate arities, because the actual candidate is the parameter-dependent tail product \(Z_{\mathrm{tail}}(y)\). A family satisfying \(Z_{\mathrm{tail}}(y)Z_{\mathrm{tail}}(y)^{\mathsf T}\succeq cI\) uniformly on all of `dom` is also impossible when the stated rank-dropping sublocus lies in `dom`. Moreover, the banked lemma applied separately for each \(y\) gives pointwise finiteness, which alone does not prove integrability over \(y\). **JUDGEMENT:** The correct invariant-level object is therefore option (iii): carry the actual varying tail family and its structural relation to the residuals, without global ellipticity. **FACT:** At width two the tail parameter disappears and the empty product specializes to the single fixed matrix \(I\), so `corankLeaf` can be instantiated with \(Z=I\) and \(c=1\). Uniformly full-rank sector families are a possible additional local construction, but not the global invariant described here.

3. **FACT:** At intermediate arity, the dimension of a front free block represents only the front contribution to `minAdm`. Under the given recursion,
\[
\minAdm(M)=N_{\mathrm{front}}+\minAdm(M_{\mathrm{tail}}),
\]
so \(N_{\mathrm{front}}=\minAdm(M)\) generally fails whenever the tail contribution is nonzero. **JUDGEMENT:** Carry the front block and its actual dimension, but not its equality with the total threshold dimension. **FACT:** At width two there is no tail, and genuine carriage identifies the active block with the single \(M_0\times M_1\) matrix; hence \(N_\Gamma=M_0M_1=\minAdm(M)\) is derived there.

4. **FACT:** Writing \(\delta_{i\ell}=\operatorname{supp}(i,\ell)-k_\ell\), exact factorization gives
\[
\operatorname{decLoss}
 =\operatorname{commonDiv}(u)^2
   \sum_i\left(\prod_\ell |u_\ell|^{\delta_{i\ell}}\operatorname{res}_i(z)\right)^2.
\]
Thus leftover monomials generally remain, and the residual block is still \(u\)-dependent after extracting the common divisor. A clean Frobenius expression requires all coordinates used for that block to have \(\delta_{i\ell}=0\), or at least a full spanning subset with zero leftovers if only a lower bound is needed. **FACT:** A sector inequality such as \(|u_1|\le |u_0|\) supplies monomial comparisons, not an exact \(u\)-independent identity; even a corner substitution normally leaves powers of the new ratio variable. **JUDGEMENT:** The clean form is justified only on a terminal uniformly supported block, or after a sector construction that proves such a block; otherwise the base needs an anisotropic leaf estimate stronger than the banked `corankLeaf`.

5. **JUDGEMENT:** The \(d\ge1\) clause should be a structural provenance certificate, not an assertion of global nondegeneracy. It should expose a measure-compatible front/tail decomposition, the actual family \(Z_{\mathrm{tail}}(y)\), and the exact support-weighted residual identity. It should also retain the exceptional-variable charge needed after extracting `commonDiv`; for the separated estimate this is \(\operatorname{jac}_\ell+1\ge k_\ell\minAdm(M)\). **FACT:** Neither fixedness of the tail nor `dim Γ = minAdm M` belongs at intermediate arities. At the base, fixed \(Z=I\), its PSD bound, and the dimension equality are consequences rather than witnesses. **FACT:** No supplied assumption guarantees that the accumulated supports are uniformly terminal at width two. Therefore one must separately prove a full minimal-support block at the base, or replace the clean Frobenius leaf argument with an anisotropic one.

## MINIMAL FAITHFUL SHAPE

Data:

- **[CARRY]** Front/tail coordinates \((y,\Gamma)\), with \(\Gamma\) the genuine free active matrix block and \(y\) containing the actual spectators/tail parameters.

- **[CARRY]** The actual family \(Z_{\mathrm{tail}}(y)\), explicitly identified through `ctx`/`genuineCarrier` with the deeper product—not a new unconstrained matrix.

- **[CARRY]** Generator-to-product-entry correspondence and leftover exponents
  \(\delta_{i\ell}=\operatorname{supp}(i,\ell)-k_\ell\).

- **[CARRY]** If the descent is sectorwise, the sector/chart map and its Jacobian/support transformation.

Propositions:

- **[CARRY]** Measure compatibility sufficient for Fubini or domination by a fixed matrix box; a global measure isomorphism to only `matBox` is stronger than necessary.

- **[CARRY]** The faithful weighted identity
  \[
  \operatorname{decLoss}(u,\phi(y,\Gamma))
  =\operatorname{commonDiv}(u)^2
   \sum_i\bigl(u^{\delta_i}[\Gamma Z_{\mathrm{tail}}(y)]_{\rho(i)}\bigr)^2.
  \]

- **[CARRY]** The exceptional-coordinate charge condition needed for
  \(\int_0^1u_\ell^{\operatorname{jac}_\ell-2c'k_\ell}\,du_\ell<\infty\).

- **[DERIVE-AT-BASE]** The tail is empty, so \(Z_{\mathrm{tail}}=I\), fixed, with \(II^{\mathsf T}\succeq I\).

- **[DERIVE-AT-BASE]** \(\dim\Gamma=M_0M_1=\minAdm(M)\).

- **[DERIVE-AT-BASE]** Either a full set of zero-leftover generators yields
  \(\operatorname{decLoss}\ge\operatorname{commonDiv}^2\operatorname{frobSq}(\Gamma)\), or an anisotropic leaf theorem is required. This terminal coverage is not forced by the supplied facts.

- **[DROP]** An existential \(Z\) unrelated to `decLoss`.

- **[DROP]** Uniform positive definiteness of the varying tail on all intermediate domains.

- **[DROP]** A clean \(u\)-independent Frobenius identity at every arity.

- **[DROP]** `dim Γ = minAdm M` as an all-arities invariant.