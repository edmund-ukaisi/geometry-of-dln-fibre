# The two θ-invariants are not the same number

Two quantities in this repository have both been called "θ", and they are **different
invariants**. This note is the durable record of the distinction; it exists because the
conflation survived in `ROADMAP.md` until 2026-07-19, when a decorrelated paper-first audit
produced a counterexample that was then machine-verified.

## The two invariants

**The geometric component count** (Lehalleur–Rimányi, this repo's Bundle 1). For a dimension
vector $d$ and rank bound $r$, the number of top-dimensional irreducible components of the
locus $\bar\Sigma^r$:

$$\theta_{\mathrm{geo}} \;=\; \binom{m}{|\delta|},$$

with $m$ the active-support threshold and $\delta$ the rounding residue of the quadratic
integer program. In Lean: `DLNFibre.Core.numTop` (geometric) and its closed form
`DLNFibre.Core.cTheta` (proved equal via the QIP minimiser count).

**The RLCT pole order** (Aoyagi, Lemma 5 of her resolution analysis). The multiplicity of the
pole of the zeta function at $-\lambda$:

$$r_{\mathrm{order}} \;=\; a(\ell-a)+1,$$

with $\ell$ the number of matrices and $a$ the binding count from her Lemma 3 minimisation
(the adjacent tie $A(a-1) = A(a)$ makes two envelope branches bind; the order counts the
binding branches). In Lean: the bare definition `aoyagiTheta` (Foundations/Lambda.lean); the
combinatorial count theorem is a live build item (aoyagi-engine build-list #2). The analytic
binding (this count = the actual pole multiplicity) needs meromorphic continuation, which
Mathlib lacks; it is a deferred seam, **and it binds to $a(\ell-a)+1$, never to
$\theta_{\mathrm{geo}}$**.

## The counterexample (machine-verified 2026-07-19)

At $d = (2,2,2,2,2)$ — five vertices, $\ell = 4$ maps, all widths $2$, $r = 0$:

- the QIP data evaluates to $m = 4$, $S = 10$, hence $a = 3$, $\delta = -2$, so
  $\theta_{\mathrm{geo}} = \binom{4}{2} = \mathbf{6}$
  (verified by `#eval` on the computable clones of `qipM`/`qipS`);
- Aoyagi's data is $\ell = 4$, $a = 2$, so
  $r_{\mathrm{order}} = 2\cdot(4-2)+1 = \mathbf{5}$.

$6 \neq 5$. The two invariants coincide at small cases (e.g. $(2,2,2)$, where both are $1$)
**by accident**; neither determines the other in general — in particular the pole order is
not recoverable from the built `cTheta` machinery, which is why the combinatorial
$r_{\mathrm{order}}$ count is its own build item.

## The mint guard

The learning-coefficient headline (`aoyagi_learning_coefficient`) delivers the **value**
$\lambda$ only. No theorem name, docstring, or PR framing may state or imply that
$\theta_{\mathrm{geo}}$ (`numTop`/`cTheta`) is the RLCT multiplicity. Any future work on the
θ analytic-multiplicity seam must target $a(\ell-a)+1$.

*Provenance: scout-lr1's decorrelated gap sweep (threads/20-gap-sweep/) + Codex convergence;
controller `#eval` verification (journal tick 321); elder charge-8 ruling (journal tick 323).*
