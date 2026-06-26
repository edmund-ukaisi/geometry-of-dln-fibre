**Verdict: ELEMENTARY route exists.**

**FACT.** The general constant-rank theorem is not logically essential once the DLN-specific normal form you describe is available uniformly at an arbitrary fibre point `v`: gauge to a rank-`r` identity corner, choose `q` regular generators with unit pivots, and solve them triangularly.

**Reason.** Constant-rank is needed when the only information is “the Jacobian has locally constant rank `q`” and one must manufacture coordinates abstractly. Here the coordinates are not abstract: the chain-product structure supplies explicit pivot variables and explicit equations of the form, after ordering,

```text
g_i = u_i · z_i + h_i
```

where `u_i(0) = 1`, so `u_i` is a local analytic unit, and `h_i` involves only already-controlled/free variables according to the triangular order. Thus `z_i = -h_i/u_i` is obtained by division by a unit. Iterating gives the local coordinate elimination directly.

**Lean Ingredient**

**FACT.** The route needs only local unit-division for analytic/smooth functions plus finite triangular iteration:

```text
polynomial/analytic functions
+ f(0) ≠ 0 ⇒ 1/f is analytic/smooth locally
+ closure under composition, product, quotient by units
+ finite induction over the triangular solve order
```

A one-variable implicit/inverse-function theorem with nonzero derivative is sufficient, but even that is somewhat more than necessary if the equations are explicitly affine in the pivot variable with unit coefficient.

**INFERENCE.** Mathlib v4.29 plausibly has enough for the smooth version through its `HasFDerivAt` / inverse-function-theorem / `ContDiff` infrastructure. I would be less confident that a fully packaged real-analytic implicit theorem is present, but the explicit rational/unit-denominator construction avoids needing such a theorem. Proving “unit denominator gives analytic local function” is much lighter than proving general constant-rank.

**Triangularity Catch**

**FACT.** Your stated computation gives the crucial missing datum: after the explicit gauge, the regular block has identity/unit-diagonal linear part, and the residual block has no linear part.

**INFERENCE.** For the DLN chain family, this is not the non-triangular constant-rank situation. The chain product is multilinear, so each chosen pivot variable occurs linearly; the gauge/block form supplies identity paths; and the regular generators can be ordered so each pivot has a unit coefficient. Thus the hard constant-rank case, where rank is locally constant but no separable triangular pivot system is available, does not arise.

The only hypothesis that must be proved uniformly in Lean is the DLN-specific combinatorial/gauge lemma:

```text
for every fibre point v, there exists an explicit gauge and pivot order
such that the q regular generators form a triangular unit-pivot system.
```

Once that lemma is in place, no fibre point should force the general constant-rank theorem.

**Final Adjudication**

`D1>=` is cheaply revivable by the elementary triangular route, not genuinely gated on a Mathlib-scale constant-rank contribution.

The precise reason is that the DLN family supplies explicit local coordinates and unit pivots. Constant-rank’s extra content is abstract coordinate production for arbitrary non-triangular maps; the DLN chain-product structure avoids that case.