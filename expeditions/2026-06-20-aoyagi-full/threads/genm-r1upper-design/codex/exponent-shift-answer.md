**1. Verdict**

**BROKEN as stated.** The shifted-exponent idea is plausible, but the stated mechanism loses essential coupling when it replaces the finite chart integral

```math
\int_0^R (g^2+z^2h^2)^{-c'} z^{a-1}\,dz
```

by the infinite Beta integral and then treats the resulting `h^{-a}` as benign.

That `h^{-a}` factor is not automatically integrable, and its bad locus is not necessarily already paid for by the tail recursion on `g`. So this is not just a missing constant or chart bookkeeping issue.

Completing the route from scratch is therefore **not bounded labour in the present form**. It requires a genuine new joint-integrability lemma for the pair `(g,h)` with the finite-interval cutoff retained. That is essentially the hard part of a recursive resolution proof.

**2. Weakest Point**

The weakest point is the spectator step:

```math
\int_0^\infty (g^2+z^2h^2)^{-c'} z^{a-1}\,dz
\sim h^{-a} g^{-2(c'-a/2)}
```

followed by the claim that `h^{-a}` is benign.

The exact condition that can fail is:

```math
h = \|VQ_{\mathrm{bot}}\| \to 0
```

while `g = \|Q_{\mathrm{top}}\|` does not vanish deeply enough, or does not vanish at all. Then `h^{-a}` may be non-integrable in the bottom-tail variables. The finite `z` integral has a cutoff depending on `Rh/g`; the infinite Beta integral discards that cutoff and can create a false divergence.

The correct finite formula has the form

```math
\int_0^R (g^2+z^2h^2)^{-c'} z^{a-1}\,dz
=
g^{a-2c'} h^{-a}
\Phi(Rh/g),
```

where

```math
\Phi(T)=\int_0^T u^{a-1}(1+u^2)^{-c'}\,du.
```

When `h/g` is small, `\Phi(Rh/g)` cancels the dangerous `h^{-a}`. The proposed proof throws away exactly that cancellation.

**3. Cheapest Discriminating Test**

Use the small case

```math
M=(2,2,1), \quad L=2, \quad t=1.
```

Then `a=(2-1)(2-1)=1`, and

```math
\minAdm(2,2,1)=2,
\qquad
\lambda=1.
```

So the target allows any `c' < 1`; take for example `c'=3/4`.

In the `t=1` chart, write the tail vector as `(u,v)`, so

```math
g=|u|,\qquad h=|v|.
```

The infinite Beta step gives the residual bound

```math
|v|^{-1}|u|^{1-2c'}.
```

For `c'=3/4`, this is

```math
|v|^{-1}|u|^{-1/2},
```

which is non-integrable in `v`.

But the original finite integral

```math
\int_{|z|\le R} (u^2+z^2v^2)^{-3/4}\,dz
```

is integrable over `(u,v)` near `(0,0)`. Thus the proposed Beta-extension/spectator argument fails even before any `L>=3` sharing of deeper factors appears.

**4. Relation To Aoyagi**

This differs from Aoyagi’s recursive blow-up proof in a risk-introducing way. A full resolution keeps track of exceptional variables and rank-drop strata jointly; it does not simply integrate out `z` to infinity and then ignore the induced spectator singularity. If the proposed arity recursion is repaired by retaining the incomplete-Beta cutoff and proving joint resolution of `(g,h)`, it may become a reorganization of Aoyagi’s proof. But in its current form, the simplification introduces a real proof obstruction.