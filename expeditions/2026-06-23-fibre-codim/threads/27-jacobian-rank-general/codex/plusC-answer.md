**1. (★C) Via Smooth-Pt-Of-Σ̄^r**

Bluntly: **not quite closed as stated**.

The clean independent part is existence of a **reduced-smooth point of a top component** of `Σ̄^r` whose product has rank exactly `r`, assuming you have the standard dominance/non-containment fact: some top component is not contained in `Σ̄^{r-1}`. That follows cleanly if you have, or can land, `codim Σ̄^{r-1} > codim Σ̄^r = C`. Then smooth locus is dense, rank-exactly-`r` is open, and `GL_{d_N} × GL_{d_0}` moves the resulting target to `E`.

But the step

`A smooth on reduced Σ̄^r  =>  rank(dg_A) = C`

is **not automatic**. It is true only if the local `g`-zero scheme is generically reduced / has the correct conormal space along that top component. Otherwise one can have the `x ↦ x^2` pathology: reduced zero locus smooth of codim `1`, but differential rank `0`.

So choosing `A` on the smooth locus of the **reduced** `Σ̄^r` does **not by itself** break circularity. It breaks circularity only after adding an independent lemma:

> At the chosen top component over rank `r`, the BR equations `g` cut `Σ̄^r` generically reduced/lci, equivalently `rank(dg_A)=C` at a general point.

That lemma is very close to the desired `+C` statement, so it should be treated as the actual remaining wall unless proved by another engine fact.

**2. Fibre-Smoothness Closing Step**

Conditional on `rank(dg_A)=C`, the Q3 logic is good.

At rank-exactly-`r`, the target rank stratum `Mat^{=r}` is smooth of dimension `δ`. The endpoint `GL × GL` orbit-tangent identity gives tangent directions inside `Σ̄^r` whose `dmult` images span `T_E Mat^{=r}`. Thus

`mult|_{Σ̄^r} : Σ̄^r -> Mat^{=r}`

is a submersion at a smooth point of the relevant component.

Then the fibre inside `Σ̄^r` is smooth of codim `δ`, so its local dimension is

`card - C - δ`.

Together with the decomposition theorem,

`rank(dmult_A) = δ + rank(dg_A) = δ + C`.

So: **Q3 is valid once Q2’s conormal/Jacobian-rank issue is genuinely settled.** Without that, it proves reduced fibre smoothness inside reduced `Σ̄^r`, but not the full Jacobian rank statement.

**3. Route Ranking**

For the formaliser, I would rank:

1. **Homogeneous sweep route**  
   Smaller surface. It uses landed `GL` baseChange, equivariance, orbit dimension, and the sweep identity  
   `dim Σ^r = δ + dim F`.  
   This avoids generic smoothness, scheme-reducedness of `g`, and Jacobian criterion subtleties.

2. **Jacobian via smooth point of `Σ̄^r`**  
   Mathematically elegant, but formally heavier. It needs: codim `Σ̄^r = C`, existence of a rank-`r` smooth top point, endpoint submersion to `Mat^{=r}`, decomposition `(b)`, and crucially a **generic reduced/lci/conormal lemma** for the BR equations.

So for codimension of `F`, use homogeneous sweep. Use the Jacobian route only if you specifically need the rank statement.

**4. Likely Error + Cheapest Test**

Most likely error: **conflating smoothness of the reduced top component with maximal rank of the chosen defining equations `g`**.

Cheapest exact test: localize at a candidate top component `P` meeting rank `r`, then compute the rank of the BR Jacobian modulo `P` over the component’s function field. Equivalently, at an exact rational smooth witness on that component, check

`dim ker(dg_A) = card - C`

or

`rank(dg_A) = C`.

If this fails, the smooth-point argument is circular/false. If it succeeds generically on one rank-`r` top component, then the Jacobian route closes cleanly via your decomposition theorem.