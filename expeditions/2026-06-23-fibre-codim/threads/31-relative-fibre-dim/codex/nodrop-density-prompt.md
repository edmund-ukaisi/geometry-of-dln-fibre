<task>
Setting (exact algebra, affine varieties over an algebraically closed field k):

Fix a dimension vector d = (d_0, d_1, ..., d_N), N >= 1. A "tuple" A = (A_1,...,A_N) is a list of
composable matrices A_i of size d_i x d_{i-1}. The "product map" is mult(A) = A_N A_{N-1} ... A_1,
a single d_N x d_0 matrix. The representation space is the affine space Rep_d of all such tuples
(coordinates = all matrix entries of all A_i).

Fix r with r <= d_0 and r <= d_N. Define:
  Sigma^r        = { A in Rep_d : rank(mult(A)) = r }   (EXACT-rank product locus)
  Sigma^{<=r}    = { A in Rep_d : rank(mult(A)) <= r }  (its Zariski closure; rank <= r is closed)

Sigma^{<=r} is REDUCIBLE in general. Its irreducible components are the maximal orbit closures
Ō_M under the group H' = GL_{d_N} x GL_{d_{N-1}} x ... x GL_{d_0} acting by simultaneous base
change A_i -> g_i A_i g_{i-1}^{-1}. (For the product, only the endpoint factors GL_{d_N} x GL_{d_0}
matter: mult(g.A) = g_N mult(A) g_0^{-1}.) Each component is parametrized by a "rank pattern" /
Kostant partition; the "top-dimensional" components are the maximal-dimension ones. There can be
SEVERAL top-dimensional components (the count is called theta; e.g. for d=(3,3,3), r=2, theta=3).

Define the chart-defining function:
  detDelta(A) = the determinant of the TOP-LEFT r x r submatrix of mult(A)
             = det( (mult(A))[1..r, 1..r] ).
This is a polynomial in the entries of A. The "pivot chart" is U = { A : detDelta(A) != 0 }.

<output_contract>
Answer these, with exact-algebra justification (give explicit matrices / orbit representatives
where relevant). Distinguish FACT (you can prove it) from INFERENCE/HEURISTIC.

Q1. Is the chart U = {detDelta != 0} DENSE in EVERY top-dimensional irreducible component of
    Sigma^{<=r} (equivalently: does U meet every top component, given each component is
    irreducible)? Either:
    (a) give a clean argument that U meets every top component, OR
    (b) exhibit a top-dimensional component on which detDelta vanishes IDENTICALLY (i.e. the
        top-left r x r minor of the product is identically 0 on that whole component), proving
        ONE chart does NOT suffice.

Q2. There is a proposed argument via the H'-orbit structure: Sigma^r is a single H'-sweep of one
    fixed rank-r fibre (Sigma^r = union over g in H' of g . (mult^{-1}(E)) for a fixed rank-r
    target E). Does the H'-action (which row/column-combines mult(A) at the two ends:
    mult(g.A) = g_N mult(A) g_0^{-1}) let one always move a generic point of any top component
    onto U? I.e.: if A has rank(mult(A)) = r, can one always choose endpoint g_N, g_0 so that the
    top-left r x r minor of g_N mult(A) g_0^{-1} is nonzero? Is this enough to conclude U meets
    every top component? State precisely what "rank exactly r" buys here.

Q3. If ONE chart {detDelta != 0} does NOT meet every top component (case Q1b), is the finite cover
    by ALL r x r pivot positions { det(mult(A)[rows R, cols C]) != 0 : |R|=|C|=r } the fix?
    Concretely: is the union of these pivot charts EQUAL to Sigma^r (the exact-rank locus)? Does a
    max-over-charts bookkeeping (dim Sigma^r = max over charts of dim(chart)) then recover the
    no-drop? Roughly how many charts (as a function of d_0, d_N, r)?

Q4. Sanity-check two concrete cases, EXACTLY:
    (i) d = (2,2,2), r = 1: top-left 1x1 minor = the (1,1) entry of mult(A) = (A_2 A_1). Does this
        entry vanish identically on any top-dimensional component of Sigma^{<=1}?
    (ii) d = (3,3,3), r = 2: top-left 2x2 minor of mult(A) = A_2 A_1 (3x3 product). theta = 3 here.
        Does this 2x2 minor vanish identically on any of the 3 top-dimensional components?
    For each, identify the top components by rank pattern and check the minor on a generic point of
    each.
</output_contract>

<grounding_rules>
- Exact algebra only for load-bearing claims. Monte-Carlo / numerics may guide but never certify a
  "vanishes identically" or "is generically nonzero" claim.
- A "vanishes identically on a component" claim must be checked against the GENERIC point of that
  component (or equivalently the orbit representative + the whole H'-orbit), not one special point.
- A "U meets every top component" claim: since each component is irreducible, U (a principal open)
  meets it iff detDelta does NOT vanish identically on it. So the two are equivalent — be explicit.
- Do not assume the top-left minor is special; the key tension is that a rank-r matrix has SOME
  nonzero r x r minor but not necessarily the TOP-LEFT one.
- Note: rank of a PRODUCT A_N...A_1 being exactly r is a constraint on the product, the components
  differ in HOW the rank drops along the chain (the intermediate ranks), but the product itself is
  just a single d_N x d_0 matrix of rank r living in the image.
</grounding_rules>
