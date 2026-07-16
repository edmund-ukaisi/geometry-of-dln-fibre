Let
\[
d:=ab,\qquad k:=\mathrm{minAdm}',\qquad R:=M_1=u+b,\qquad N:=(u+a)R.
\]

The cleanest route is the ratio trick, but not with \(\kappa\) dropped. Use a joint full-block finiteness estimate on the pivot shell.

## Q1 — ratio architecture

**FACT.** The following generic ENNReal lemma is sound:

```lean
theorem exists_finite_mul_of_finite_imp
    {L R : ℝ≥0∞}
    (hR0 : R ≠ 0)
    (hfin : R < ⊤ → L < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ L ≤ C * R
```

Proof:

- If `R = ⊤`, take `C := 1`.
- If `R < ⊤`, then `L < ⊤` by `hfin`; take `C := L / R`.
- Since `R ≠ 0, ⊤`, ENNReal division gives `(L / R) * R = L` and `L / R < ⊤`.

**INFERENCE.** For the stated consumer, this is complete. The real theorem to prove is exactly

```lean
pivotDomRHS ... c' < ⊤ → pivotDomLHS ... c' < ⊤
```

No all-\(c'\) pointwise domination is needed.

## Q2 — extracting the exponent threshold

**FACT.** Finite RHS forces
\[
c'<\frac{k+d}{2},
\qquad\text{equivalently}\qquad
c'-\frac d2<\frac k2.
\]

More primitively, since `J = k - 1` is natural subtraction, the divergence threshold is
\[
c'\ge \frac{J+d+1}{2}.
\]
To rewrite this as \((k+d)/2\), Lean needs `1 ≤ k`.

**FACT.** This requires a divergence lower bound on RHS. The banked upper bound
\[
RHS\le C\cdot\mathrm{comparator}
\]
cannot imply anything from `RHS < ⊤`.

The required divergence proof is comparatively cheap. Restrict to

\[
0<v_0<1,\qquad |\Gamma_{ij}|\le v_0.
\]

Uniformly for \(A_{\rm cor}\) in its box, for fixed \(z\),
\[
\operatorname{decLoss}(z,v)+\|\Gamma A_{\rm cor}Z\|^2
 \le K(z)v_0^2.
\]
On the a.e. set where `decLoss > 0`, the base is positive, so
\[
(\cdots)^{-c'}\ge K(z)^{-c'}v_0^{-2c'}.
\]
The \(\Gamma\)-cube has volume proportional to \(v_0^d\), and the monomial contributes \(v_0^J\). Thus RHS dominates
\[
\int_0^1 v_0^{J+d-2c'}\,dv_0,
\]
which is infinite precisely when \(J+d-2c'\le-1\), including equality.

A suitable lemma is:

```lean
theorem pivotDomRHS_eq_top_of_critical
    (hmin : 1 ≤ minAdm')
    (hc :
      (((minAdm' + a * b : ℕ) : ℝ) / 2) ≤ c') :
    pivotDomRHS ... c' = ⊤
```

with the useful contrapositive:

```lean
theorem exponent_lt_critical_of_pivotDomRHS_lt_top
    (hR : pivotDomRHS ... c' < ⊤) :
    c' - (((a * b : ℕ) : ℝ) / 2)
      < ((minAdm' : ℝ) / 2)
```

## Preferred finiteness proof: keep the entire block

For \(c'>0\), combine all block variables:
\[
T=\begin{pmatrix}P&B_{12}\\ C&D\end{pmatrix}
   \in\mathbb R^{(u+a)\times M_1}.
\]
After enlarging away `IsUnit P`, the loss is exactly
\[
\|TQ_{\rm stack}\|_F^2.
\]

On `pivotShell`,
\[
Q_{\rm stack}Q_{\rm stack}^{\mathsf T}\succeq\varepsilon^2I,
\]
hence
\[
\|TQ_{\rm stack}\|_F^2\ge\varepsilon^2\|T\|_F^2.
\]
Consequently, uniformly in \(z,A_{\rm cor}\),
\[
\int_{T\in[-1,1]^N}\|TQ_{\rm stack}\|^{-2c'}\,dT<\infty
\quad\text{when}\quad c'<N/2.
\]

Finite RHS gives
\[
2c'<k+d
 \le u\rho+ab
 \le uM_1+ab
 \le (u+a)M_1=N.
\]
The final inequality is \(ab\le aM_1\), since \(b\le M_1\).

**INFERENCE.** Thus all \(c'>0\) are handled by one joint full-block D-B estimate. S3 is unnecessary on the pivot shell.

For \(c'\le0\), the exponent \(-c'\) is nonnegative, so the integrand is bounded provided the DLN polynomial maps \(Q_p(z),Z(z)\) are bounded on the parameter box. Bounded domains alone would not imply this for an arbitrary measurable `Zf`; the actual polynomial boundedness must be recorded.

## Q3 — dropping \(\kappa\)

**FACT.** For \(c'>0\),
\[
(w+\kappa)^{-c'}\le w^{-c'}
\]
is valid when \(w>0\), hence a.e. on the shell because `w = 0` means the top coefficient block is zero.

It is not literally pointwise valid under Mathlib’s `Real.rpow` convention: for negative exponent, `0 ^ (-c') = 0`. Thus when \(w=0<\kappa\), the proposed inequality reads a positive number \(\le0\). One must explicitly discard the null set `w = 0`.

**FACT.** Even as an a.e. estimate, dropping \(\kappa\) is not sufficient. It demands
\[
c'<\frac{uM_1}{2}.
\]
Finite RHS supplies only
\[
c'<\frac{k+ab}{2},
\]
and `hpiv` gives \(k\le u\rho\le uM_1\), not
\[
k+ab\le uM_1.
\]

For example, \(u=1,b=1,M_1=2,a=4,k=2,\rho=2\) permits
\[
c'<3,
\]
whereas the dropped-\(\kappa\) pivot integral already diverges for \(c'\ge1\).

So:

- Dropping \(\kappa\) is an a.e. valid upper bound.
- It can overestimate LHS to \(\top\).
- The corank/bottom-block charge is genuinely needed if one insists on a top-block-only proof.
- It is captured more cleanly by the joint full-block D-B estimate than by S3.

If using the sequential S3 architecture, the correct split is:

1. \(c'\le0\): boundedness.
2. \(0<c'\le ab/2\): joint full-block D-B; S3 is unavailable.
3. \(c'>ab/2\): peel \(D\), obtaining \(c''=c'-ab/2\), then use
   \[
   c''<k/2\le u\rho/2\le uM_1/2.
   \]

The stated S3 lemmas integrate \(A_{\rm cor}\) over the full box. Enlarging away `pivotShell` can destroy the rank needed for the later pivot estimate, so this sequential route would need a pointwise-in-\(A_{\rm cor}\), shell-preserving peel.

## Q4 — minimal new lemmas

The preferred analytic lemma is a uniform shell estimate:

```lean
theorem shell_fullBlock_cube_lintegral_le
    {r q n : ℕ} {ε c : ℝ}
    (hε : 0 < ε)
    (hc0 : 0 < c)
    (hc : c < (((r * q : ℕ) : ℝ) / 2)) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ Q : Matrix (Fin q) (Fin n) ℝ,
        Q * Q.transpose ⪰ ε^2 • 1 →
        (∫⁻ T in matBox r q 1,
          ENNReal.ofReal
            ((frobSq (T * Q)) ^ (-c))) ≤ K
```

Instantiate with `r := u + a`, `q := M₁`.

**FACT.** Pointwise finiteness is a D-B instantiation: the map \(T\mapsto TQ\) has range rank \(rM_1\). But the existing D-B signature only gives `< ⊤` for each fixed \(Q\); that alone does not justify integration over \(z,A_{\rm cor}\). The new lemma should package the uniform bound supplied by the Loewner floor.

Therefore the minimal architecture is:

1. RHS critical-exponent divergence lemma.
2. Uniform joint full-block shell integral lemma.
3. Elementary nonpositive-exponent boundedness.
4. Generic ENNReal ratio lemma.

No coupled-residual lemma and no S3 are needed for the preferred proof.