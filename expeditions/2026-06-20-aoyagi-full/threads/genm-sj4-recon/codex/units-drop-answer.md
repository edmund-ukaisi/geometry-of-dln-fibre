## (a) Units-drop soundness

**Verdict: DROP** the raw units bound from the carried invariant. This is a design inference forced by Facts 1 and 4.

- **Derived:** A fixed \(c>0\) valid for every \(r\) is impossible: at \(r=0\),
  \[
  Z_{\rm tail}(0)Z_{\rm tail}(0)^T-cI=-cI
  \]
  is not positive semidefinite.
- **Derived:** Even \(\forall r\,\exists c_r>0\) fails at \(r=0\). Quantifying only over one selected \(r\) would not support provenance over the whole domain.
- **Derived:** At width \(2\), \(Z_{\rm tail}=I\), so step #4 may derive the bound with \(c=1\).
- **Derived:** On a units sector with \(\sigma_{\min}(Z_{\rm tail})\ge\varepsilon>0\), step #5 may re-supply a uniform local bound, for example \(c=\varepsilon^2\). The complementary sector recurses without this bound.

**Subtlety:** the units argument must be invoked only after restricting to the units sector. Any theorem that still extracts the bound directly from global `adm` would become unsound. One could carry the conditional structural statement “full row rank implies existence of such \(c\),” but not the unconditional bound itself.

## (b) Width-3 witness

All arithmetic conclusions below are checkable from the supplied data.

| Clause | Result | Exact reason |
|---|---:|---|
| Split isomorphism/domain | PASS | \(e_\Gamma(A_1,A_2)=(A_1,A_2)\) is coordinate reassociation; it preserves the standard product measure and product box. |
| Provenance | PASS | \((\Gamma Z_{\rm tail})_{ij}=\sum_k(A_1)_{ik}(A_2)_{kj}=(A_1A_2)_{ij}=\operatorname{res}_{(i,j)}\). |
| Dimension bound | PASS | \(\minAdm(M)=3\le a n=2\cdot2=4\). |
| Alpha | PASS | Every support exponent is \(1\); hence any \(i_0\) satisfies \(1\le1\) for every \(j\). Nonvacuous: \(\iota\) has four elements. |
| Delta-0 | PASS | For the sole divisor, every generator has exponent \(1\), so the shared exponent is \(k(0)=1\). |
| Beta | PASS | \(\minAdm/2=3/2\), while \(\operatorname{axisRatio}(3,1)=(3+1)/(2\cdot1)=2\); thus \(3/2\le2\). |
| Units bound for all \(r\) | FAIL | The box contains \(r=0\); then the matrix is \(-cI\), not PSD for any \(c>0\). |

**Verdict: INHABITED** for the units-dropped \(\gamma'\), assuming the ambient measures are the stated standard coordinate/product measures. It is neither vacuous nor ill-formed from the supplied data.