## Q1

**ARGUED — `{OPT-STANDALONE}` for both wings, with a corrected sector atlas.**

- **Wide \(M_0\le M_1\), \(t=M_0\):** \(A_1\mapsto XA_1\) is surjective for fixed full-row-rank \(X\). A joint source-incidence sector CoV can retain the exceptional variables; its Jacobian is a pure monomial. No Gram of \(WZ_{\rm deep}\) remains. Do not first push forward to \(\rho(W)\).

- **Tall \(M_1\le M_0\), \(t=M_1\):** the claimed reduction to a free \((M_0,M_2,\ldots)\) chain is false. \(W=FA_1\) lies in \(\{\operatorname{rank}W\le M_1\}\). Write sectorwise \(W=U_sV_s\), with \(V_s\in\mathbb R^{s\times M_2}\); the plain target is
  \[
  \operatorname{redChain}_sM=(s,M_2,\ldots),
  \]
  top sector \(s=M_1\), not \((M_0,M_2,\ldots)\).

An ordinary blow-up indexed only by \(\operatorname{rank}W=r\) is insufficient. The atlas needs incidence sectors \((r,s)\), \(r\le s\le\min(M_0,M_1)\), separating the source mechanisms producing the same rank drop. Before exceptional variables are integrated out, the Jacobian is monomial; integrating fibres first produces the unwanted density/Gram factors.

## Q2

**PROVEN — `{OPT-DECORATED}` for the \(d=1,\ a\ge u\) arm.**

After `gammaAtom`, the charge is \(au/2\) and the residual factor is
\[
\det(\widetilde Q\widetilde Q^\top)^{-a/2}.
\]

1. **No front-sector cancellation.** Deep variables can make \(\widetilde Q\) approach a nonzero rank-\((u-1)\) matrix while every front exceptional coordinate is a unit. Hence the Gram divisor and front Jacobian divisor are independent.

2. **Last-layer qbox is only conditional.** If \(\widetilde Q=DA_{\rm last}\), \(D\in\mathbb R^{u\times k}\) is full row rank and \(A_{\rm last}\in\mathbb R^{k\times q}\), then qbox requires
   \[
   u\le q,\qquad a<q-u+1.
   \]
   The CoV also emits
   \[
   \det(DD^\top)^{-q/2},
   \]
   transferring the decoration one layer earlier. Outside the strict qbox range the integral diverges near a nonzero rank-\((u-1)\) matrix; the extra loss remains bounded there and gives no repair.

Thus plain hIH cannot receive the result. The decoration must retain the bounded-\(C\) cutoff, equivalently
\[
\min\!\left\{\operatorname{vol}(C{\rm Box})\,w^{-c'},
\ K\det(\widetilde Q\widetilde Q^\top)^{-a/2}
 w^{-(c'-au/2)}\right\}.
\]
A naked Gram-decorated IH is itself false in the bad qbox dimensions.

## Q3

**ARGUED — minimal standalone wing atom.**

Let \(M:\operatorname{Fin}(L+3)\to\mathbb N\), \(t=\min(M_0,M_1)\), and let `wingFrontBox M` contain
\[
F\in[-1,1]^{M_0\times M_1}
\]
whose leading \(t\times t\) minor is invertible. Assume
```lean
hIH : ∀ M' : Fin (L + 2) → ℕ, RouteMBoxThresholdFinite M'
```
Then the atom should state:
```lean
theorem frontWingRankSector_lintegral_lt_top
    (M : Fin (L + 3) → ℕ)
    (hIH : ∀ M' : Fin (L + 2) → ℕ,
      RouteMBoxThresholdFinite M')
    (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
  (∫⁻ F in wingFrontBox M,
    ∫⁻ A' in paramsBoxM (tailChain M) 1,
      ENNReal.ofReal
        ((frobSq (F * prod (tailChain M) A')) ^ (-(c' : ℝ)))) < ⊤
```

Here
\[
\operatorname{prod}(\operatorname{tailChain}M,A')
   =A_1Z_{\rm deep},
\quad F(A_1Z_{\rm deep})=(FA_1)Z_{\rm deep}.
\]
Sector \(s\le t\) has charge
\[
N_s=(M_0-s)(M_1-s)
\]
and invokes plain hIH on \(\operatorname{redChain}_sM=(s,M_2,\ldots)\) at
\[
c_s=c'-\frac{N_s}{2},
\qquad
c_s<\frac{\minAdm(\operatorname{redChain}_sM)}2.
\]

Consumed banked:

- plain `hIH`;
- `minAdm_le_peelCharge_add_redChain` / the exact min recursion;
- `corner_block`, `scaledRadialEuclid`, and `sumSqND`;
- finite-box and Tonelli plumbing.

New sublemmas:

- finite joint incidence-sector cover indexed by \((r,s)\);
- per-sector measurable CoV;
- Jacobian identity
  \[
  |\det D\Phi|=u(\xi)\prod_j|z_j|^{\nu_j-1},
  \qquad 0<c\le u(\xi)\le C;
  \]
- integral-level sector replacement
  \[
  I_{r,s}(c')\le C_{r,s}\bigl(1+
  I_{\operatorname{redChain}_sM}(c'-N_s/2)\bigr);
  \]
- null-boundary removal and finite sector summation.

Cheapest Q2 computation: use \(M=(4,3,2)\), \(t=u=a=q=2\), \(b=1\), \(c'=5/2\), and
\[
\widetilde Q_\varepsilon=\operatorname{diag}(1,\varepsilon).
\]
Then the front Jacobian is a unit, the residual loss tends a positive constant, while
\[
\det(\widetilde Q_\varepsilon\widetilde Q_\varepsilon^\top)^{-a/2}
=|\varepsilon|^{-2},
\qquad
\int_{-\delta}^{\delta}|\varepsilon|^{-2}\,d\varepsilon=\infty.
\]
This simultaneously rules out cancellation, qbox disposal, and a naked Gram-decorated IH.