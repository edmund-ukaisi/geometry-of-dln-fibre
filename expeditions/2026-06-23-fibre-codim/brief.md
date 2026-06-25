# Expedition brief — the fibre-codimension bundle-shift (LR Lemma 4.6)

**Branch:** `expedition/fibre-codimension` (off `dev` @ `8cba3dd`, worktree `fibre-codim`).
**Opened:** 2026-06-23, after the `explicit-ctheta` close (PR #7).

## Central question

Prove **Lehalleur–Rimányi Lemma 4.6** (the fibre-codimension bundle-shift), discharging the currently
**ASSUMED** interface `BundleShiftInterface.cited_bundle_shift` (`DLN.RlctPayoffGeneral`): for a genuine
deep network (`0 < N`) and `B` of *exact* rank `r ≤ min d`,

$$
\operatorname{codim} \operatorname{mult}^{-1}(B)
  = \operatorname{codim} \overline{\Sigma}{}^r \;+\; r\,(d_0 + d_N - r),
$$

i.e. $\operatorname{mult}^{-1}(B)$ is a locally-trivial bundle over the rank-$r$ matrix variety
$\mathrm{Mat}^{\mathrm{rk}=r}$ (of dimension $r(d_0+d_N-r)$), so its codimension is that of the closed
rank-$\le r$ locus plus the base dimension. (The $\overline{\Sigma}{}^r$ form folds in
$\operatorname{codim}\overline{\Sigma}{}^r = \operatorname{codim}\Sigma^r$, Cor 4.4 + Lemma 4.5 —
already `Core` geometry.)

**Why this is the chunk.** It is the genuine remaining *geometric* content of the LR paper — the
general fibres $\operatorname{mult}^{-1}(B)$, the title object — and the **last assumed step** under the
`rlct = C/2` payoff (`RlctPayoffGeneral.rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`). Discharging
it leaves that payoff standing on **only** the genuinely-Cited Aoyagi/Watanabe analytic bound
($\operatorname{rlct}\le\tfrac12\operatorname{codim}$).

## Known difficulty (de-risk first)

The interface docstring records that a prior thread (thread 11) **hit the "fibre-dimension wall of
Mathlib v4.29"** — the locally-trivial-bundle / fibre-dimension count is absent from Mathlib. So this
is **hard**: it likely needs a from-scratch dimension-theory build (in the spirit of the q-series
sub-library and the `voigt-discharge` AG dimension library). **This expedition opens with a RECON**
(thread 01) to scope reachability before any formalisation grinding — *whole-in-reach?*

## Route (LR's proof, to be verified by recon)

1. $\operatorname{mult}^{-1}(B)$ for $B$ of rank $r$ fibres over the orbit of $B$ (the rank-$r$ matrices
   $\mathrm{Mat}^{\mathrm{rk}=r}$, dimension $r(d_0+d_N-r)$), locally trivially, with fibre $\cong$ a
   zero-product-type locus.
2. Dimension additivity (total = base + fibre) → the codim shift.
3. $\operatorname{codim}\overline{\Sigma}{}^r = C$ is **landed** (`Core.SigmaCodim`); the $r=0$ fibre
   case ($\operatorname{codim}\operatorname{mult}^{-1}(0) = C$) is **landed** (`DLN.RlctPayoff`).

## Closing criterion

Either: **Lemma 4.6 PROVED** — `cited_bundle_shift` discharged, so the general-$B$ fibre codim (and
hence the `rlct = C/2 + shift` payoff) is unconditional but for the cited analytic bound; green,
sorry-free, axiom-clean; witness `(2,2,2)`, `r=1` (predicted fibre codim 4) re-derived. **Or:** a
sharp **obstruction + roadmap** naming the precise missing theory (if the fibre-dimension machinery is
out of reach), so the assumption is at least pinned with a concrete build target. Exposition + PR.

## Scope guards

- This is the **LR route** (`DLNFibre.Core` geometry + `DLNFibre.DLN.RlctPayoff*`). **Non-colliding
  with the live aoyagi-full expedition** (Aoyagi's independent λ-via-resolution route, `DLN.RLCT.*`).
- The analytic $\operatorname{rlct}\le\tfrac12\operatorname{codim}$ direction stays **Cited**
  (Aoyagi/Watanabe); nothing here is named `rlct_…` as if it proved that bound.
- Controller is in a worktree ⟹ teammate isolation collapses to this shared worktree (serial).
