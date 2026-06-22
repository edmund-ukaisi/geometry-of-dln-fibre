# Expedition brief — `perm-invariance`

## Central question

Formalise the paper's **surprising headline** (Lehalleur–Rimányi Cor 5.10): the codimension/component
invariants `(C, θ)` of the rank-`r` product locus depend **only on the multiset** of the dimension
vector `d` — i.e. `(C, θ)` is invariant under permuting `d`, even though the underlying type-A quiver
is *ordered*:

> `cCodim (d ∘ σ) r = cCodim d r` and `numTop (d ∘ σ) r = numTop d r` for every permutation `σ` of the
> vertices `Fin (N+1)` (equivalently: `(C, θ)(d) = (C, θ)(sort d)` — the value depends only on the
> sorted multiset).

This is the last major un-formalized result of the paper. The combinatorial `(C,θ)` forms are LANDED
(QIP Thm 6.1 `cCodim_eq_qipMin`; the explicit closed form Thm 7.10, both for *weakly-increasing* `d`);
permutation invariance EXTENDS them to all `d` and is the conceptual surprise.

## Closing criterion

`cCodim`/`numTop` permutation-invariance (Cor 5.10) formalised, green / 0-sorry / axiom-clean, via the
**FULL ZERO-CITED q-series route** (operator decision, 2026-06-22): build a `Core.QSeries` sub-library
and reprove the Poincaré-series identities — including RWY 2018's Thm 5.6 via the elementary PEEL
induction — from `Finset`/`PowerSeries` primitives, with no external citation. Delivers, as bedrock:
Cor 5.10 + the Poincaré series (Thm 5.5) + the explicit `(C,θ)` for **all** `d` (extending the
LANDED monotone-only forms) + a reusable q-Pochhammer / q-binomial / q-Vandermonde / Durfee library
(absent from Mathlib v4.29, upstreamable).

## The route — sized & certified (threads 01–03)

RECORD CORRECTION: the sizing pass's "open problem" was wrong. The one hard link (Thm 5.6 / the "5gon")
**is** Rimányi–Weigandt–Yong 2018 (arXiv:1608.02030), the paper's own cited `[RWY]`. A direct
Kostant-bijection proof of perm-invariance IS open (`|M⁺_d|≠|M⁺_{σd}|` blocks it; the direct route
collapses to a `≥2500 LoC` global swap map — thread 02 OBSTRUCTED-as-shorter), but the q-series route
sidesteps it by proving the generating-function identity and reading off `(C,θ)`. The chain (thread 03,
all links exact-verified):

```
(perm-inv Cor 5.10) ⟸ L0 cCodim d 0=cCodim(sort d)0 ∧ numTop d 0=numTop(sort d)0
 ⟸ L1 (C,θ)-extraction: lowestTerm(Qseries d r)=numTop·q^{cCodim}  [CLEAN: Pm coeffs ≥0 ⟹ no cancellation]
 ⟸ L2/Thm5.5  Qseries d r = P r·∑_s (−1)^s q^{C(s,2)} P s·Pmult(d−r−s)   [Pmult MANIFESTLY multiset-symmetric]
 ⟸ S1–S4 chain  (S1 shift REUSES the LANDED codimForm_update_corner; S3 = q-binomial inversion)
 ⟸ S0=Thm5.6(5gon)  Pmult d = ∑_{m⊢d} q^{codimForm} Pm m   [= RWY 2018, reproved zero-cited]
 ⟸ PEEL  induction on N: peeling bijection + codim split c(m)=c(m')+Δ_b(x) + local transfer identity
```

Build ladder (~6–8 substantive files, ~2–3 wk — sequence bottom-up, serial Lean-writers):
- **M1 `Core.QSeries` primitives** — `P`/`Pm`/`Pmult`/`Qseries`; `Pm` coeffs ≥0 + constant-term 1.
- **M2 classical q-facts** — q-binomial theorem/inverse (S3), q-Vandermonde, `N=1` Durfee (some avoidable).
- **M3 PEEL / Thm 5.6** (the bulk) — the load-bearing **local transfer identity** (PIN symbolically first).
- **M4 the S1–S4 chain → Thm 5.5** (L2).
- **M5 L1 extraction** (clean).
- **M6 `cCodim`/`numTop` symmetry → Cor 5.10** (all `r` via the LANDED `cCodim_rankShift`) + the geometric
  transfer through `Core.SigmaComponents`/`CThetaGeometric`.
- **(independent) order-reversal fragment** — `(C,θ)(d)=(C,θ)(reverse d)` via the codimForm-preserving
  bijection `[a,b]↦[N−b,N−a]` (441/441 verified); ~1 file zero-cited bedrock, landable any time.

## LANDED bricks (consumable, on `dev`)

`Core.CTheta` (`cCodim`, `numTop`, `codimForm`, `kostantPartitions`, `multiplicityArray`, the rank-shift
`cCodim_rankShift`); `Core.CThetaQIP`/`CThetaQIPConverse` (Thm 6.1, monotone `d`); `Core.CThetaValue`/
`CThetaExplicit` (Thm 7.10 closed forms); `Core.CCodimZeroMono`/`CCodimZeroStrict` (dimension-monotonicity
of `cCodim·0`); `Core.SigmaComponents`/`ThetaComponentCount`/`CThetaGeometric` (the geometric `(C,θ)`).

## Scope / boundary

- **Zero-cited, including the Poincaré series.** Thm 5.5 / Thm 5.6 are now IN scope — reproved from
  `Finset`/`PowerSeries` primitives in `Core.QSeries`, NOT cited. (The equivariant-cohomology *derivation*
  is bypassed; the combinatorial PEEL proof replaces it.) `#print axioms` stays `[propext, Classical.choice,
  Quot.sound]`.
- The new q-series sub-library is network-free engine content → lives in `DLNFibre.Core` (never imports DLN).
- Geometric corollary inherits the existing `[IsAlgClosed k][CharZero k]` scope.
- Pre-formalisation step (thread 03's flag): PIN the PEEL local transfer identity symbolically
  (q-Vandermonde × `N=1` Durfee) before the M3 tide — Codex's decomposition is inference, not yet proved
  from primitives.

## Operating mode

Controller drives autonomously (operator: "set this up as a largish expedition — you can do it well").
Surface only at completion or a genuine blocker/scope-surprise. Controller runs from a worktree ⟹ serial
Lean-writers; parallel doc/recon seats. **SIZING-PASS FIRST** (the discipline that has repeatedly avoided
wasted sub-libraries — and the roadmap's "genuine lift, NOT free" warning is explicit here).
