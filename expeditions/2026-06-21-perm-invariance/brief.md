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

`cCodim`/`numTop` permutation-invariance formalised, green / 0-sorry / axiom-clean, via a **zero-cited
combinatorial route** (a `codimForm`/Kostant-partition symmetry argument), NOT the paper's
equivariant-cohomology Poincaré-series derivation (Thm 5.5, which needs machinery Mathlib lacks). A
refuted/refined/scope-surprise close (the combinatorial route genuinely needs Thm 5.5 ⟹ a Cited layer)
is also valid — surface with a sized verdict.

## Provisional ladder (RE-SCOPED BY THE SIZING PASS — do not build before it returns)

The roadmap flags Cor 5.10 as "a genuine lift, NOT free," but "possibly reachable by an independent
combinatorial route." The sizing pass settles the route. Candidate shapes:
- **P-cCodim:** `cCodim` is symmetric in `d`. Route candidates: (a) a `codimForm`/Kostant-partition
  bijection under permuting `d` (the form's pairing structure under vertex permutation); (b) via the
  QIP — but `cCodim_eq_qipMin` is *monotone-`d` only*, so reduce a general `d` to `sort d` and show the
  direct `cCodim d` equals `cCodim (sort d)` (the heart of the invariance).
- **P-numTop:** `numTop` is symmetric in `d` (same bijection at the minimiser level).
- **P-geom (corollary):** the geometric `(C,θ)` reading (codim of `Σ̄^r` / #top-dim components) inherits
  the invariance through the LANDED `Core.CThetaGeometric`/`Core.SigmaComponents` bridges.

## LANDED bricks (consumable, on `dev`)

`Core.CTheta` (`cCodim`, `numTop`, `codimForm`, `kostantPartitions`, `multiplicityArray`, the rank-shift
`cCodim_rankShift`); `Core.CThetaQIP`/`CThetaQIPConverse` (Thm 6.1, monotone `d`); `Core.CThetaValue`/
`CThetaExplicit` (Thm 7.10 closed forms); `Core.CCodimZeroMono`/`CCodimZeroStrict` (dimension-monotonicity
of `cCodim·0`); `Core.SigmaComponents`/`ThetaComponentCount`/`CThetaGeometric` (the geometric `(C,θ)`).

## Scope / boundary

- Aim **zero-cited** for the combinatorial invariance (the `(C,θ)` invariants are pure combinatorics of `d`).
- The equivariant-cohomology Poincaré series (Thm 5.5) is OUT of scope (a likely-Cited heavy layer); the
  combinatorial route is the target. If the route forces Thm 5.5, surface (Cited layer or sub-expedition).
- Geometric corollary inherits the existing `[IsAlgClosed k][CharZero k]` scope.

## Operating mode

Controller drives autonomously (operator: "set this up as a largish expedition — you can do it well").
Surface only at completion or a genuine blocker/scope-surprise. Controller runs from a worktree ⟹ serial
Lean-writers; parallel doc/recon seats. **SIZING-PASS FIRST** (the discipline that has repeatedly avoided
wasted sub-libraries — and the roadmap's "genuine lift, NOT free" warning is explicit here).
