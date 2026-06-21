# Thread 09 — L4d affine-domain dimension formula (equidimensionality)

**Seat:** formaliser (tide). **Branch:** `expedition/voigt-discharge`. **Commit:** `74460f0`.

## Target
Lift the L5 polynomial-ring catenary equality to a finite-type domain `A = R ⧸ I` (`R = MvPolynomial
(Fin n) k`, `I` prime): `height p + dim(A/p) = dim A`; plus the maximal-ideal corollary `height m =
dim A` and the local↔global `dim(Localization.AtPrime m) = dim A`. Sized at ~1–2 modules. Delivered
in **one module** (`DLNFibre/Core/AffineDomainDimension.lean`, 213 lines).

## Route taken — Noether normalization + integral height transport (NOT quotient-chain)
Two consults with decorrelated Codex pinned the design. Both natural routes (Q = quotient-chain split
`height_R(P) = height_R(I) + height_A(p)`; N = Noether-normalize `A`, transport height) reduce to **one
new fact**: the integral height transport `height_A(p) = height_B(p.comap g)` for the Noether-
normalization map `g : B = k[y₁..y_s] ↪ A`. Route N chosen — it reuses L5.4 (dimension invariance) and
the L5 polynomial catenary equality as black boxes, no catenary re-induction.

The transport's two inequalities:
- `≤` (going-up): the spectrum `comap` is strictly monotone for an integral extension
  (`strictMono_comap_of_isIntegral`, from L5's `Core.IntegralDimension`); map a chain below `P` to one
  below `p.under`.
- `≥` (going-down): `Ideal.exists_ltSeries_of_hasGoingDown` lifts a chain below `p.under` (realizing
  its height) to one below `P` of the same length.

## The decisive find — Mathlib HAS the going-down theorem
Codex's second consult (`codex/route2-answer.md`) classified L4d as **unbounded** ("needs a going-down
brick Mathlib lacks") — but that verdict rested on an inventory claim I gave it that was **wrong**.
`rg HasGoingDown` over Mathlib surfaced `Mathlib/RingTheory/IntegralClosure/GoingDown.lean`:
`instance [IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] :
Algebra.HasGoingDown R S` (`@[stacks 00H8]`). The base `B = k[y₁..y_s]` is a UFD, hence
`IsIntegrallyClosed` (`UniqueFactorizationMonoid.instIsIntegrallyClosed`, surfaced via
`import Mathlib.RingTheory.Polynomial.RationalRoot`); `A` is a domain. So `Algebra.HasGoingDown B A`
fires by `inferInstance`. L4d **is** bounded — kill-condition did NOT fire. Mirror of the L5 sizing
("recon 01 misread Mathlib").

## Mathlib lemmas used
`Algebra.HasGoingDown` (`@[stacks 00H8]`, integral + integrally-closed base) + `Ideal.exists_ltSeries_
of_hasGoingDown`; `UniqueFactorizationMonoid.instIsIntegrallyClosed` (via `RationalRoot`);
`faithfulSMul_iff_algebraMap_injective`; `Order.length_le_height`, `Order.height_eq_iSup_last_eq`,
`LTSeries.map`/`map_length`/`last_map`; `Ideal.exists_ltSeries_length_eq_height`; `Ideal.quotientMap`
+ `quotientMap_injective` + `isIntegral_quotientMap_iff`; `RingHom.IsIntegral.trans`;
`Ideal.Quotient.maximal_ideal_iff_isField_quotient`; `ringKrullDim_eq_zero_of_isField`;
`IsLocalization.AtPrime.ringKrullDim_eq_height`; `exists_integral_inj_algHom_of_quotient`.

## Own lemmas reused
L5: `ringKrullDim_eq_of_integral_injective`, `ringKrullDim_mvPolynomial_fin_field`,
`strictMono_comap_of_isIntegral` (`Core.IntegralDimension`); `height_add_ringKrullDim_quotient_eq`
(`Core.NoetherMonicPositioning`).

## What fought back
- The `IsIntegrallyClosed (MvPolynomial (Fin s) k)` instance does **not** synthesize without
  `import Mathlib.RingTheory.Polynomial.RationalRoot` (where the UFM → integrally-closed instance
  lives). One probe build to find it.
- `RingHom.IsIntegral.trans` takes the ring homs `f g` **explicitly** (declared in a `variable (f) (g)`
  block), so dot-notation `hint.trans` misparses; spell it `RingHom.IsIntegral.trans g (mk p) hint …`.
- Two `CommRing`-instance diamonds: (a) the headline's `Algebra B A := g.toRingHom.toAlgebra` fought
  `set A`/`set B` aliasing — fixed with `algebraize [g.toRingHom]`; (b) `ringKrullDim_eq_zero_of_field`
  on `A/m` clashed with `Ideal.Quotient.commRing` — fixed by routing through `IsField` +
  `ringKrullDim_eq_zero_of_isField`.

## Status
Whole library green; `scripts/sorries` = 0; `#print axioms` on all four headlines =
`[propext, Classical.choice, Quot.sound]`. Non-vacuity witnesses in-file (transport via identity;
the formula at `(n=1, ⊥, ⊥)` giving `0 + 1 = 1`; the corollaries firing; maximal-ideal class
inhabited via `Ideal.exists_maximal`). Statement card written (`statement-card.md`).

## Next (per synthesis L4★ ladder)
L4d done → **L4a** (cotangent ↔ dimension, smooth ⟹ regular — the genuinely multi-week sub-library,
untouched here; consumes `ringKrullDim_localizationAtPrime_isMaximal_eq` from this module).
**Awaiting:** controller reviewer fidelity AUDIT + hardener bedrock pass.
