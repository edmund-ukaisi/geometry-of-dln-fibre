# Certificate — coupled diag(b) ideal identity (pen-and-paper, thread 27)

Pen-and-paper `pnp-coupledB` (2026-07-20). All results exact (sympy Gröbner over ℚ; exact-rational
monomial-ideal RLCT LP), decorrelated-confirmed by an independent Codex `xhigh` consult. Batteries:
`theory/aoyagi-2023-reproduction/{_rlct_lp,g-coupled-branch-census,g-coupled-224-heart,g-coupled-334-diagb,
g-coupled-3322-shareddepth,g-lemma1-tractability}.py`; Codex I/O in `./codex/`. **Controller-calibrated**:
ran `g-coupled-334-diagb.py` (EXIT 0) and confirmed the load-bearing checks; see the calibration note below.

## (a) The coupled diag(b) — VERIFIED at the ideal level
**(3,3,4) — the genuine corank-(2,2) frontier (unique coupled-only minimiser t=(1,0); no clean minimiser).**
- **Peel** (Aoyagi Lemma 2 / Thm 3): exact matrix identity `Q₁·C¹·Q₂ = diag(1,Δ)`, `Q₁,Q₂` unipotent
  (det 1), giving `⟨C¹C²⟩ = ⟨T, Δ·S⟩`.
- **(2,2,4) heart** (Gröbner-verified): the radial Δ blow-up pulls `⟨ΔS⟩` back to a literal monomial ideal.
- **Join → single binding divisor of exponent 8:** total Jacobian `E⁷·α³`, `loss = E²·unit` (unit(0)=1),
  `h_E=7`, ratio `(7+1)/2 = 4 = ½·Mval(1,0) = ½·8`. Aoyagi's Case-1(1) exponent-accumulation realised.
- **b = (E, Eαv, Eαvδw), b₁|b₂|b₃** ⟹ `⟨∏C⟩ = ⟨b₁,b₂,b₃⟩ = ⟨E⟩` (principal), `loss = b₁²·unit`, **rlct = 4**.
**(3,3,2,2) — corank-1 (scalar δ) + shared-C³ depth coupling (NOT corank≥2 — honest downgrade from the
brief's pairing).** `b = (vz, vθzη)`, shared C³-radial `z` binds at ratio 2. rlct = 2 = ½·Mval(2,1,0).

**Load-bearing soundness point (independently found + Codex + controller-confirmed).** The ideal identity
`⟨∏C⟩=⟨bᵢ⟩` is LITERAL (`U·∏C·V=diag(b)`, U,V unimodular), **but the loss = `Σbᵢ²·(analytic unit)`, NOT
literally `Σbᵢ²`** — the resolution's unit transforms are non-orthogonal (Frobenius NOT preserved;
`‖C¹C²‖² ≠ ‖T‖²+‖ΔS‖²`, verified). So the RLCT equality REQUIRES Lemma 1 (ideal-invariance) and cannot be
gotten from a change-of-variables/norm identity — this is why Object A is needed and the chart route (F1)
was category-dead. **The single strongest confirmation of the ideal-level frame.**

## (b) Case-2 governing quantity (the flagged fork) — RESOLVED
The **running-min `M(S)=min(M¹..Mˢ)` governs the b-exponents; NO separate "label" exists in the ideal
route.** At (2,2,3,2) the disputed divisor has accumulated exponent 4 (= Mval of admissible (2,2,0)) while
the raw-width label (2,3,0) implies 6 — physical exponent 4 is correct. The Engine's raw-width T-label was
a redundant stored field; the fork DISSOLVES (label not a primitive; FIX-A only makes a carried label
agree). Defect sits on a NON-binding divisor — `minAdm(2,2,3,2)=3` unchanged.

## (c) Lemma-1 ≥-direction — TRACTABLE / detail-at-scale, NOT new math
Divisibility collapses the b-side to a single dominant monomial (`Σbᵢ²=b₁²·unit`); resolved entries are
`b₁·(chart-regular)`, one a unit ⟹ two-sided pointwise bound ⟹ RLCT equality by monotone integration
(`≤`=`rlctAt_mono` banked; `≥` symmetric). **The genuine content is elsewhere:** (i) the ideal identity =
Object B (the resolution, the real hard part); (ii) the Mathlib-ABSENCE of rlct/germ/integral machinery = a
BUILD, not a monument. Named risk: gluing chart-local bounded-coefficient estimates over a finite cover of
the proper resolution.

## (d) Verified vs genuinely open (for the architect's decomposition)
**VERIFIED** (exact + Gröbner + decorrelated Codex + controller-run battery): the combinatorial layer;
the coupled diag(b) MECHANISM (peel + radial + join) at (3,3,4)/(3,3,2,2)/(2,2,4); the single-exponent-Mval
binding divisor; Frobenius-non-preservation ⟹ Lemma 1 load-bearing; Case-2 running-min governance; the
Lemma-1 ≥ reduction.
**GENUINELY OPEN (frontier leaves, honestly named):** (1) `⟨∏C⟩=⟨diag(b)⟩` + divisibility chain in **full
L/width generality** — proven at instances, owed ∀; this IS Object B. (2) Lemma 1 both directions in Lean
at full generality (rlct/germ machinery — a build). (3) Monomial-ideal RLCT general/coupled Newton in Lean
(Object C). (4) Order ρ (Object E) — untouched (deprioritised, kept in reach).

## The boundary + the recommended next kill-instance (the pnp's own honest flag)
The general-L divisibility-chain reading (single dominant monomial) is verified only at instances. **Most
likely to break it:** an **L≥4 coupled binder with TWO independent shared deep factors** (a `(3,3,4,·)`-type
per §5 of the 334 work) — where the deepest chart may NOT monomialise to a single divisibility chain. This
MUST be probed before committing the general-L Object-B statement (kill-set adequacy; the shallow-instance
confound). → dispatched as the next pen-and-paper probe.

## Controller calibration note (2026-07-20)
Ran `g-coupled-334-diagb.py` (EXIT 0): peel + Frobenius-non-preservation + loss=E²·unit + h_E=7 → rlct 4
all confirmed. One misleading print — `(C) … <b1,b2,b3>=<b1> (principal): False` — is a **sympy-`%`
artifact** (line 119 tests `b2 % b1 == 0`, which sympy does not reduce for symbolic products); the real
divisibility check (`chain_ok`, line 109) is True and the PASS assertion uses it. Principality holds via
divisibility; the "False" is a print bug, not a mathematical discrepancy. (Battery print worth tidying;
non-load-bearing.)
