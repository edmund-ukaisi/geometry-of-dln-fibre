# Frame-stripping bridge — Lean route + HONEST effort read

The producer's (d')/(e') is down to ONE obligation: `hR : Rcore = S0·(1−K)·S1` (the hypothesis the
banked S5c atom `schur_core_germ_comparability` consumes). The algebra is VERIFIED true (sympy ALL ZERO,
`two-layer-ldu-verify.py`; `K = Z1·P⁻¹·Y0`, `P = A0A1+Y0Z1`). The question: the LEAN route + an honest
contained-vs-multi-tide read. **Honest verdict: CONTAINED-to-MODERATE (NOT research-grade multi-tide) at
L=2 — Mathlib's `SchurComplement` API supplies the block-LDU building blocks; the genuine work is a
directed ~150-250 LoC derivation, not an open research problem.** Decorrelated Codex (xhigh) on the route.

## The bridge is TWO obligations — only ONE is new

### (A) Frame-stripping — ALREADY DONE (not new)
The "DESPITE the per-layer Pf,Qf frames" worry resolves: `framedLayer_s = Pf_s·reindex(fromBlocks (1+X_s)
Y_s Z_s T_s)·Qf_s`, and `∏(framedParamsPivot) = Pf₀·(∏ raw C_s)·Qf_{L-1}` with interior frames telescoping
to `I` at `2≤L`. The producer reindexes `P0·(∏A−B)·QL` where `P0,QL` ARE the endpoint frames — so the
ENDPOINT conjugation + interior telescope strip the frames, leaving the FRAME-FREE product `∏ C_s`,
`C_s = fromBlocks (1+X_s) Y_s Z_s T_s`. **This is exactly the (b)-exact reconstruction's `hconj`** (the
endpoint-telescope, banked/in-build for the front-pivot route). So the frame-stripping is NOT a new
obligation — it's the same `hconj` chain. The two-layer-ldu identity is on the frame-free `C_s`, which is
what `hconj` delivers. ⇒ **the frames don't enter the LDU — they're gone before it.**

### (B) The LDU `Rcore = S0·(1−K)·S1` on the frame-free product — the NEW piece
`Rcore = S − R·P⁻¹·Q` (the global Schur of `∏C = fromBlocks P Q R S`), claim `= S0·(1−K)·S1`,
`S_s = T_s − Z_s·A_s⁻¹·Y_s`, `K = Z1·P⁻¹·Y0`. THREE inverses (`A0⁻¹, A1⁻¹, P⁻¹`); no clean ring proof.

## The Lean route (the honest assessment — Mathlib has the toolkit)

**Mathlib `LinearAlgebra/Matrix/SchurComplement.lean` is the right toolkit** (it exists, axiom-clean):
- `fromBlocks_eq_of_invertible₁₁ A B C D [Invertible A] : fromBlocks A B C D = (lower-unipotent)·(blockdiag
  A (D−C⅟A B))·(upper-unipotent)` — the per-layer block-LU with the Schur complement `D − C⅟A B`.
- `invOf_fromBlocks_zero₂₁_eq` / `_zero₁₂_eq` — the unipotent/triangular inverses.

**Route (block-LDU, directed):**
1. **Per-layer LU** (`fromBlocks_eq_of_invertible₁₁` ×2, A_s = `1+X_s` invertible near 0):
   `C_s = L_s·D_s·U_s`, `L_s = fromBlocks 1 0 (Z_s⅟A_s) 1`, `D_s = blockdiag A_s S_s`,
   `U_s = fromBlocks 1 (⅟A_s Y_s) 0 1`, `S_s = T_s − Z_s⅟A_s Y_s`. (Mathlib lemma, direct.)
2. **The product + the unipotent strip**: `C0·C1 = L0·D0·(U0·L1)·D1·U1`. The global Schur of `C0C1` (wrt
   the (1,1) block) is INVARIANT under the outer `L0` (lower-unipotent, left) and `U1` (upper-unipotent,
   right): `Schur(L0·M·U1) = Schur(M)`. **This is the load-bearing sub-lemma** — Mathlib does NOT have
   "Schur invariant under unipotent congruence" directly; prove it from `fromBlocks_multiply` + the
   block-(2,2)-Schur-complement formula (`schur_P11_decomp`-style, or `Matrix.schur_complement_eq₂₂`).
   ~50-80 LoC (the unipotent factors' (1,1)=I, (2,1)/(1,2) shift the off-diagonal but the (2,2)-Schur
   absorbs it — a `fromBlocks_multiply` + `ring`-after-inverse-cancel computation).
3. **The middle `U0·L1`** (the non-telescoping part): `U0·L1 = fromBlocks (1+⅟A0 Y0 Z1 ⅟A1) (⅟A0 Y0)
   (Z1 ⅟A1) 1`. Then `D0·(U0 L1)·D1 = fromBlocks (A0(1+⅟A0 Y0 Z1 ⅟A1)A1) (A0 ⅟A0 Y0 S1) (S0 Z1 ⅟A1 A1)
   (S0·1·S1)` = `fromBlocks P (Y0 S1) (S0 Z1) (S0 S1)` (using `A0(1+⅟A0 Y0Z1⅟A1)A1 = A0A1+Y0Z1 = P`,
   `A0⅟A0=1`, `⅟A1 A1=1` — the inverse-cancels). ~40-60 LoC of block-mul + `invOf` cancellation.
4. **The Schur of `fromBlocks P (Y0S1) (S0Z1) (S0S1)`** (wrt P invertible): `= S0S1 − (S0Z1)·P⁻¹·(Y0S1)
   = S0·(1 − Z1·P⁻¹·Y0)·S1 = S0·(1−K)·S1`. The `S0·…·S1` factoring is `Matrix.mul_sub`/`mul_assoc` once
   the middle is `1 − Z1 P⁻¹ Y0`. ~30-40 LoC.

**Total: ~150-250 LoC**, directed (not search). The 3 inverses are handled as `Invertible` instances +
`invOf_mul_self`/`mul_invOf_self` cancellation (Mathlib's `Matrix.mul_invOf_cancel_*` simp set, used in
`fromBlocks_eq_of_invertible₁₁`'s own proof). The non-telescoping middle (step 3) is the `D0·(U0L1)·D1`
block-mul — explicit, not an obstruction.

## The honest contained-vs-multi-tide read

**CONTAINED-to-MODERATE, NOT research-grade multi-tide.** Reasoning:
- The MATH is verified (sympy ALL ZERO) — no math wall, as the brief notes.
- Mathlib's `SchurComplement` API provides the per-layer LU (step 1) + the inverse lemmas — the heaviest
  primitives are banked.
- The genuine new work is steps 2-4: the unipotent-strip Schur-invariance (step 2, the one real lemma)
  + two block-mul computations (steps 3-4). All directed, all `fromBlocks_multiply` + `invOf`-cancel +
  `ring`-after-block-extract — the SAME proof style as `schur_P11_decomp` (banked) and Mathlib's own
  SchurComplement proofs.
- **The "no clean ring proof" caveat is real but not fatal:** it's not ONE `ring` call, but it IS a
  bounded directed sequence of block-mul + inverse-cancel steps (≈ 4 lemmas), each individually `simp
  [fromBlocks_multiply] + invOf-cancel + ring`-shaped. Risk is BOOKKEEPING (block-index alignment, the
  `Invertible P` instance from `A_s` units), NOT mathematical depth.

**Realistic effort: MODERATE 2-3 tides (~200-350 LoC)** (padded from my first 150-250 after decorrelated
Codex — the extra is Lean plumbing: `Invertible P` instance selection, `⅟` rewrite orientation, keeping
block terms in the `simp`-recognized shape). Single formaliser, NOT a multi-tide research grind.
- Step 2 (unipotent-strip Schur-invariance) is clean IF stated NARROWLY:
  `Schur(fromBlocks 1 0 L 1 · fromBlocks P Q R S · fromBlocks 1 U 0 1) = S − R·⅟P·Q` `[Invertible P]`
  — `fromBlocks_multiply` + `schur_complement_eq₂₂` + `mul_assoc`/`invOf_mul_self`/`mul_invOf_cancel_left`.
  ~60-120 LoC; balloons ONLY if formulated through `toBlocks` of arbitrary products (avoid that).
- **Do NOT use the direct route** (one big non-commutative expression, 3 inverse-cancel zones) — Codex
  + my read agree it's MORE brittle in Lean. The LDU route LOCALIZES the cancellation (A0/A1 first, then
  P, then the final factor). Reserve direct manipulation ONLY for the last `S0·S1 − S0·Z1·⅟P·Y0·S1 =
  S0·(1−K)·S1` factoring (`mul_sub`/`mul_assoc`).
- **Biggest risk: the `Invertible P` / `⅟P` bookkeeping** around the rewritten top-left block `P =
  A0A1+Y0Z1` (the instance + the `⅟` rewrite orientation). The `Invertible P` comes from `det P ≠ 0` at
  w0 (`P(w0) = 1`) on a neighborhood (same det-continuity as S5a). NOT a wall — a contained-to-moderate
  directed build.

## Composition + soundness (UNCHANGED from rcore-coreabsorb-cert)
With `hR` in hand, the banked S5c atom gives `|frobSq(Rcore) − frobSq(∏S)| ≤ C·Sreg`; `coreΦ = ‖∏S‖²`
(exact, the coreAbsorb decode); the in-sum two-sided `Sreg+frobSq(Rcore) ≍ Sreg+coreΦ` at γ=1+C closes
(d')/(e'). **Soundness-critical (unchanged): the IN-SUM charge, NOT a standalone `frobSq(Rcore) ≍ coreΦ`**
(the germ counterexample — the atom statement-card's `W=I+ηE₁₂` witness).

## Build-ready statement
    -- in DeepestSchurComparability (network-free) OR the framedParams apparatus (it references ∏C blocks):
    theorem schur_product_ldu {M : Type*} [Fintype M] [DecidableEq M]
        (A0 Y0 Z0 T0 A1 Y1 Z1 T1 : Matrix M M ℝ) [Invertible A0] [Invertible A1]
        (P := A0*A1 + Y0*Z1) [Invertible P] :
        (let S := Z0*Y1 + T0*T1; let R := Z0*A1+T0*Z1; let Q := A0*Y1+Y0*T1;
         S - R * ⅟P * Q)
          = (T0 - Z0*⅟A0*Y0) * (1 - Z1*⅟P*Y0) * (T1 - Z1*⅟A1*Y1)
Then `hR` for the producer instantiates this with the framed-product blocks (frame-free, post-`hconj`).
The general-L version telescopes (`R = S0 W0 S1 W1 … S_{L-1}`) — for the L=2 headline this two-layer
lemma suffices; general-L is a separate induction (heavier, NOT needed for the L=2 (b)-route).

## SCOPE / honest caveats
- The Lean route is for **L=2** (the two-layer LDU). General-L (`∏ S_k W_k`) is a separate induction —
  NOT needed for the L=2 headline, flag if the headline later needs L≥3.
- The block dimension is **general M** (the lemma is `Matrix M M`), so it covers the matrix core (r≥2 /
  M>1) — matching the S5c atom's generality. (The `Invertible P` instance comes from `A_s` units near w0
  + a neighborhood det-argument, same as S5a.)
- I did NOT prototype the step-2 unipotent-strip lemma in Lean — the LoC estimate is from the proof
  structure + the analogous `schur_P11_decomp`/Mathlib SchurComplement proofs, NOT a built prototype.
  If step 2 snags, the direct-block-mul fallback is the contained (if uglier) backstop.

## Files
- `/tmp/frame_strip_route.py` (the frame-stripping structure + the LDU route + inverse count). The
  verified algebra: `…/agent-a78499affaadcfb71/…/codex/two-layer-ldu-verify.py` (l2-core-de's, ALL ZERO).
  Mathlib: `LinearAlgebra/Matrix/SchurComplement.lean` (the per-layer LU + inverse toolkit).
  `codex/frame-stripping-{prompt,answer}.md` (decorrelated route consult).
