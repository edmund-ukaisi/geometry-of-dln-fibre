# L3.2a follow-up — the nested minor-pivot cover, BUILD-READY (de-risks the general-lift N2)

**Seat:** `pen-and-paper` (design, no Lean). **Date:** 2026-06-25. **Thread:** `28-hfin-recStep-spec`.
**Target (controller follow-up to `L32a-cover-cert.md`):** pin the exact Lean shape of the **nested
minor-pivot cover** — the piece I flagged as not-yet-verbatim-reuse, which de-risks the GENERAL lift's
fragile N2 (`schur_minorPivot_split`). Two sub-questions: (a) does `argmaxCellOn`/`Finset.exists_max_image`
over the `j×j`-minor index set discharge the second-level cover-up-to-null cleanly (with `{all j×j minors
= 0}` the next-lower level)? (b) pin the `r≥3` block-Gauss det-1 shift bookkeeping for the explicit block
identity. **Method:** exact sympy (Cramer minor-ratio, block-diagonal Schur, comparison constants) +
decorrelated Codex (xhigh, independent). Scripts `scripts/L32a_{minorpivot_cover,disjoint_split,Q4_edge,
Q4_cramer,morse_divisor}.py`; Codex `codex/L32a-minorpivot-{prompt,answer}.md`. (`(3,3,4)`/`r=2` is
`ring`-clean and does NOT need this — this de-risks the general `r≥3` lift, ahead of `r1-ladder`.)

---

## VERDICT: the nested minor-pivot cover is BUILD-READY for general `r`. It reuses the generic
## `argmaxCellOn`/`Finset.exists_max_image` cover at the MINOR level (no "rank = max nonzero minor"
## theorem), with FOUR build refinements pinned (three from the decorrelated Codex, all exact-confirmed):
## **(R1) comparison-not-equality**, **(R2) Cramer minor-ratio shear bound `≤ 1` [closes the `det→0`
## edge]**, **(R3) deterministic tie-break for disjointness [avoids the algebraic-null proof]**, **(R4)
## per-level RE-PINNING by radial blow-up [closes the termination/no-inherited-pin gap]**.

> **The one-line shape.** The inner `R`-space recursion is the SAME radial-blow-up + `argmaxCellOn`
> machinery, alternated at each corank level: `[radial Δ=a·R re-pins a nonzero entry] → [argmaxCellOn over
> the j×j MINOR-index Finset, pivot = max-modulus minor M11] → [det-1 block-Gauss ⟹ Schur complement Sc,
> corank r−j] → [recurse on ‖Sc·Q‖²]`. The minor-pivot bound is the classical **complete-pivoting**
> fact: with the max-modulus `k`-minor as pivot, the Gauss multipliers `M21·M11⁻¹` have entries `≤ 1`
> (each is a Cramer ratio of `k`-minors, numerator `≤` the max `= det M11`). Depth `≤ r`.

---

## 1. (a) THE NESTED MINOR-PIVOT COVER — reuses `argmaxCellOn` at the minor level (Q1, Q2)

**The atlas (corank descending, NO rank-minor bridge).** Cover the inner `R`-space by levels
`k = r, r−1, …, 1`:
- **Level k:** on `{some k×k minor of R has det ≠ 0}`, run `argmaxCellOn` with `active` = the Finset of
  all `k×k` minor-index pairs `(I,J)` and "coordinate" `R ↦ det(R.submatrix I J)` (a polynomial,
  measurable). `Finset.exists_max_image` picks the pivot `(I*,J*)` with maximal `|det|`, nonzero ⟹ that
  `k×k` minor `M11` is INVERTIBLE on its cell.
- The complement `{all k×k minors = 0}` is **NOT dropped as null** and **NOT asserted `= {rank < k}`** —
  it is simply the domain of Level `k−1` (its own argmax over `(k−1)`-minors).
- **Termination:** the radial blow-up RE-PINS a nonzero entry at each level (R4), so `rank R ≥ 1`; each
  level's residual Schur block is strictly smaller, reaching size `1` in `≤ r` levels. At size `1`,
  `‖Sc·Q‖² = Sc²·∑Q²` (scalar `Sc`), a clean monomial × Morse — terminal.

> **Codex (Q1) = NEEDS-CARE → closed by R4.** Codex's gap: the Schur complement `Sc` does NOT inherit
> the original pinned entry, so termination cannot rely on it. **Fix (R4, `L32a_morse_divisor.py`):** the
> recursion RADIALLY BLOWS UP the residual core `‖Sc·Q‖²` afresh (`Sc = a'·R'`, `R'` re-pinned to 1) at
> each level — the pin is RE-ESTABLISHED per level, not inherited. The `{Sc = 0}` zero-residual endpoint
> is exactly that level's `a'=0` null divisor (dropped as the top `{Δ=0}`). This matches thread 27's
> validated alternating radial-blow-up + rank-recursion structure.

> **Codex (Q2) = CORRECT for cover, NEEDS-CARE for disjointness → R3.** `Finset.exists_max_image` works
> for any finite family of measurable real functions (not just linear coords), so the argmax-over-minors
> cover is valid (cells = preimages of argmax cells under the polynomial minor map). For
> **a.e.-disjointness**, the tie set `{|det minor_a| = |det minor_b|}` is a proper algebraic hypersurface
> (null), but **proving "proper polynomial zero set is null" is expensive in Lean**. **Fix (R3, Codex):**
> impose a DETERMINISTIC tie-break order on the minor-index Finset (well-order, pick the least index on a
> tie) ⟹ genuinely disjoint measurable cells, no algebraic-null proof needed. (The existing
> `argmaxCellOn_aedisjoint` uses `absEq_null` for COORDINATE pivots; at the minor level, prefer the
> tie-break to avoid a per-minor-pair algebraic-null lemma.)

**Verified (exact, `L32a_minorpivot_cover.py`):** the level structure, the max-minor-invertible pivot,
the Schur determinant identity `det R = det M11 · det Sc` (`r=2,3`), the corank drop `r → r−j`.

---

## 2. (b) THE `r≥3` BLOCK-GAUSS det-1 SHIFT — the explicit `schur_minorPivot_split` (Q3, Q4)

**The exact block-diagonal reduction (verified `r=2,3`, `L32a_disjoint_split.py`).** On the
minor-pivot cell, with `M11` the invertible `j×j` pivot (after a permutation to top-left — sign tracked,
det-1):

    L · R · U  =  blockdiag(M11, Sc),   Sc = M22 − M21·M11⁻¹·M12,
    L = [[I, 0], [−M21·M11⁻¹, I]],  U = [[I, −M11⁻¹·M12], [0, I]]   (both unitriangular, det 1).

> **Verified:** `L·R·U = diag(M11, Sc)` exactly, `det L = det U = 1`, for `(r,j) = (2,1),(3,1),(3,2)`.

**R1 — COMPARISON, not equality (Q3, the key correction to the #54 spec L2.2).** The naive
`‖R·S‖² = unit·‖P‖² + ‖B·Q‖²` **equality is FALSE** — `L` is non-orthogonal, so `‖L⁻¹·X‖² ≠ ‖X‖²`. The
honest statement (det-1 `S`-reparam `S = U·(P;Q)`, `P,Q` DISJOINT):

    c0·(‖M11·P‖² + ‖Sc·Q‖²)  ≤  ‖R·S‖²  ≤  c1·(‖M11·P‖² + ‖Sc·Q‖²),   0 < c0 ≤ c1 < ∞.

The threshold of `‖R·S‖²^{−c'}` is preserved by this bounded sandwich (`c1^{−c'}·D^{−c'} ≤ ‖RS‖^{−2c'} ≤
c0^{−c'}·D^{−c'}`, `c'>0`). This IS the `step2E_unit_ge_one`/`Uval334_ge_sq` bounded-unit pattern the
`(2,2,2)`/`(3,3,4)` proofs already use — NOT a new analytic device. **Codex (Q3) = CORRECT.**

**R2 — the comparison constants are ABSOLUTE (`≤ 1` shear), closing the `det M11 → 0` edge (Q4).** The
load-bearing risk: `M21·M11⁻¹ = M21·adj(M11)/det(M11)` looks like it blows up as `det M11 → 0`. It does
NOT, by the classical complete-pivoting bound, which I proved **symbolically** (`L32a_Q4_cramer.py`):

> Each shear entry is a Cramer minor-ratio:
> `(M21·M11⁻¹)[a,b] = det( M11 with row b replaced by M21's row a ) / det(M11)` — the numerator is a
> `k×k` MINOR of `R`. Since `M11` is the **max-modulus** `k`-minor (the argmax pivot), `|numerator| ≤
> |det M11|`, so **`|shear entry| ≤ 1`**. Symbolically verified for `(r,k) = (2,1),(3,1),(3,2),(4,2),
> (4,3)`. (MC guide `L32a_Q4_edge.py`: max shear `≈ 1.4` over 200k random `r=3` — consistent, but the
> `≤ 1` entrywise bound is the EXACT certificate.) The shear does not blow up because the numerator minor
> shrinks in lockstep with `det M11` (both are `k`-minors, `M11` the max).

> **Codex (Q4) = CORRECT, independently:** "the numerator is a `k×k` minor of `R`; since `M11` was chosen
> with maximal `|k`-minor`|`, `|numerator| ≤ |det M11|`, so each entry of `A` has `|·| ≤ 1`. … `M11 =
> diag(ε,1)`: the inverse has size `1/ε`, but the max-minor condition forces outside-row replacement
> minors to be `O(ε)`, cancelling the blow-up." Both shears `M21·M11⁻¹` AND `M11⁻¹·M12` are bounded
> (the latter by column-replacement minor-ratios). The cell needs **NO further subdivision**.

**R-tail — `‖M11·P‖²` is a Morse block of threshold `jp/2`, `det M11` only in the constant (Q3 tail,
`L32a_morse_divisor.py`).** Codex's sharp tail: the comparison gives `‖M11·P‖²` (full-rank, `M11`
invertible POINTWISE), a `jp`-dim Morse block of threshold `jp/2` REGARDLESS of `det M11` (any
nondegenerate quadratic form on `ℝ^{jp}` has threshold `jp/2`). The `det M11`-variation is NOT a new
divisor — it is the corank-`(r−j)` core's OWN singularity, already accounted by `λ_{r−j,p}` in the
recursion (R4: it is re-blown-up at the next level). **No double-count, no new threshold.**

---

## 3. THE PRECISE LEAN TARGETS (refines `L32a-cover-cert.md` §4 N2)

### N2a `shear_entry_minor_ratio` (LOW–MEDIUM, the Cramer bound — the critical bridge per Codex Q5)
```
theorem shear_entry_le_one {r k : ℕ} (R : Matrix (Fin r) (Fin r) ℝ) (I J : ...k-subsets...)
    (hmax : ∀ I' J', |（R.submatrix I' J').det| ≤ |(R.submatrix I J).det|)   -- the argmax pivot
    (hne : (R.submatrix I J).det ≠ 0) (a b) :
    |(M21 * (M11)⁻¹) a b| ≤ 1
```
Proof: Cramer `(M21·M11⁻¹)[a,b] = (a k×k minor of R)/det M11`, then `hmax`. **Mathlib confirmed
present** (`Adjugate.lean`/`NonsingularInverse.lean`): `Matrix.inv_def` (`A⁻¹ = det⁻¹ • adjugate`),
`Matrix.mul_adjugate`, and `Matrix.cramer_apply` (`cramer A b i = (A.updateCol i b).det`) — exactly the
"minor with one column/row replaced by an outside vector" determinant that makes each shear entry a
minor-ratio (use `cramer` on `M11` with `b` = an `M21` row/`M12` col). The classical complete-pivoting
bound; the bridge Codex flagged as the main formalisation cost.

### N2b `schur_minorPivot_split` (MEDIUM, the comparison — REVISED to `≤`/`≥`, NOT `=`)
```
theorem schur_minorPivot_split {r k p : ℕ} (R …) (M11 invertible, max minor) (S …) :
    ∃ (c0 c1 : ℝ) (hc : 0 < c0) (hc' : c0 ≤ c1) (P : Matrix (Fin k) (Fin p) ℝ)
      (Sc : Matrix (Fin (r-k)) (Fin (r-k)) ℝ) (Q : Matrix (Fin (r-k)) (Fin p) ℝ),
      R.det = M11.det * Sc.det
    ∧ c0 * (‖M11 * P‖_F² + ‖Sc * Q‖_F²) ≤ ‖R * S‖_F²
    ∧ ‖R * S‖_F² ≤ c1 * (‖M11 * P‖_F² + ‖Sc * Q‖_F²)
```
where `c0,c1` are ABSOLUTE (from N2a's `≤ 1` shears + the bounded chart). `P,Q` are the det-1 `S`-reparam
`S = U·(P;Q)`. The two bounds + the disjoint-sum threshold + `radial_morse_dominates_lt_top` (L1.1) give
the per-cell finiteness. **Build risk MEDIUM** — the `r=2`/`(3,3,4)` case has scalar `M11`, `≤ 1` shear
trivial; the `r≥3` block-Gauss permutation bookkeeping is the genuine cost (Codex Q5 second-cost).

### N2c the minor-level cover (LOW, reuse + tie-break)
`argmaxCellOn` over the minor-index Finset via `Finset.exists_max_image` (the polynomial "coordinate"
`det∘submatrix`); **deterministic tie-break order for disjointness (R3)** rather than the algebraic-null
`absEq_null` analog.

### Build-risk ranking (refined, per Codex Q5)
1. **(MEDIUM, the critical bridge) N2a** — the Cramer minor-ratio shear bound, used uniformly over all
   minor-index pairs + permutations. The classical fact; Mathlib has the adjugate/`updateRow` det
   machinery (confirm the minor-replacement lemma exists).
2. **(MEDIUM) N2b** — the Schur block-Gauss bookkeeping for arbitrary indexed submatrices + permutations
   (the determinant identity is standard; the index alignment is tedious).
3. **(LOW) N2c** — minor-level argmax cover + tie-break.

Codex Q5: do NOT use a global blow-up of the maximal-minor ideal (cleaner conceptually, heavier in
Mathlib); the nested finite argmax cover is more elementary and Lean-compatible.

---

## 4. CLOSE (the discipline trio)

- **Firmest result.** The nested minor-pivot cover is BUILD-READY for general `r`: it reuses
  `argmaxCellOn`/`Finset.exists_max_image` at the minor level (no rank-minor bridge), with the four
  refinements pinned — comparison-not-equality (R1), Cramer minor-ratio shear `≤ 1` closing the `det→0`
  edge (R2, exact for `(r,k)` up to `(4,3)`), deterministic tie-break (R3), per-level re-pinning closing
  termination (R4). The Schur identity `det R = det M11·Sc` and the block-diagonal `L·R·U = diag(M11,Sc)`
  are sympy-exact. Decorrelated Codex independently confirmed Q1–Q5 with these exact refinements.
- **Most likely to break it (Codex Q5 + my read).** N2a — proving and USING the Cramer minor-ratio shear
  bound uniformly over arbitrary minor-index pairs and permutations in Lean (the bridge from "argmax
  minor" to "bounded comparison"). The math is the classical complete-pivoting bound (closed exactly
  here); the Lean cost is the index/permutation bookkeeping, not a math risk.
- **Next construction / consult to settle the open part.** Confirm the exact Mathlib lemma for the
  minor-replacement determinant (`det(M11 with row b ← M21 row a) = ±` a submatrix det) — `Matrix.det_
  updateRow_eq` / `mul_adjugate` chain — so N2a is fully grounded; then `r1-ladder` hits N2 (the `r=2`
  scalar case) first and the general `r≥3` N2b/N2a lands behind it. The minor-level cover + tie-break
  (N2c) is the one piece to prototype as a small standalone `argmaxCellOn`-over-a-`Finset`-of-minors
  example, confirming `Finset.exists_max_image` discharges it as cleanly as the coordinate version.

**Cross-ref:** this refines `L32a-cover-cert.md` §3 (the rank recursion) and §4 (N2). The main cert's
cover/Jacobian/integrand/threshold/termination verdicts are unchanged; this pins the second-level cover's
exact Lean shape and corrects the L2.2 split from `=` to a bounded `≤`/`≥` comparison.
