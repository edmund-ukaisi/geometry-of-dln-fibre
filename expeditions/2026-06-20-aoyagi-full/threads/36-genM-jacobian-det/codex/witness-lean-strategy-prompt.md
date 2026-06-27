# Lean 4 / Mathlib v4.29 strategy review — the nonzero-Hmat witness (dead-leaf + carrier), opaque dependent widths

I am formalising `∃ w : Fin N → ℝ, achieverUfun w ≠ 0` (the last rate-side gap). This reduces (via banked lemmas) to: at a chosen witness point `w`, the ℝ matrix `Hmat 0 : Matrix (Fin (Text 0)) (Fin (Wext L)) ℝ` of an abstract telescope `Chain` is NONZERO (it is a sum-of-squares `∑∑ (Hmat 0 i j)^2`, so `≠ 0 ⟺ ∃ i j, Hmat 0 i j ≠ 0`).

## The `Chain` structure (banked, sorry-free)
```
structure Chain (n : ℕ) (u : 𝕜) where
  Wwid Twid : ℕ → ℕ
  A : (k:ℕ) → Matrix (Fin (Wwid k)) (Fin (Wwid (k+1))) 𝕜
  C : (k:ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid k)) 𝕜
  B : (k:ℕ) → Matrix (Fin (Twid k)) (Fin (Twid (k+1))) 𝕜
  E : (k:ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid (k+1))) 𝕜
  R : Matrix (Fin (Twid n)) (Fin (Wwid n)) 𝕜
  step base ...
-- suffix s : Matrix (Fin (Wwid s)) (Fin (Wwid n)); suffix n = 1; suffix s = A s * suffix (s+1)
-- Hmat s : Matrix (Fin (Twid s)) (Fin (Wwid n)); Hmat n = R; Hmat s = B s * Hmat (s+1) + E s * suffix (s+1)
```
Banked unfold lemmas: `Hmat_succ c s (h:s<n) : Hmat s _ = B s * Hmat (s+1) _ + E s * suffix (s+1) _`; `Hmat_last : Hmat n _ = R`; `suffix_succ`, `suffix_last`.

For my instance `n = L`, `Wwid = Wext M` (`Wext k = M k`), `Twid = Text M (tach M)` (`Text 0 = M0`, `Text (k+1) = tach k`). The chain comes from `chainOfMt` with a STRUCTURED decoder `genBlkFlatStruct` reading FREE coordinates from disjoint flat slots:
- `B k = Bmat k`: `k=0` is `reindex 1` (identity, Text0=Text1); `k+1` is `bmatStack (readK) (readX)` = stacked `[K ; X·K]` (top Text(k+2) rows = K, bottom rows = X·K). Entry laws `bmatStack_top`/`bmatStack_bot` banked.
- `E k = Rmat k * A k`, where `Rmat (k+1) = rmatPad (readE)` = `[[0,0],[0,E]]` (E in bottom-right r_k×c_k); `Rmat 0 = 0`. `A k = chainA (readN k) (readW k) (C (k+1))` with entry laws `chainA_apply_castAdd` (top Text(k+1) rows = `C-N*W`) / `chainA_apply_natAdd` (bottom rows = W).
- `R = Rfin L = 0` always.
- `readK/X/N/E/W x` read single coords `x (chartIdxEquiv.symm ⟨k, …⟩)`; disjoint slots. The witness `w` is a function `Fin N → ℝ`; I set it to 0 except a chosen deep-E coord (value `e`) and carrier-W coords (value `ω`).

## The construction (pen-and-paper VALIDATED, sympy-exact on (3,3,1,3))
`q := deepest boundary with Text q > 0` (q≥1 since Text 1 = M0≥1; dead-leaf case q<L since Text L = 0).
Witness `w`: K=I (so readK = identity entries), X=0, N=0, all E=0 EXCEPT `E_q(0,0)=e`, all W=0 EXCEPT carriers `W_b(0,0)=ω` for `b ∈ [q, L-1]`.
Then at `w`: `B_b = [I;0]` (top rows identity), `E_b = 0` for `b≠q`, `Hmat L = 0`, `suffix L = I`.
- `Hmat q = B_q·Hmat(q+1) + E_q·suffix(q+1)`. The `E_q·suffix(q+1)` term carries `e·∏ω` at row 0.
- For `s<q`: `Hmat s = B_s·Hmat(s+1) + 0` = picks up `Hmat(s+1)` row-0 entry via `B_s=[I;0]`.
Result `Hmat 0 (0,0) = e·∏carriers = e·ω^(L-q)` ≠ 0. Set `e=ω=1`.

Codex earlier suggested a `rowPath` carried symbolically + downward induction `H_entry_survives : ∀ s ≤ q, Hmat s (rowPath s) j₀ = e·∏ω`, base via `Hmat_last`/`suffix_last`/`Rfin=0`/`deep_E_entry`, step via `bmatStack_top` + `E_zero_before` + `Finset.sum_eq_single`.

## My questions
1. Is the `rowPath`-as-constant-`⟨0,_⟩` simplification sound here? At the witness, every `B_s` has top-rows = identity, so the surviving row index is 0 at EVERY level (rowPath s = ⟨0, _⟩ : Fin (Text s), needs Text s ≥ 1 for s ≤ q — true since q is the deepest positive Text). So I can DROP the symbolic rowPath and just use `i₀ := ⟨0, by …⟩` everywhere. Confirm or warn.

2. The cleanest Lean induction statement. I propose downward induction on `d := q - s` proving `P s : Hmat s ⟨0,_⟩ ⟨0,_⟩ = e * ω^(L-q)` for `s ≤ q`. But the matrix product `B_s · Hmat(s+1)` at entry (0,0) is `∑_t B_s 0 t * Hmat(s+1) t 0`; I need `Finset.sum_eq_single ⟨0,_⟩` with `B_s 0 t = if t=0 then 1 else 0` (top row of [I;0]). Is `bmatStack_top` enough to get `B_s ⟨0,_⟩ t = (1:Matrix) ⟨0,_⟩ t` for the `t` in the top block, and is there friction proving the OTHER rows/cols vanish? Suggest the tightest tactic skeleton.

3. The base case `Hmat q`: `Hmat q ⟨0,_⟩ ⟨0,_⟩ = (B_q·Hmat(q+1) + E_q·suffix(q+1)) ⟨0,_⟩ ⟨0,_⟩`. I want to show `B_q·Hmat(q+1)` contributes 0 (because `Hmat(q+1)` is 0 at the witness — its E-below-q all zero, B's all [I;0] but R=0 and all E=0 for s>q so Hmat(q+1)=0). Is proving `Hmat(q+1) = 0` (the whole matrix) by a SEPARATE downward induction `∀ s, q < s → s ≤ L → Hmat s = 0` cleaner than entry-wise? (Hmat L = R = 0; Hmat s = B_s·0 + E_s·suffix(s+1) = 0 since E_s=0 for s>q.) I think yes. Confirm.

4. The carrier propagation `E_q · suffix(q+1)` at (0,0) = `e·∏ω`. `suffix(q+1)` is a product of A-layers q+1..L-1, each `A_b = [C-N*W ; W]` with N=0 so top = C, bottom = W. With carriers W_b(0,0)=ω and the deep structure, suffix(q+1)(0,0) telescopes to ∏ω. This is itself a downward induction over suffix. Is it cleaner to prove `suffix s ⟨0,_⟩ ⟨0,_⟩ = ω^(L-s)` for q+1 ≤ s ≤ L by downward induction (base suffix L = I → 1; step suffix s = A_s · suffix(s+1), A_s row-0 picks the carrier)? Note: which row of A_s carries? At boundary b≥q+1, Text(b+1)=0 (below q all Text=0), so the "kept" top block of A_b has Text(b+1)=0 ROWS — so A_b is ALL lift rows = W_b! That means A_b = W_b directly (no kept block). So suffix(q+1) = W_{q+1}·…·W_{L-1}. Does the `Text(b+1)=0 ⟹ chainA is entirely natAdd block` simplify the entry law? Suggest how to exploit `Text(b+1)=0` to kill the castAdd block.

5. Overall: is this 5-lemma plan (zero-above-q ; suffix-carrier-product ; deep-E-entry ; entry-survives downward ; assemble) the right decomposition, or is there a materially simpler route given the banked entry laws? Estimate the hardest sub-lemma.

Please be concrete about Mathlib v4.29 tactics (`Finset.sum_eq_single`, `Matrix.mul_apply`, `Fin.cast`, the opaque-width `⟨0, by omega⟩` index handling). Answer tersely and rank the risks.
