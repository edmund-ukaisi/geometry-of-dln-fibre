<task>
Lean 4 / Mathlib v4.29. I am porting a proven `L = 2` "role partition" equiv to general `L`.
I must build ONE equiv and its two readbacks; pick the construction that minimizes Lean pain.

## Fixed conventions (do not change)

- `L : ℕ`, widths `H : Fin (L + 1) → ℕ` (vertices `0..L`), rank `r : ℕ`.
- `FlatRowIdx H := Σ s : Fin L, Fin (H s.castSucc)` ; `FlatIdx H := Σ q : FlatRowIdx H, Fin (H q.1.succ)`.
  So a flat index is `⟨⟨s, i⟩, j⟩` with `s : Fin L` (LAYER), `i : Fin (H s.castSucc)`, `j : Fin (H s.succ)`.
- Pivot family `ι : (v : Fin (L+1)) → Fin r → Fin (H v)`, `hι : ∀ v, Function.Injective (ι v)` (one per VERTEX).
  Layer `s : Fin L` splits rows by `sumSplit (ι s.castSucc) (hι s.castSucc)` and cols by `sumSplit (ι s.succ) (hι s.succ)`,
  where `sumSplit σ hσ : Fin r ⊕ Fin (n - r) ≃ Fin n` places pivots in `Sum.inl`, so `.symm` classifies pivot(inl)/nonpivot(inr).
- `CoreIdxGen H r := FlatIdx (fun s => H s - r)` ; `RegIdxGen H r := (Fin (H 0 - r) × Fin r) ⊕ (Fin r × (Fin r ⊕ Fin (H (Fin.last L) - r)))`.
- `card_RegIdxGen : Fintype.card (RegIdxGen H r) = r*(H 0 + H (Fin.last L) - r)` is PROVEN.

## The role table (Codex-settled earlier), block = (row-class, col-class):

  s = 0:        ₁₁ SPEC  ₁₂ SPEC  ₂₁ REG   ₂₂ CORE
  0 < s < L-1:  ₁₁ SPEC  ₁₂ SPEC  ₂₁ SPEC  ₂₂ CORE
  s = L-1:      ₁₁ REG   ₁₂ REG   ₂₁ SPEC  ₂₂ CORE

CORE = every layer's ₂₂ (nonpiv row, nonpiv col), layer-preserved  ==  FlatIdx (H-r).
REG  = first layer's ₂₁  (nonpiv, piv)  ⊕  last layer's ₁₁,₁₂ (piv, any col).
SPEC = the rest (first ₁₁,₁₂; last ₂₁; ALL interior ₁₁,₁₂,₂₁).

## What the downstream needs (the equiv feeds `splitOfPartition`)

I must produce `e_idx_gen : Fin nReg ⊕ (Fin (flatDim (H-r)) ⊕ Fin specDim) ≃ Fin (flatDim H)`.
`splitOfPartition e` reads `(split x).2.1 j = x (e (inr (inl j)))` BY RFL. So the CORE slot of the equiv
must reduce (rfl or one simp) to the ₂₂ flat coordinate `⟨⟨s, sumSplit (ι s.castSucc) _ (inr i')⟩, sumSplit (ι s.succ) _ (inr j')⟩`,
so that the KEY lemma `paramsEquivFlat_symm_splitMP_core : (paramsEquivFlat (H-r)).symm (split x).2.1 = coreParams x`
goes through (in L=2 it was `rfl` + `simp [roleToFlat]`). REG readbacks similar. SPEC is untouched (no readback).

## The L=2 template (PROVEN, what I am generalizing)

At L=2 there are NO interior layers. `roleToFlat : RegIdx ⊕ (CoreIdx ⊕ SpecIdx) → FlatIdx H` is a hand-written
`match` (layer hardcoded 0/1 for Reg/Spec, layer-preserved for Core). `flatToRole` classifies via nested
`Fin.cases` on `Fin 2` then `sumSplit.symm` on row/col. `roleEquiv := Equiv.ofBijective roleToFlat (injective-from-leftinverse + card_role_eq)`.
`SpecIdx` is an EXPLICIT sum (first ₁₁,₁₂ ⊕ last ₂₁). The Core readback `e_idx_core` is `rfl`.

## The general-L difficulty

(1) SpecIdx now must also include ALL interior layers' ₁₁,₁₂,₂₁ — a dependent `Σ` over interior `s`, painful to enumerate.
(2) Naming first/last LAYER as elements of `Fin L`: `(0 : Fin L)` needs `0 < L`; the last layer `⟨L-1,_⟩ : Fin L`
    has `.succ` equal to `Fin.last L : Fin (L+1)` only up to the `(L-1)+1 = L` proof — a defeq gap that bites `RegIdxGen`'s
    `Fin (H (Fin.last L) - r)` vs `Fin (H (last-layer).succ - r)`.
(3) The `flatToRole` classifier would need a first/interior/last layer dispatch producing role values whose TYPE depends on s,
    with a junk case for spec cells that may be EMPTY (no default element).

## Three candidate constructions I am weighing

(A) COMPLEMENT-SUBTYPE. Build injective `regCoreEmb : (RegIdxGen ⊕ CoreIdxGen) → FlatIdx H` (explicit `match`,
    core layer-preserved, reg at layers 0 / L-1). Set `SpecIdxGen := {x // x ∉ Set.range regCoreEmb}`. Then
    `roleEquivGen := (Equiv.sumCongr (Equiv.ofInjective regCoreEmb hinj) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range regCoreEmb))`,
    reassociate with `Equiv.sumAssoc`. AVOIDS interior enumeration AND card_role_eq. Cost: injectivity of regCoreEmb,
    and confirming Core readback stays rfl through `ofInjective`/`sumCompl`/subtype coercion.

(B) L=2-PORT. Explicit `SpecIdxGen` sum WITH an interior `Σ (s : {s : Fin L // 0 < s ∧ s+1 < L}), (...)`, hand-written
    roleToFlat/flatToRole with a 3-way layer dispatch, prove left-inverse + card_role_eq. Faithful to L=2 but heavy.

(C) COMBINATOR. `FlatIdx H ≃ Σ s, (Fin(H s.castSucc) × Fin(H s.succ))`, per-layer `(sumSplit.symm ×) ≫ prod-sum-distrib`
    to 4 blocks, regroup `Σ s (B11⊕B12⊕B21⊕B22) ≃ (Σ s B22) ⊕ rest`, peel layers 0 and L-1 for Reg via Fin.cons/snoc.
    No injectivity, no junk; but combinator soup + Reg-corner peeling of a `Σ` over `Fin L`.

<output_contract>
1. RANK (A)/(B)/(C) for least total Lean friction to a green build with the REQUIRED rfl-ish Core readback. One paragraph why the winner.
2. For the WINNER: the precise `Equiv`/def construction (name the exact Mathlib combinators + their key simp/defeq lemmas),
   and how the Core readback `(split x).2.1 j = ...₂₂ coordinate` is discharged (rfl? which simp lemmas?).
3. For the WINNER's hardest obligation (e.g. injectivity of regCoreEmb, or the interior Σ, or the combinator readback),
   give a concrete Lean proof SKETCH (tactics + the disjointness/recovery argument), noting the exact case structure.
4. The first/last LAYER indexing + the `(L-1).succ = Fin.last L` defeq gap: recommend the cleanest handling
   (carry `0 < L`? destructure `L = n+1` via `obtain`/`match`? `Fin.lastCases`/`Fin.cons`/`Fin.snoc`? finCongr casts?).
   Give the concrete idiom.
5. Any TRAP that will cost me an hour if unwarned (measurability through the reindex, DecidablePred for sumCompl,
   Fintype instance on the subtype, `Set.range` vs `Function.range`, heq in Sigma equality, etc.).
</output_contract>

<grounding_rules>
Flag any Mathlib lemma name you are not sure exists in v4.29 as "verify". Distinguish "this is defeq" (rfl works)
from "needs a simp lemma" explicitly. Do not invent a combinator; if unsure of the exact name, describe its type and say "verify name".
</grounding_rules>
</task>
