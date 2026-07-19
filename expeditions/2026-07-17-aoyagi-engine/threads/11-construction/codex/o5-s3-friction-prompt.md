<task>
Lean 4 + Mathlib v4.29. I am completing a proof file
`lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean` (cwd = repo root
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/t01-r2 ;
READ that file — it has ~180 proven lines + 3 build errors + 2 more lemmas to add).

GOAL (cert §3, "envelope-splice"): prove **every Mval-minimizer of Adm M is Clearable**.
Defs (all real, read them): Lambda.lean has
  tPrev M T j = if j=0 then M 0 else T (j-1)   (ℤ)
  Mval M T = ∑ j:Fin L, (tPrev M T j - T j)*(M j.succ - T j)   (ℤ, factors signed but ≥0 on Adm)
  admBound M j = if j=0 then min (M 0) (M 1) else M j.succ
  admPred = weak-decrease ∧ (T j ≤ admBound M j) ∧ (last coord = 0);  Adm = piFinset.filter admPred
EngineDefs/EngineConstruction: widthMinUpto M n = min(M i : i ≤ n) (an inf' over a filter);
  widthMinUpto_succ M (h:n+1<L+1) : widthMinUpto M (n+1) = min (widthMinUpto M n) (M ⟨n+1,_⟩);
  widthMinUpto_zero : widthMinUpto M 0 = M 0 ; widthMinUpto_mono (h:m≤n): widthMinUpto M n ≤ widthMinUpto M m.
ClearableReify.Clearable M a := ∀ i j:Fin L, i.val+1=j.val → a j < a i → a i = widthMinUpto M j.val →
  ∀ m:Fin L, m.val ≤ i.val → a m = widthMinUpto M (m.val+1).
tStar M : Fin L → ℕ is the banked Mval-minimizer (RouteMAchieverPath), tStar M ∈ Adm M.

The file ALREADY PROVES: adm_le_widthMinUpto (a m ≤ widthMinUpto M (m+1)), mval_term_nonneg,
envVal M k = widthMinUpto M (k+1), prefix_forces_env (all summands ≤ i vanish ⟹ T = envelope up to i),
spliceEnv M a i = (envelope on ≤i, a beyond), spliceEnv_le_envVal.

THREE BUILD ERRORS + TWO OWED LEMMAS. I need your diagnosis on the two frictions (RULINGS mandate
consulting these FIRST) and a structural sanity-check on the two owed lemmas:

1. FIN-LITERAL FRICTION — `envVal_le_admBound` line ~151, k.val=0 case:
   `have hM1 : M (1 : Fin (L+1)) = M ⟨k.val+1, by omega⟩ := by apply congrArg M; apply Fin.ext; rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]; omega`
   errors "omega could not prove the goal" at the inner `Nat.mod_eq_of_lt (by omega)` (needs 1 < L+1; hL:0<L is in scope). What is the clean idiom to prove `M (1:Fin(L+1)) = M ⟨k.val+1,_⟩` when k.val=0? (the recurring (2,2,4)-era opaque-Fin-literal quirk.)

2. SEAM PLACEHOLDERS — `spliceEnv_mem_Adm` lines ~198-201, weak-decrease seam. Goal shape: prove
   `spliceEnv M a i.val` is weakly decreasing, given a∈Adm, i.val+1=j.val, a j < a i, a i = widthMinUpto M j.val.
   The seam case: p.val ≤ i.val (in envelope prefix) and q.val > i.val (beyond, = a q). Need
   `spliceEnv q = a q ≤ spliceEnv p = widthMinUpto M (p+1)`. Chain: a q ≤ a j (weak-dec, q ≥ j) < a i
   = widthMinUpto M j.val = envVal i ≤ envVal p = widthMinUpto M (p+1) (envelope antitone, p ≤ i). Give the
   clean tactic sequence (the `hdec`/`widthMinUpto_mono` lemmas, careful Fin index arithmetic).

3. SANITY-CHECK the two owed lemmas' structure (don't write full proofs, just the cleanest decomposition):
   (a) Mval-comparison: for non-clearable a∈Adm, Mval (spliceEnv M a i) < Mval a where i is the
       pre-saturation index of the first bad descent. Cert: splice prefix summands (≤i) become 0
       (envelope value zeroes each term), a's prefix has some summand >0 (non-envelope, by
       contrapositive of prefix_forces_env), boundary term (j) + suffix (>j) unchanged. What's the
       cleanest split of ∑ into prefix/boundary/suffix, and how to get the strict drop?
   (b) final: every minimizer is Clearable (contrapositive: non-clearable ⟹ ∃ strictly cheaper admissible sibling ⟹ not minimizer). Any pitfalls tying this to tStar / minAdm = inf' Mval?
</task>

<output_contract>
Four sections, terse. §1: the exact Lean idiom for the Fin-literal friction (a working snippet).
§2: the seam tactic sequence (a working snippet). §3: the prefix/boundary/suffix ∑-split for the
Mval-comparison + how the strict drop is obtained (Finset.sum_lt_sum or similar; which term is strict).
§4: the final-lemma decomposition + any pitfall. Flag anything you're unsure of as [UNSURE].
</output_contract>

<grounding_rules>
You may READ the repo files (read-only). Ground claims in the actual defs/lemma signatures you find;
if you assert a Mathlib lemma exists, name it exactly (v4.29). Flag inference vs verified-from-file.
</grounding_rules>
