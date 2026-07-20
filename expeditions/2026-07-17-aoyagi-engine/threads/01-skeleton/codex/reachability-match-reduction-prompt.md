<task>
Lean 4 / Mathlib v4.29. I have a noncomputable def:

  noncomputable def conOracle (M : Fin (L+1) → ℕ) (s : ConState L) : ConDecision M s :=
    if h1 : L ≤ s.layer then oracleTerminal M s
    else if h2 : widthMinUpto M (s.layer+1) ≤ s.cleared then rolloverDecision M s _ h2
    else
      match hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared+1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with
      | some target =>
        match hf : chooseMin s target with
        | some f => (have htarget : s.cleared+1 ≤ target := <derived from hmin>; case1Decision M s f (target - s.cleared) _ _ _ _ _ _)
        | none => oracleTerminal M s
      | none => case2Decision M s _ _ _

  def ConDecision.stepChildren : ConDecision M s → List (StepChild M s)
    | .terminal _ _ => [] | .step _ children _ _ _ => children

  -- oracleTerminal = .terminal ...; rolloverDecision/case1Decision/case2Decision = .step ...

GOAL: prove `∀ c ∈ (conOracle M s).stepChildren, OracleInv M c.child`. Per concrete branch decision I already have a lemma giving OracleInv for its children. The ONLY blocker is reducing `conOracle M s` in `hc : c ∈ (conOracle M s).stepChildren` to the concrete branch decision.

FAILED so far:
1. `rw [conOracle]; split_ifs`; then in else-else branch `split at hc` → "Could not split an if or match expression in the type c ∈ ... of hc" (match is under `.stepChildren`, an application; split won't reach it).
2. `split` on the ∀-goal → same "could not split".
3. `rcases hmin : (<filterMap>).min? with _ | target` then `simp only [conOracle, dif_neg h1, dif_neg h2, hmin, case2Decision, ConDecision.stepChildren, List.mem_singleton] at hc` → hc NOT reduced; subsequent `subst hc` fails "did not find equation for eliminating hc". The equation-binding `match hmin : x with` does not iota-reduce under simp even after rewriting the discriminant to `none`.
4. `rw [conOracle, dif_neg h1, dif_neg h2] at hc` then `rcases hmin : (<filterMap>).min? with _ | target` → still not reduced.
</task>

<output_contract>
Answer Q1, Q2, Q3 in order, each with a concrete v4.29 tactic snippet I can paste.
Q1: the idiomatic way to reduce conOracle in `hc : c ∈ (conOracle M s).stepChildren` to the concrete branch decision, given nested dites + equation-binding dependent matches `match h : x with`.
Q2: is proving per-branch reduction EQUATIONS `conOracle M s = case2Decision M s ...` (via `unfold conOracle; split` on the equation goal, match at head of LHS) then `rw` into hc the right move? Will `split` handle `match h : x with` there? Will proof-irrelevance make RHS `hcap`/`⟨layer, by omega⟩` args match conOracle's internal ones (so the equation is provable by rfl/split)?
Q3: would replacing `match h : x with` by plain `match x with` make reduction trivial (e.g. `simp only [conOracle, dif_neg, ...]; split at hc` works)? If so, cleanest way to still recover `target ∈ occ` (for `1 ≤ target - cleared`) inside the branch WITHOUT the binder — e.g. `List.min?_mem` re-derived from a separate `hmin : ....min? = some target` obtained via `rcases`/`cases h : ...` at the proof site.
Keep it tight; prefer the approach most likely to just work.
</output_contract>
