<task>
In a Lean4+Mathlib formalisation of Aoyagi's RLCT learning-coefficient theory for deep linear
networks, there is a VACUITY trap I need help pinning a non-vacuous statement around. Adjudicate the
GENUINE realizability statement an "achiever" needs.

SETTING (decl-grounded, these are the committed definitions):
- M : Fin (L+1) -> Nat   (reduced layer widths).
- T : Fin L -> Nat       (an "exponent vector").
- admBound M j := if j=0 then min (M 0)(M 1) else M (j+1).
- admPred M T := (forall j, T j <= admBound M j)
                 AND (forall i j, i<=j -> T j <= T i)        -- T weakly DECREASING
                 AND (forall j, j.val = L-1 -> T j = 0).      -- last entry 0
- Adm M := finite set of T with admPred.
- tPrev M T j := if j=0 then M 0 else T (j-1)   (over Z).
- Mval M T := sum_{j:Fin L} (tPrev M T j - T j) * (M (j+1) - T j)   (over Z, signed).
- minAdm := inf over Adm M of Mval.
- An ACHIEVER T* is a T* in Adm M with Mval M T* = minAdm.

SEPARATELY (the matrix side), over a field k, with d = M (widths):
- A "Tuple d" is a tuple of matrices A_s : Matrix (Fin d_{s+1}) (Fin d_s) k, s : Fin L.
- submult d A i j (i<=j) := A_{j-1} * ... * A_i  (the interval product), identity at i=j.
- rankFn d A i j := if i<=j then (submult d A i j).rank else 0.   -- the "rank pattern" of A
- RealizableRank d := Set.range (rankFn d).
- The "diagonal cascade" cascadeTuple d t (for t : Fin L -> Nat) sets A_s := partialId (d_{s+1})(d_s)(t_s),
  the rectangular partial-identity diag(1^{t_s},0). Its prefix sub-products are single partial-identities,
  so rankFn (cascadeTuple d t) 0 j = survivors (d_j)(d_0)(running-min of the t's over (0,j]) — a known lemma
  rankPattern_cascade_prefix.

THE VACUITY TRAP: there is a lemma
  cascadeTuple_mem_realizableRank : rankFn d (cascadeTuple d t) ∈ Set.range (rankFn d) := ⟨cascadeTuple d t, rfl⟩
This is f(x) ∈ range(f) — TRUE FOR ANY tuple, proves NOTHING about achievers. It has been mis-cited as
"realizability" three times. I need the GENUINE statement.

THE QUESTIONS (answer each crisply):

Q1. Define r* = "the achiever's prescribed rank pattern", derived from the ADMISSIBLE-exponent side
    (Adm/Mval/minAdm) INDEPENDENTLY of the cascade. What is the right mathematical definition of r* as a
    function of an achiever T* and M? It must NOT be defined as rankFn(cascadeTuple ...). Give the
    independent definition and its Lean decl-shape (type, inputs).

Q2. State the GENUINE realizability equality that ties the matrix-side cascade to the orbit-side achiever
    pattern: rankFn(cascadeTuple ... t*) = r* (an EQUALITY to the independently-defined target), not a
    membership. What exactly is t* (the cascade's per-block survivor counts) in terms of the achiever T*
    and M? Give the precise statement + Lean decl-shape. Especially the (0,j) row.

Q3. To prove the equality NON-VACUOUSLY general (not anchor-coincidental), one must decide-check a
    PROPERTY-BREAKING witness M whose achiever T* is structurally richer than trivial small cases. What
    structural features of (M, T*) make the equality's proof exercise its real content rather than passing
    by a degenerate coincidence? (Think about what makes the window-min / interior 2-index rank pattern
    non-trivial vs trivial.)
</task>

<output_contract>
- Q1: the independent r* definition (math + Lean decl-shape).
- Q2: the genuine equality (math + Lean decl-shape), with t* spelled in terms of T* and M.
- Q3: the structural features that make a witness non-degenerate; flag any feature that would make the
  general equality FALSE or only conditionally true.
- Mark each claim as FACT (forced by the defs) or INFERENCE (your reasoning).
</output_contract>

<grounding_rules>
- Ground in the committed definitions above; do not invent alternative conventions.
- If r* genuinely cannot be defined independently of the cascade (a real obstruction), say so explicitly.
- Do NOT assume the running ranks are monotone unless you derive it from admPred; state whether you derive it.
- Withhold nothing about edge cases. I have withheld my own tentative conclusion deliberately.
</grounding_rules>
