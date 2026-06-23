<task>
I am deciding the cheapest provable ROUTE for an identity in a Lean RLCT formalisation. Derive from the
stated facts; distinguish FACT from INFERENCE; exact integer/rational arithmetic only.

OBJECTS (all exact, verified):
- Mval(M,T) = Σ_{j=0}^{L-1} (ρ_j − T_j)(M_{j+1} − T_j), ρ_0=M_0, ρ_j=T_{j-1}. [per-stratum codim, RLCT side]
- minAdm(M) = min over admissible T of Mval(M,T).  lambdaCore(M) = ½·minAdm(M).
- multSum(m) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1}·m_{uv}, the LR quadruple-sum geometric codim (N=L), m = the
  Kostant multiplicity array (2nd difference of the orbit rank pattern).
- cleanCore(c, m') = ¼(Σ_{i<c} q_i² − Σ_{k≤c} m'_k²), m' = the c+1 smallest widths of M (sorted), q = the
  balanced c-split of P=Σ m'_k. [Aoyagi's closed form]

ESTABLISHED FACTS (I have verified each exactly):
- FACT 1 (symbolic, sympy.expand, L=2,3,4): multSum(diff(r)) = Mval(M,T) IDENTICALLY in (M,T), where r is
  the explicit pattern r_{ij}=ρ_j+(M_i−ρ_i) (i≤j). A pure polynomial identity. [per-stratum]
- FACT 2 (A1, a PROVEN Lean theorem lambdaCore_eq_clean): lambdaCore(M) = cleanCore(c*, sortedSmallest M c*)
  for the GENUINE achiever's breakpoint count c* (an EXISTENTIAL — c* is the minimiser's, NOT min over c).
- FACT 3 (exhaustive, L=2..4): minAdm(M) = 2·cleanCore(c, sortedSmallest M c) for SOME c (the achiever's);
  the NAIVE min over c of 2·cleanCore is WRONG (goes to 0 / negative on width-spike M).
- FACT 4 (exhaustive): the geometric reading multSum = codim Ō holds only when diff(r) ≥ 0 (a genuine
  Kostant partition), i.e. on width-monotone M; on width-spike M the candidate r is not realizable.
</task>

<output_contract>
Q1. Chain the facts: is "minAdm(M) = geometric codim of the achiever orbit" PROVABLE via the route
    minAdm = Mval(T*) = multSum(T*) [FACT 1 at T=T*] and minAdm = 2·cleanCore [FACT 2/3], i.e. does #136
    route THROUGH A1's existing closed-form tie, needing NO fresh quadruple-sum=single-sum proof? Or is
    a direct multSum=cleanCore reconciliation still required? State which, and the exact logical chain.
Q2. Is multSum (quadruple-sum) = cleanCore (¼(Σq²−Σm²)) a DIRECT identity, or do they only agree at the
    achiever via Mval/minAdm? I.e. is the shortcut "multSum reduces to cleanCore" a per-stratum reduction
    of the two closed forms, or a value-coincidence at the minimiser? This decides whether fm3 proves a
    quadruple-sum↔single-sum reduction (heavy) or just composes FACT1 + FACT2 (light).
Q3. The cheapest Lean route for "minAdm = geometric codim": rank these — (a) compose FACT1 (per-stratum
    Mval=multSum, ring) + FACT2 (A1, done) at T=T*; (b) prove multSum=cleanCore directly; (c) other. Which
    is provably cheapest given FACT1 is a ring-identity and FACT2 is already a green theorem?
Q4. Any obstruction to route (a)? E.g. does evaluating FACT1's per-stratum identity at the achiever T*
    require knowing T* explicitly, or does the per-stratum identity (holding for ALL admissible T) plus
    "minAdm is attained at some admissible T*" suffice (so the geometric codim at the achiever = minAdm by
    the identity, no explicit T* needed)?
</output_contract>

<grounding_rules>
- Treat FACTs 1–4 as established (I verified them exactly). Reason about the ROUTE, not re-deriving them.
- FACT vs INFERENCE explicit. The naive min-over-c of cleanCore is WRONG (FACT 3) — don't use it.
- The geometric reading is scoped to realizable (width-monotone) M (FACT 4); the value chain (minAdm=...)
  is general.
</grounding_rules>
