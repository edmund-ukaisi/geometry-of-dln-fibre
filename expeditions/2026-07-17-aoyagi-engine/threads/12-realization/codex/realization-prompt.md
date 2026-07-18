<task>
Independent combinatorial adjudication. I am formalising a resolution-of-singularities recursion
(Aoyagi 2023, deep linear networks) and need an INDEPENDENT determination of one truth-value.
Do NOT trust my framing beyond the exact rules; compute from scratch.

SETUP. Fix an integer width vector M = (M^1, ..., M^{L+1}) (so L = len(M)-1 "layers"), M^i >= 1.
Running-min corank: M(S) = min(M^1, ..., M^S). A "divisor" is an integer vector T = (T^1,...,T^L)
with level t~(T) = min(T). The recursion builds a branching tree of states (S, J, divs), S in 1..L,
J >= 0, divs a multiset of divisors. Start (1, 0, {}). Rules at (S, J, divs), using
Mrun = M(S) = min(M^1..M^S) and MSp1 = min(M(S), M^{S+1}):

  * if S = L+1: LEAF (record divs). stop.
  * if J >= MSp1: ROLLOVER -> go to (S+1, 0, divs). (single child)
  * else let occ_above = { levels m of divisors in divs : J+1 <= m <= M(S)-1 }.
      - if occ_above nonempty: CASE 1. target = min(occ_above); pick f = the componentwise-<=
        LEAST divisor among those at level target (assume it exists -- it does here). This BRANCHES
        into two children:
          1(1): replace f by setTail(f, S, J) [set coords S..L of f to J], STAY at (S, J).
          1(2): ADD a new divisor setTail(f, S, J) [copy], keep f, go to (S, J+1).
      - else: CASE 2. ADD a new divisor c with head c^i = M(i+1) for i=1..S-1 (running-min
        envelope) and tail c^i = J for i=S..L; go to (S, J+1). (single child)
  setTail(T,S,J): coords 1..S-1 unchanged, coords S..L set to J.

The "t~=0 realized profile set" P(M) = { T : T is a divisor in SOME leaf, and min(T) = 0 }.

ADMISSIBLE SET. Adm(M) = weakly-decreasing tuples a=(a^1>=a^2>=...>=a^L=0) with a^i <= M(i+1) for
all i (equivalently a^1 <= min(M^1,M^2), a^j <= min(a^{j-1}, M^{j+1})). This is the paper's index set
of "strata"; the paper's read-off asserts (loosely) that the t~=0 leaf divisors enumerate Adm(M).

FACTS I have (integer-exact, both a from-scratch reimplementation AND a separately-validated
reference simulator agree): for the six instances M in {(2,2,2),(3,3,4),(2,2,2,2),(2,2,3,2),
(2,2,3,3,2),(3,2,4,2)} we get P(M) = Adm(M) exactly. I have NOT told you what happens at other M.

THE QUESTION (adjudicate independently): Is P(M) = Adm(M) for EVERY M? Test in particular
M = (3,3,4,2,3) (L=4). If P(M) != Adm(M) at some M, exhibit the exact discrepancy (which admissible
tuples are/aren't realized at t~=0) and give the sharpest structural characterization you can of the
realized set P(M) as a subset of Adm(M) -- name the mechanism. Also: is the Mval-minimizer (the
admissible tuple minimizing Mval(M,a) = (M^1-a^1)(M^2-a^1) + sum_{j=2}^{L}(a^{j-1}-a^j)(M^{j+1}-a^j))
always in P(M)?
</task>

<output_contract>
1. VERDICT: is P(M)=Adm(M) universal? yes/no, with the decisive instance if no.
2. For M=(3,3,4,2,3): P(M), Adm(M), and the exact set difference (compute it).
3. CHARACTERIZATION of P(M) inside Adm(M): the sharpest predicate on a in Adm you can prove/observe
   that decides a in P(M); NAME the mechanism (why certain admissible tuples fail).
4. MINIMIZER: is the Mval-minimizer always realized at t~=0? argument or counterexample.
5. Mark each claim [PROVED] / [COMPUTED] / [CONJECTURED]. Keep it tight.
</output_contract>

<grounding_rules>
- Compute exactly (write and run integer-only code if useful; the rules above are complete and
  self-contained). Do not floating-point anything.
- Use ONLY the rules as stated; if a rule is ambiguous, state the interpretation you took.
- Distinguish what you COMPUTED from what you CONJECTURE. Do not defer to my framing.
</grounding_rules>
