<task>
DLN/Aoyagi RLCT formalisation (Lean). I need to adjudicate whether a predicate-bridge is PROVABLE, and the cleanest route.

DEFINITIONS (all over the achiever path of M : Fin(L+1)→ℕ, i.e. widths M[0..L]):
- tStar M : an argmin over the admissible cone Adm(M) of Mval(M,·); tStar is Classical.choose (ANY argmin). Admissibility: T:Fin L→ℕ with (i) T[j] ≤ admBound(j) where admBound(0)=min(M0,M1), admBound(j)=M[j+1]; (ii) WEAKLY DECREASING (i≤j ⟹ T[j]≤T[i]); (iii) T[L-1]=0. Mval(M,T)=Σ_{j=0}^{L-1}(tPrev_j − T[j])·(M[j+1] − T[j]), tPrev_0=M0, tPrev_j=T[j-1].
- tach M : Fin(L+1)→ℕ = cons(M0, tStar M). So tach[0]=M0, tach[k+1]=tStar[k].
- Text(k): Text(0)=M0, Text(k+1)=tach[k]. So Text(1)=M0, Text(k+1)=tStar[k-1] for k≥1. (Text is weakly decreasing: Text(k+1)≤Text(k), inherited from tStar's weak-decrease + tach[0]=M0≥tStar[0].)
- Wext(k)=M[k]. deepRank = Text(L); deepRows = Wext(L-1) = M[L-1].
- InteriorDrop(M) := 0<M[L] ∧ ∃ p∈[1,L−1]: Text(p+1)<Text(p) ∧ (∀ b∈[p,L−1]: Text(b+1)<M[b]).
- NoInteriorBothDrop(M) := ∀ s∈[1,L−1]: ¬(Text(s+1)<Text(s) ∧ Text(s+1)<M[s]).
- BoundaryClean(M) := ¬InteriorDrop(M) ∧ deepRank = deepRows  (i.e. Text(L) = M[L−1]).

CLAIM TO ADJUDICATE: BoundaryClean(M) ⟹ NoInteriorBothDrop(M), for 2≤L, for the chosen tStar.

EVIDENCE: brute-forced widths 1..4, L≤5 (5456 M's, all argmins): ZERO clean-branch M violate NoInteriorBothDrop. At L=2 the mechanism is clear: the only interior s is s=L−1=1, and the both-drop's second conjunct Text(2)<M[1] is deepRank<deepRows, FALSE under clean (deepRank=deepRows). For L≥3 there are interior s<L−1, and empirically NONE both-drop either — but I don't have the structural reason for the SHALLOWER interior boundaries.

WHAT I OBSERVED about clean Text sequences (L≥3): they look like [M0, M0, …, then a single drop to r, then constant r, …, r] — Text drops AT MOST to its final value r=deepRank=deepRows and the both-drop never fires at interior boundaries. Conjecture: under clean, at any interior s where Text DROPS (Text(s+1)<Text(s)), the value Text(s+1) is ≥ M[s] (so the SECOND conjunct fails) — i.e. a drop only happens "down to the row-count floor". But I'm not certain this is the right invariant, nor that it's the argmin (tStar-specific) vs. holds for ALL admissible weakly-decreasing T.
</task>

<output_contract>
1. IS THE BRIDGE TRUE for the chosen tStar (yes/no/uncertain), and is it an ARGMIN-specific fact or does it hold for ANY admissible weakly-decreasing T with Text(L)=M[L−1]? (the latter would be a much cleaner Lean proof — pure admissibility arithmetic, no Mval-minimizer reasoning).
2. THE INVARIANT: state the precise structural invariant that makes NoInteriorBothDrop hold under clean, and a proof sketch. If it needs the argmin property, say exactly which minimality fact.
3. THE CHEAPEST LEAN ROUTE: (a) prove the bridge (give the key lemma chain), or (b) if argmin-specific and hard, recommend carrying hNo as a confirmed-true dischargeable precondition with the numeric evidence, or (c) flag a real residual if it can fail outside the tested grid.
4. THE TRAP: the single most likely way "BoundaryClean ⟹ NoInteriorBothDrop" is FALSE or my invariant is wrong (one concrete failure mode — e.g. a width pattern outside 1..4 / L≤5, or a tStar-ambiguity issue where a clean argmin coexists with an interior-both-drop argmin).
Keep under ~450 words. Mark inference vs. what you can verify from the definitions alone.
</output_contract>

<grounding_rules>
Reason from the definitions; you cannot run the Lean or my brute-force. Mark each claim (a) defensible inference / (b) guess. Do NOT rubber-stamp "it's true" — if the shallower-interior-boundary case has a plausible counterexample structure, construct it explicitly.
</grounding_rules>
