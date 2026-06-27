<task>
I am formalising in Lean 4 + Mathlib (v4.29) a "germ comparability" atom for a deep-linear-network
RLCT computation. Design-review the PRECISE Lean STATEMENT (not the proof) of an abstract
matrix-algebra lemma before I transcribe it, so it is (a) PROVABLE, (b) exactly what the downstream
consumer needs, (c) not over-claiming.

## The mathematics (verified by an independent symbolic/numeric expedition, "S5c cert")

Setting: a 2-layer (L=2) reduced-core chain. Layers s=0,1. Each layer block-decomposes (block-LDU) as
`C_s = [[a_s, Y_s],[Z_s, T_s]]` with `a_s` an r×r pivot (-> I_r at the deepest point), and the per-layer
"Schur complement" `S_s = T_s - Z_s * a_s^{-1} * Y_s` (M×M core block). The GLOBAL Schur complement of
the product `C_0*C_1` reduces, by an EXACT block-LDU middle-factor identity, to:

    R = S_0 * W * S_1,     W = I_M - Z_1 * A^{-1} * Y_0,     A = a_0*a_1 + Y_0*Z_1   (global product pivot)

`W -> I_M` at the deepest point. The product of per-layer Schur cores is `PiS = S_0 * S_1`. So:

    R - PiS = S_0 * (W - I_M) * S_1 = - S_0 * (Z_1 * A^{-1} * Y_0) * S_1.

Germ orders at the deepest point (all deviations -> 0 with scale eps): `S_s = O(eps)`, `PiS = O(eps^2)`,
`W - I = O(eps^2)`, so `R - PiS = O(eps^4)` -- STRICTLY higher order than `PiS = O(eps^2)`. The off-pivot
data `Y_0, Z_1` are each `O(eps)` and are controlled by the "regular energy" `sumE2` near the deepest pt.

KEY SUBTLETY (a counterexample the cert found): the NAIVE two-sided box ratio `sum|R|^2 ~ sum|PiS|^2` is
FALSE for M>1 off-germ (e.g. `S_0=eps*E_12, S_1=eps*E_21` makes `PiS=eps^2 E_11 != 0` but `W[1,1]=0` can
force `R=0`). So the comparability must be a GERM/in-sum statement, NOT a uniform box ratio:

    |sum|R|^2 - sum|PiS|^2| <= C * sumE2    on a neighborhood Nhds(0)   (one-sided in-sum, charged to sumE2)

This survives the rank-deficient slice because there sumE2 is bounded below too.

## What the downstream consumer ACTUALLY uses

In a separate file, a theorem `hproducer` needs, for each w in some Nhds(deepest point), with
`Rcore = P11 - P10*inv(P00)*P01` (the global product's Schur core, P00 the invertible pivot block) and
`coreF = |PiS|^2` (a concrete real >= 0):

    (d)  sum_ij (Rcore i j)^2  <=  gamma2 * coreF
    (e)  coreF  <=  gamma1 * sum_ij (Rcore i j)^2

i.e. a TWO-SIDED MULTIPLICATIVE comparability with positive constants gamma1,gamma2. But per the cert
this clean two-sided ratio is FALSE off-germ. The honest objects are: the EXACT identity `R = S0*W*S1`,
and the in-sum germ bound `|sum|R|^2 - sum|PiS|^2| <= C * sumE2`.

## My questions (design-review the STATEMENT, in priority order)

1. Given the downstream consumer's conjuncts (d)/(e) are a two-sided multiplicative ratio that the cert
   says is FALSE off-germ but TRUE as a germ -- what is the RIGHT Lean statement for the atom
   `schur_core_germ_comparability`? Specifically should the atom deliver
   (A) the exact identity `R = S0*W*S1` PLUS the absolute-difference germ bound
       `exists U in Nhds 0, forall q in U, |sum|R q|^2 - sum|PiS q|^2| <= C * (sumE2 q)`,  OR
   (B) try to deliver (d)/(e) directly (and if so with what extra hypotheses to be TRUE -- is the
       multiplicative form recoverable on the germ from the absolute bound plus a lower bound
       sum|PiS|^2 <= K*sumE2 ...)?
   I lean to (A) as the honest atom. Confirm or correct, and state precisely how (A) is later turned
   into the consumer's (d)/(e) -- or whether (d)/(e) themselves must be RE-STATED as absolute/germ bounds.

2. For the abstract matrix-algebra core, the cleanest network-free Lean signature? I want pure `Matrix`
   over R, `Fin r`/`Fin M` indices, taking `a0 a1 : Matrix (Fin r) (Fin r) R`,
   `Y0 : Matrix (Fin r) (Fin M) R`, `Z1 : Matrix (Fin M) (Fin r) R`, `S0 S1 : Matrix (Fin M) (Fin M) R`,
   `A : Matrix (Fin r) (Fin r) R` with `[Invertible A]`, and a HYPOTHESIS pinning
   `R = S0*(1 - Z1*inv(A)*Y0)*S1` as the DEFINITION of R (so the identity is an input, not re-derived
   from a full block-LDU -- the block-LDU derivation is a separate heavier obligation). Then the
   deliverable is the remainder identity `R - S0*S1 = - S0*(Z1*inv(A)*Y0)*S1` (pure ring algebra,
   trivial) and a Frobenius bound `sum|R-S0S1|^2 <= (sum|S0|^2)*(sum|Z1*inv(A)*Y0|^2)*(sum|S1|^2)`
   (submultiplicativity). Is this the right factoring -- i.e. is the genuinely-load-bearing,
   transcribable content just (i) the trivial remainder ring identity + (ii) a Frobenius
   submultiplicative bound on the remainder, leaving the "charged to sumE2" step
   (`|Z1|,|Y0| <= sqrt(sumE2)`) to the consumer? Or should the atom carry the sumE2 charge?

3. Is statement (A) at risk of being VACUOUS / trivially true? The absolute bound
   `|sum|R|^2-sum|PiS|^2| <= C*sumE2` -- if C is huge, is it trivially satisfiable on a small enough
   neighborhood, saying nothing? How to state it as non-vacuous bedrock (C must be UNIFORM, independent
   of q on the nbhd; the bound for the SPECIFIC sumE2 the consumer controls). Suggest the guard.

4. Sanity-check the germ-order arithmetic: `R - PiS = -S0(Z1 inv(A) Y0)S1`. S0,S1,Y0,Z1 all O(eps),
   inv(A)=O(1) => O(eps^4); PiS = S0 S1 = O(eps^2); sumE2 ~ |Y0|^2+|Z1|^2 = O(eps^2). So
   `|sum|R|^2-sum|PiS|^2| <= 2|PiS||R-PiS| + |R-PiS|^2 = O(eps^6) <= C*sumE2 = C*O(eps^2)`. Is the charge
   to sumE2 (only O(eps^2)) CORRECT with a UNIFORM C on a nbhd (since eps^6/eps^2 = eps^4 -> 0 bounded)?
   yes/no + one-line reason.
</task>

<output_contract>
Four numbered sections answering 1-4, each <= 200 words. For Q1 give a clear verdict (A or B) and the
exact bridge to (d)/(e). For Q2 give a concrete Lean-flavoured signature sketch (types + hypotheses +
conclusion). For Q3 state the precise non-vacuity guard. For Q4 a yes/no + the one-line reason. End with
a single "BOTTOM LINE" sentence: the recommended atom statement.
</output_contract>

<grounding_rules>
Design-review of a STATEMENT, not a proof. Flag any place where my proposed factoring would make the
atom UNPROVABLE or UNSOUND. Distinguish "this is standard Mathlib" (fact) from "I'd guess this lemma
exists" (inference). Do NOT write the proof; focus on whether the statement is right.
</grounding_rules>
