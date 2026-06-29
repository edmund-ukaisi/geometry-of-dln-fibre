<task>
I am an adversarial fidelity reviewer auditing a Lean 4 + Mathlib re-home of commutative-algebra
lemmas. I need a decorrelated opinion on TWO fidelity judgments. Do NOT review the proofs (they
build sorry-free, axiom-clean); judge only whether NAMES + STATEMENTS + @[stacks] TAGS + the
"minimal hypotheses" claim are faithful.

Background math facts (please verify these against your own knowledge, do not take them on trust):
- Stacks 00OK (Lemma 10.112.4): "Suppose R ⊂ S and S integral over R. Then dim R = dim S."
- Stacks 00GU (Lemma 10.36.22): going-up — for R→S integral and primes p⊂p' in R with q over p,
  there is q'⊇q over p'.
- Stacks 00GT (Lemma 10.36.20): incomparability — for R→S integral, two distinct primes of S over
  the same prime of R are incomparable.

The Lean declarations under review (in namespace DLNFibre.Core.Dimension):

(1) HEADLINE, tagged @[stacks 00OK]:
    theorem ringKrullDim_eq_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
        (hf : f.IsIntegral) (hinj : Function.Injective f) :
        ringKrullDim S = ringKrullDim A

(2) tagged @[stacks 00GU]:
    theorem exists_ltSeries_comap_last_of_isIntegral [CommRing A] [CommRing S] [Algebra A S]
        [Algebra.IsIntegral A S] (hinj : Function.Injective (algebraMap A S))
        (p : LTSeries (PrimeSpectrum A)) :
        ∃ q : LTSeries (PrimeSpectrum S), q.length = p.length ∧
          comap (algebraMap A S) q.last = p.last
    (i.e. every strict prime chain in A lifts to a strict prime chain in S of the SAME length whose
    last term contracts back to the chain's last term)

(3) NOT tagged @[stacks] (only docstring-cites 00GT):
    theorem strictMono_comap_of_isIntegral [CommRing R] [CommRing S] [Algebra R S]
        [Algebra.IsIntegral R S] : StrictMono (comap (algebraMap R S))

(4) NOT tagged (called "one half of 00OK"):
    theorem ringKrullDim_le_of_integral [CommRing A] [CommRing S] {f : A →+* S}
        (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim A
    -- note: integrality only, NO injectivity hypothesis

(5) NOT tagged ("one half of 00OK"):
    theorem ringKrullDim_ge_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
        (hf : f.IsIntegral) (hinj : Function.Injective f) : ringKrullDim A ≤ ringKrullDim S

The "minimal hypotheses" claim made in the docstring/card:
  "injectivity is genuinely load-bearing for the dim A ≤ dim S half (lying-over over ⊥ needs
   comap ⊥ = ⊥, i.e. ker f = ⊥); the dim S ≤ dim A half (ringKrullDim_le_of_integral) drops
   injectivity entirely."

QUESTIONS:
Q1. Does the HEADLINE name+statement faithfully state Stacks 00OK? Is @[stacks 00OK] accurate?
Q2. Is @[stacks 00GU] on declaration (2) accurate — is "lift a strict prime chain to an equal-length
    strict prime chain" the right content to attach to the going-up tag 00GU, or is 00GU strictly
    the single-step lemma and the chain version a corollary (so the tag is at most "morally" right)?
Q3. Is the restraint correct: declarations (3),(4),(5) NOT tagged @[stacks], with (3) only
    docstring-citing 00GT? In particular: is it RIGHT not to tag (4)/(5) [each a one-directional
    inequality, i.e. half of 00OK], and is it RIGHT that strict-mono-comap (3) is a RESTATEMENT of
    incomparability 00GT rather than literally 00GT (so a docstring cite, not a @[stacks] tag, is
    the honest choice)? Could any be mis-tagged or under-tagged?
Q4. Is the "minimal hypotheses" claim ACCURATE? Specifically:
    (a) Is dim S ≤ dim A genuinely injectivity-free for an integral ring map? (Consider: comap is
        always defined; strict-mono of comap on Spec for an integral extension — does it need
        injectivity? Think about whether comap can identify two distinct primes of A as the same
        prime of S, lowering a chain.)
    (b) Does dim A ≤ dim S genuinely REQUIRE injectivity? Give the cleanest counterexample to the
        injectivity-free version (an integral, non-injective map where dim A > dim S).
</task>

<output_contract>
Four sections Q1..Q4. Each: a one-word verdict (FAITHFUL / ACCURATE / CORRECT-RESTRAINT, or
MISMATCH / OVERCLAIM / MISTAG), then 2-4 sentences of justification. For Q4(b) give an explicit
counterexample ring map. Be terse. End with a single overall line: PASS or the list of flags.
</output_contract>

<grounding_rules>
Distinguish what you know as mathematical FACT (Krull dimension theory, Stacks lemma statements)
from INFERENCE about the Lean encoding. Flag any place where you are guessing about Mathlib's
exact definitions (e.g. RingHom.IsIntegral, ringKrullDim as WithBot ℕ∞, LTSeries length
conventions) versus stating established commutative algebra. If a tag is "defensible but not
literal," say so rather than forcing a binary verdict.
</grounding_rules>
