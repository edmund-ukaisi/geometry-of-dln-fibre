**Q1 — VERDICT: sound.**

Confident from the stated math: the localization-kills-`I` argument is valid. For `q = I`, uniqueness is genuinely free: if `J` is another minimal prime with `J ≤ I`, then minimality forces `J = I`.

Sharpest concern: the `T ⊄ q` step depends essentially on finiteness of the other minimal primes and on `q ≠ ⊤`. Noetherian gives finiteness; primality gives properness. The empty “other primes” case is fine: then `T = ⊤`, so choose `1 ∉ q`. `R ⧸ I` nontrivial follows from `I` being prime/proper.

**Q2 — VERDICT: honest reduction, conditional.**

Inference from the description: `e` is load-bearing but not circular. It supplies the geometric identification of the component quotient with an orbit-closure coordinate ring; smoothness then comes from independent orbit smoothness, the domain generic-point step, and C1.

It is stronger than minimally necessary: generic smoothness of `sweepFibreRing ⧸ I` would suffice. But a full `k`-algebra isomorphism to `orbitRing M` does not itself state `IsSmoothAt k I`, so it is not smuggling the conclusion unless `orbitRing M` or `OrbitSmooth` were defined/proved circularly, which cannot be checked without the source.

Caveat: the global claim is honest only if C2(a) means existence of such an `M` and `e` for every intended component. Without that existence theorem, the lemma is formally true but possibly unused.