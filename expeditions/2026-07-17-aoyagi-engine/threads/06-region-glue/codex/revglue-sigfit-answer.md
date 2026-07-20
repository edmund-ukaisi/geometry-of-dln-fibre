- Q1 — **FIT:** With `t := resolutionOf M`, all hypotheses and the conclusion unify exactly; implicit `{L}` and `{M}` are inferred from the explicit tree argument.

- Q2(a) — **FIT:** The eight conjuncts exactly match `hsrcM`, `hbdd`, `hdcInj`, `hrcInj`, `hdisj`, `hnull`, `hlp`, and `hlj`, in that order; a flat `obtain ⟨…⟩` works.

- Q2(b) — **FIT:** Every `l.divExp k` occurs through `finRange → map → append-left → flatMap`, and positive `l.resRank` occurs through `if_pos → singleton → append-right → flatMap`; these are exactly all exponent bounds required by the lemma.