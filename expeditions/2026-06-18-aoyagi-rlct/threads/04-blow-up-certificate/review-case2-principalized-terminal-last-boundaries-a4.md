# Review - A4 Case 2 principalized terminal-last boundaries

Reviewed objects:

- `sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal`
- `sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal`
- `reproduction-case2-principalized-terminal-last-boundaries-a4.md`
- `statement-card-a4-principalized-terminal-last-boundaries.md`

Verdict: no blocking source/math or overclaiming issue found.

Both theorems are conjunction packages.  The actual-width package conjoins the
terminal-last original-row boundary and relabelled certificates with
finite-center value/divisibility/ideal facts.  The row-exhausted package
conjoins the terminal-last transported-prefix boundary with the same
finite-center facts, and does not add original-row equality or `(S+1,0)`
relabelled certificates.

Independent xhigh review (`Aquinas the 5th`) endorsed the names and statement
shape.  The reviewer emphasized the kill conditions: do not use the
row-exhausted package as an original-row theorem; do not attach `(S+1,0)`
relabelled certificates to it; do not drop `S+1=L`; and do not read the
finite-center clauses as chart coverage, Jacobian/normal-crossing data, RLCT
extraction, transition invariance, or terminal-product principalization.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
