Q1. Yes, Route N gives:
Let `dA = ringKrullDim (A ⧸ p)`, `dB = ringKrullDim (B ⧸ q)`, `q = p.comap φ`.
H3 on `B ⧸ q → A ⧸ p`: `dA = dB`.
H3 on `B → A` plus `dim B = s`: `ringKrullDim A = s`.
H1 on `B`: `(q.height : WithBot ℕ∞) + dB = (s : WithBot ℕ∞)`.
Assuming `(★) p.height = q.height`:
`(p.height : WithBot ℕ∞)+dA = (q.height : WithBot ℕ∞)+dB = s = ringKrullDim A`.
Conversely, GOAL plus H1 gives `p.height + dB = q.height + dB`; cancel finite `dB`.
Use `WithBot.add_natCast_cancel` if `dB` is exposed as a natural; otherwise lift through `ENat.add_left_injective_of_ne_top` / `ENat.add_right_injective_of_ne_top`. Not `WithTop.add_left_cancel` directly, because the equation is in `WithBot ℕ∞`.

Q2. (★) is not bounded from H1-H6.
Your inequality labels are reversed:
`height_A(p) ≤ height_B(q)` is bounded by H6: contract any chain below `p`; `strictMono_comap_of_isIntegral` keeps it strict below `q`.
The missing direction is `height_B(q) ≤ height_A(p)` for the fixed prime `p`.
H5 only lifts to some prime over `q`, not the chosen `p`; making the lift end at `p` is exactly going-down/fixed-top lifting, absent from inventory.

Q3. Reject the escape hatch as a 1-2 module proof.
Peeling on `I` via a monic element makes `A` integral over a smaller affine domain and immediately needs the same fixed-prime height transport.
Peeling on `P \ I` reduces to relative height in the interval `[I,P]`, i.e. the catenary split `height_R(P)=height_R(I)+height_A(p)`.
The flat one-variable tower only controls ambient polynomial height; it does not supply the missing interval split after quotienting.

Q4. (b) NEEDS-ONE-BRICK, but the brick is the unbounded core:
`height_le_comap_height_of_hasGoingDown_fixedTop` / equivalently `Algebra.HasGoingDown` for the Noether-normalization map from the normal polynomial base, giving `height_B(q) ≤ height_A(p)`.
Together with H6 it proves (★), then Route N closes.
That brick is the missing going-down/catenary content, so L4d is not bounded under the current mandate.