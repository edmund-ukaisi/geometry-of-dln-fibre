1. VERDICT: sound. OBSERVED: `M.submatrix id S` is exactly the selected-column minor; INFERENCE: `hS : Function.Injective S` is the right `b ≤ q` witness, with no sign issue because the determinant is squared.

2. VERDICT: sound. INFERENCE: singular `A` gives `det A = 0 ≤ det B` since `B` is PSD, and nonsingular PSD `A` is PD; conjugating by `A^{-1/2}` reduces to eigenvalues of `C` all at least `1`.

3. VERDICT: sound. INFERENCE: `xᵀ(PPᵀ)x = ‖xᵀP‖²` is correct, and injectivity of `S` makes the selected terms a genuine subset sum of nonnegative squares.

4. VERDICT: sound. INFERENCE: for positive-definite symmetric real `A`, the CFC square root is symmetric, invertible, squares to `A`, and its inverse satisfies `WAWᵀ = 1` and `|det W| = (sqrt det A)⁻¹`.

5. VERDICT: sound. OBSERVED/INFERENCE: the only note is naming scope: “general square real matrices” is fine because the PSD hypotheses force the relevant symmetry/Hermitian structure; no vacuity or overclaim beyond the expected vacuity when no injective selector exists.

OVERALL = PASS-WITH-NOTES