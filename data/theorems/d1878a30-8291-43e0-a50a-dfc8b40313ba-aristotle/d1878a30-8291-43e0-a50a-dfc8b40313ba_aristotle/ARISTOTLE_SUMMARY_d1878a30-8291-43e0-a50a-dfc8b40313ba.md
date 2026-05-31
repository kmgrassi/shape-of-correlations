# Summary of changes for run d1878a30-8291-43e0-a50a-dfc8b40313ba
All 7 lemmas (plus a helper) have been formalized and proved in `RequestProject/NoisyTsirelsonCompletion.lean`. The file compiles cleanly with no `sorry` and uses only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Here is what was proved:

1. **`det_fin_four`** — Helper lemma expanding the determinant of any 4×4 real matrix into its 24-term Leibniz formula.

2. **`noisyTsirelsonGram_det`** (Lemma 1) — The determinant identity:
   `det(G) = (1 - y²)(1 - z²) - 4x²(1 - x²)`

3. **`psd_det_upper_bound`** (Lemma 2) — If G is PSD, then:
   `(1 - y²)(1 - z²) ≥ 4x²(1 - x²)`

4. **`min_overlap_upper_bound`** (Lemma 3) — For 0 ≤ x ≤ 1/√2 and G PSD:
   `min(|y|, |z|) ≤ √(1 - x²) - x`

5. **`noisyTsirelsonGram_achievable_psd`** (Lemma 4) — Setting y = z = √(1-x²) - x yields a PSD matrix (proved via a sum-of-squares decomposition of the quadratic form).

6. **`mu_constraints`** (Lemma 5) — μ-submultiplicativity implies `μx² ≤ |y|` and `μx² ≤ |z|`.

7. **`mu_upper_bound`** (Lemma 6) — Under PSD and μ-submultiplicativity: `μ ≤ (√(1-x²) - x)/x²`.

8. **`mu_achievable`** (Lemma 7) — Setting y = z = t = √(1-x²) - x and μ = min(1, t/x²) yields both PSD and μ-submultiplicativity (proved by finite case analysis over all Fin 4 triples).

The file uses the index convention 0 = A₀, 1 = A₁, 2 = B₀, 3 = B₁, consistent with the CHSH setup described in the request.