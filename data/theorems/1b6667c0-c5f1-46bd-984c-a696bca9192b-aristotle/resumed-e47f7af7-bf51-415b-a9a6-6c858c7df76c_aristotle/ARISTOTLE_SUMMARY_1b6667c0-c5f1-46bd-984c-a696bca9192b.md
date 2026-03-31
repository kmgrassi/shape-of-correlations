# Summary of changes
Both Route A and Route B are fully formalized and verified in Lean 4 with Mathlib — no `sorry` remains, and all theorems depend only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Route A: Wave Dynamics → Multiplicative Correlation (`RequestProject/RouteA.lean`)

**Abstract Bridge Theorems:**
- `exp_neg_submul`: If `D` satisfies the triangle inequality, then `exp(-D)` is submultiplicative.
- `neg_log_submul_triangle`: Converse — if `I` is submultiplicative with `0 < I ≤ 1`, then `-log(I)` satisfies the triangle inequality.
- `exp_neg_log_id`: The transformations are inverses: `-log(exp(-D)) = D`.
- `neg_log_submul_pseudometric`: Submultiplicative kernel with symmetry/reflexivity induces a pseudometric.

**Walk-Based Path Models (Theorem A1):**
- `Walk` structure with `src`, `dst`, `weight`, `cost`, `concat`.
- `concat_weight`: Weight of concatenated walk = product of weights.
- `concat_cost`: Cost of concatenated walk = sum of costs.
- `walk_submul_exists`: Concatenating optimal walks yields submultiplicativity of maximal-path correlation.

**Main Synthesis (Theorem A2):**
- `action_to_geometry`: Any function `D` satisfying the triangle inequality gives `exp(-D)` submultiplicative and `-log(exp(-D)) = D` as a pseudometric. This is the formal statement: **path-based propagation ⇒ multiplicative kernel ⇒ emergent geometry**.

## Route B: Entropy/Information → Multiplicative Correlation (`RequestProject/RouteB.lean`)

**Exponential Decay Model (Theorem B3):**
- `expDecayKernel`: Defines `I(i,j) = exp(-α|i-j|)` on integers.
- `exp_decay_submul`: This kernel is submultiplicative.
- `exp_decay_refl`, `exp_decay_symm`, `exp_decay_pos`, `exp_decay_le_one`: Basic properties.
- `exp_decay_pseudometric`: The induced distance is a pseudometric.
- `exp_decay_distance_eq`: The emergent distance equals `α·|i-j|` (line geometry).

**Markov Factorization (Theorem B1):**
- `MarkovMediation`: Definition of Markov mediation property.
- `markov_factorization_submul`: Markov factorization implies submultiplicativity.
- `markov_chain_exact`: Exact Markov factorization gives equality (stronger than submultiplicativity).

**Data Processing / Counterexample (Theorem B2):**
- `submul_needs_structure`: Explicit counterexample on `Fin 3` showing that symmetry + positivity alone do NOT guarantee submultiplicativity. Uses the kernel `I(0,2) = 0.1 < 0.81 = I(0,1)·I(1,2)`.

**Synthesis:**
- `submul_kernel_gives_pseudometric`: Any submultiplicative kernel (from either route) induces a pseudometric via `-log`.

## Key Takeaway

The formalization rigorously establishes that **multiplicative correlation is not an arbitrary assumption** — it arises naturally from:
- **Route A**: Compositional propagation along paths (wave dynamics, least-action)
- **Route B**: Exponential decay / Markov structure (information theory)

And in both cases, `-log` of the correlation kernel yields an emergent pseudometric geometry. The counterexample (Theorem B2) shows that additional structure (Markov, path composition, exponential decay) is genuinely needed beyond mere symmetry and positivity.