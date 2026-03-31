# Summary of changes
## Completed: Both Routes Fully Formalized and Verified

All theorems across both routes are **fully proven** in Lean 4 with no `sorry` statements and only standard axioms.

### Route A: Wave Dynamics → Multiplicative Correlation (`RequestProject/RouteA.lean`)

**Abstract Bridge Theorems:**
- `exp_neg_submul`: If D satisfies the triangle inequality, then exp(-D) is submultiplicative: `exp(-D(i,k)) ≥ exp(-D(i,j)) · exp(-D(j,k))`.
- `exp_neg_log_id`: The transformations D ↦ exp(-D) and I ↦ -log(I) are inverses.
- `neg_log_submul_triangle`: If I is submultiplicative with 0 < I ≤ 1, then -log(I) satisfies the triangle inequality.
- `neg_log_submul_pseudometric`: Full pseudometric structure (reflexivity, symmetry, triangle inequality, non-negativity).

**Walk-Based Path Models (Theorem A1):**
- Formal `Walk` type with vertices, source, destination, weight, and cost.
- `Walk.concat_weight`: **The weight of a concatenated walk equals the product of weights** — the formal heart of "composition of propagation amplitudes is multiplicative."
- `Walk.concat_cost`: Cost of concatenated walks is additive.
- `walk_submul_exists`: Given walks i→j and j→k, there exists a walk i→k with weight = product of weights. This proves maximal-path correlation is submultiplicative.

**Main Synthesis (Theorem A2):**
- `action_to_geometry`: If D is a pseudometric (e.g., shortest-path distance), then exp(-D) is submultiplicative and -log(exp(-D)) = D recovers the geometry. **Path-based propagation ⇒ multiplicative kernel ⇒ emergent geometry.**

### Route B: Information / Entropy → Multiplicative Correlation (`RequestProject/RouteB.lean`)

**Exponential Decay Model (Theorem B3):**
- `exp_decay_submul`: The kernel I(i,j) = exp(-α|i-j|) is submultiplicative.
- `exp_decay_refl`, `exp_decay_symm`, `exp_decay_pos`, `exp_decay_le_one`: Basic properties.
- `exp_decay_distance_eq`: The induced distance is exactly α|i-j| — confirming emergent line geometry.
- `exp_decay_pseudometric`: Full pseudometric structure for the exponential decay model.

**Markov Factorization (Theorem B1):**
- `markov_chain_exact`: If correlations factorize exactly through every mediator (Markov chain), then submultiplicativity holds.

**Counterexample (Theorem B2):**
- `submul_needs_structure`: Explicit counterexample showing that a symmetric positive kernel with I(i,i)=1 does NOT automatically satisfy the submultiplicative inequality. (I(0,1)=I(1,2)=0.9, I(0,2)=0.1 violates it.) This proves additional structure (Markov, exponential decay, path composition) is genuinely needed.

**Synthesis:**
- `submul_kernel_gives_pseudometric`: Any positive symmetric submultiplicative kernel with I(i,i)=1 yields a pseudometric via -log — regardless of whether it comes from wave dynamics or information theory.

### Key Takeaway
The formalization proves that **multiplicative correlation structure, and therefore emergent geometry, arises naturally from compositional propagation or least-cost structure** rather than being assumed a priori. The counterexample shows this requires genuine structural assumptions — symmetry and positivity alone are insufficient.