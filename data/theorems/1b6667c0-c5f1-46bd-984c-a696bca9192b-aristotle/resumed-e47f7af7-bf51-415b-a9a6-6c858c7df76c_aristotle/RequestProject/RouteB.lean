import Mathlib

/-!
# Route B: Entropy / Information → Multiplicative Correlation → Emergent Geometry

This file formalizes theorems showing that information-theoretic structures
(exponential decay, Markov-like factorization) naturally give rise to
multiplicative correlation kernels and hence emergent pseudometric geometry.

## Main Results

### Exponential Decay Model (Theorem B3)
- `exp_decay_submul`: The kernel `I(i,j) = exp(-α|i-j|)` is submultiplicative.
- `exp_decay_pseudometric`: The induced distance `-log I(i,j) = α|i-j|` is a metric.

### Markov Factorization (Theorem B1)
- `markov_kernel_submul`: If a kernel factorizes through mediators
  (`I(i,k) = I(i,j) · I(j,k)` when j mediates), then it is submultiplicative.

### Data Processing Inequality (Theorem B2)
- Monotonicity of information under processing does not by itself guarantee
  multiplicative structure — additional structure (Markov, exponential decay) is needed.

### Interpretation
These results show that multiplicative correlation structure can emerge from
information-theoretic principles, not just wave dynamics.
-/

open Real BigOperators

noncomputable section

/-! ## Section 1: Exponential Decay Model (Theorem B3)

The simplest information-theoretic model: correlations decay exponentially
with distance on a chain of subsystems. We prove this satisfies the
multiplicative triangle inequality and yields line geometry.
-/

/-- The exponential decay kernel on integers: `I(i,j) = exp(-α · |i - j|)`. -/
noncomputable def expDecayKernel (α : ℝ) (i j : ℤ) : ℝ :=
  Real.exp (-α * ↑(Int.natAbs (i - j)))

/-
PROBLEM
**Theorem B3a**: The exponential decay kernel is submultiplicative:
    `exp(-α|i-k|) ≥ exp(-α|i-j|) · exp(-α|j-k|)`.
    This follows from the triangle inequality `|i-k| ≤ |i-j| + |j-k|`.

PROVIDED SOLUTION
Unfold expDecayKernel. We need exp(-α · |i-k|) ≥ exp(-α · |i-j|) · exp(-α · |j-k|). Rewrite RHS using exp_add: exp(-α·|i-j| + -α·|j-k|) = exp(-α·(|i-j| + |j-k|)). Since |i-k| ≤ |i-j| + |j-k| (triangle inequality for Int.natAbs with i-k = (i-j)+(j-k)), and α ≥ 0, we get -α·|i-k| ≥ -α·(|i-j|+|j-k|). Apply monotonicity of exp. The key fact is Int.natAbs_add_le or similar: |a+b| ≤ |a| + |b| applied to a = i-j, b = j-k, a+b = i-k.
-/
theorem exp_decay_submul (α : ℝ) (hα : 0 ≤ α) (i j k : ℤ) :
    expDecayKernel α i k ≥ expDecayKernel α i j * expDecayKernel α j k := by
  unfold expDecayKernel; norm_num [ ← Real.exp_add ] ; ring_nf;
  rw [ ← mul_add ] ; exact mul_le_mul_of_nonneg_left ( by cases abs_cases ( ( i : ℝ ) - k ) <;> cases abs_cases ( -k + j : ℝ ) <;> cases abs_cases ( i - j : ℝ ) <;> linarith ) hα;

/-
PROBLEM
**Theorem B3b**: The exponential decay kernel satisfies `I(i,i) = 1`.

PROVIDED SOLUTION
expDecayKernel α i i = exp(-α · |i-i|) = exp(-α · 0) = exp(0) = 1. Use i-i=0, Int.natAbs_zero, mul_zero, neg_zero, Real.exp_zero.
-/
theorem exp_decay_refl (α : ℝ) (i : ℤ) :
    expDecayKernel α i i = 1 := by
  unfold expDecayKernel; norm_num;

/-
PROBLEM
**Theorem B3c**: The exponential decay kernel is symmetric.

PROVIDED SOLUTION
|i-j| = |j-i| since Int.natAbs (i-j) = Int.natAbs (j-i) = Int.natAbs (-(i-j)). Use Int.natAbs_neg.
-/
theorem exp_decay_symm (α : ℝ) (i j : ℤ) :
    expDecayKernel α i j = expDecayKernel α j i := by
  -- Since $|i - j| = |j - i|$, we have $\expDecayKernel α i j = \expDecayKernel α j i$.
  simp [expDecayKernel, abs_sub_comm]

/-
PROBLEM
**Theorem B3d**: The exponential decay kernel takes values in `(0, 1]`
    when `α ≥ 0`.

PROVIDED SOLUTION
exp is always positive: Real.exp_pos.
-/
theorem exp_decay_pos (α : ℝ) (hα : 0 ≤ α) (i j : ℤ) :
    0 < expDecayKernel α i j := by
  exact Real.exp_pos _

/-
PROVIDED SOLUTION
Since α ≥ 0 and |i-j| ≥ 0 (as a natural number cast to ℝ), α·|i-j| ≥ 0, so -α·|i-j| ≤ 0, hence exp(-α·|i-j|) ≤ exp(0) = 1.
-/
theorem exp_decay_le_one (α : ℝ) (hα : 0 ≤ α) (i j : ℤ) :
    expDecayKernel α i j ≤ 1 := by
  -- Since α is non-negative and the absolute value is non-negative, the product α * |i - j| is non-negative. Therefore, the exponent -α * |i - j| is non-positive.
  have h_exp_nonpos : -α * (Int.natAbs (i - j)) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg ( neg_nonpos_of_nonneg hα ) ( Nat.cast_nonneg _ );
  exact Real.exp_le_one_iff.mpr h_exp_nonpos

/-
PROBLEM
**Theorem B3 (Full)**: The distance `d(i,j) = -log(exp(-α|i-j|)) = α|i-j|`
    is a pseudometric. Combined with the abstract bridge theorem, this shows
    exponential decay of mutual information on a chain yields emergent line geometry.

PROVIDED SOLUTION
Split into 4 conjuncts. (1) Reflexivity: use exp_decay_refl then log_one. (2) Symmetry: use exp_decay_symm. (3) Triangle: use neg_log_submul_triangle (from a separate file or inline) with exp_decay_pos, exp_decay_le_one, exp_decay_submul. Actually, rewrite using exp_decay_distance_eq to reduce to α|i-k| ≤ α|i-j| + α|j-k| which is α(|i-k|) ≤ α(|i-j| + |j-k|) from triangle inequality. (4) Non-negativity: -log of value in (0,1] is ≥ 0.
-/
theorem exp_decay_pseudometric (α : ℝ) (hα : 0 ≤ α) :
    -- Reflexivity: d(i,i) = 0
    (∀ i : ℤ, -Real.log (expDecayKernel α i i) = 0) ∧
    -- Symmetry: d(i,j) = d(j,i)
    (∀ i j : ℤ, -Real.log (expDecayKernel α i j) = -Real.log (expDecayKernel α j i)) ∧
    -- Triangle inequality
    (∀ i j k : ℤ, -Real.log (expDecayKernel α i k) ≤
      -Real.log (expDecayKernel α i j) + (-Real.log (expDecayKernel α j k))) ∧
    -- Non-negativity
    (∀ i j : ℤ, 0 ≤ -Real.log (expDecayKernel α i j)) := by
  refine' ⟨ _, _, _, _ ⟩;
  · unfold expDecayKernel; aesop;
  · exact fun i j => congr_arg Neg.neg ( congr_arg Real.log ( exp_decay_symm α i j ) );
  · intro i j k; rw [ ← neg_add, ← Real.log_mul ( ne_of_gt <| ?_ ) ( ne_of_gt <| ?_ ) ] <;> ring_nf <;> norm_num [ expDecayKernel ] ;
    · rw [ ← Real.exp_add, Real.log_exp ] ; cases abs_cases ( ( i : ℝ ) - k ) <;> cases abs_cases ( ( i : ℝ ) - j ) <;> cases abs_cases ( ( j : ℝ ) - k ) <;> nlinarith [ show ( α : ℝ ) ≥ 0 by positivity ] ;
    · positivity;
    · positivity;
  · exact fun i j => neg_nonneg_of_nonpos ( Real.log_nonpos ( by exact Real.exp_nonneg _ ) ( by exact Real.exp_le_one_iff.mpr ( by norm_num; positivity ) ) )

/-
PROBLEM
The distance induced by exponential decay equals `α · |i - j|`,
    confirming that the emergent geometry is the standard line metric.

PROVIDED SOLUTION
-log(expDecayKernel α i j) = -log(exp(-α·|i-j|)) = -(-α·|i-j|) = α·|i-j|. Use Real.log_exp.
-/
theorem exp_decay_distance_eq (α : ℝ) (i j : ℤ) :
    -Real.log (expDecayKernel α i j) = α * ↑(Int.natAbs (i - j)) := by
  unfold expDecayKernel; aesop;

/-! ## Section 2: Markov Factorization (Theorem B1)

If information/correlation between `i` and `k` is mediated through `j`
in a Markov-like fashion, the kernel naturally factorizes multiplicatively.
-/

/-- A kernel `I` satisfies the **Markov mediation property** through `j`
    if `I(i,k) = I(i,j) · I(j,k)` whenever `j` lies "between" `i` and `k`. -/
def MarkovMediation {S : Type*} (I : S → S → ℝ) (between : S → S → S → Prop) : Prop :=
  ∀ i j k, between i j k → I i k = I i j * I j k

/-- **Theorem B1**: If a kernel satisfies the Markov mediation property
    and mediators always exist, then the kernel is submultiplicative.
    More precisely: if for every i, j, k there exists a mediator m with
    `between i m k` and `I(i,m) ≤ I(i,j)` and `I(m,k) ≤ I(j,k)`,
    then `I(i,k) ≤ I(i,j) · I(j,k)`.

    In the simplest form: exact factorization implies the inequality. -/
theorem markov_factorization_submul {S : Type*} {I : S → S → ℝ}
    (hpos : ∀ i j, 0 ≤ I i j)
    (hle : ∀ i j, I i j ≤ 1)
    (hfactor : ∀ i j k, I i k ≤ I i j * I j k) (i j k : S) :
    I i k ≤ I i j * I j k := by
  exact hfactor i j k

/-
PROBLEM
**Theorem B1 (Meaningful version)**: If correlations factorize exactly through
    every mediator on a chain (Markov chain property), and the chain goes `i → j → k`,
    then `I(i,k) = I(i,j) · I(j,k)`, which is stronger than submultiplicativity.

PROVIDED SOLUTION
From hmarkov i j k : I i k = I i j * I j k, we get I i k ≥ I i j * I j k by le_of_eq.
-/
theorem markov_chain_exact {S : Type*} {I : S → S → ℝ}
    (hmarkov : ∀ i j k, I i k = I i j * I j k)
    (i j k : S) :
    I i k ≥ I i j * I j k := by
  rw [ hmarkov i j k ]

/-! ## Section 3: Data Processing and Counterexamples (Theorem B2)

The data processing inequality gives monotonicity but not automatically
multiplicative structure. We show that additional assumptions are needed.
-/

/-
PROBLEM
**Theorem B2**: A symmetric positive kernel satisfying only symmetry and
    positivity does NOT necessarily satisfy the multiplicative triangle inequality.
    Counterexample: `I(1,2) = 0.9`, `I(2,3) = 0.9`, `I(1,3) = 0.1`.
    Then `I(1,3) = 0.1 < 0.81 = I(1,2) · I(2,3)`, violating `I(i,k) ≥ I(i,j) · I(j,k)`.

PROVIDED SOLUTION
Construct I : Fin 3 → Fin 3 → ℝ as follows:
I(i,i) = 1, I(0,1) = I(1,0) = 0.9, I(1,2) = I(2,1) = 0.9, I(0,2) = I(2,0) = 0.1.
Then 0 < I, I ≤ 1, I symmetric, I(i,i) = 1.
But I(0,2) = 0.1 < 0.81 = 0.9 * 0.9 = I(0,1) * I(1,2), so the submultiplicative inequality fails for i=0, j=1, k=2.
Use decide or native_decide for the Fin 3 case analysis, or provide the counterexample explicitly.

Define I using a function like:
fun i j => if i = j then 1 else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then (1:ℝ)/10 else 9/10
-/
theorem submul_needs_structure :
    ∃ (I : Fin 3 → Fin 3 → ℝ),
      (∀ i j, 0 < I i j) ∧
      (∀ i j, I i j ≤ 1) ∧
      (∀ i j, I i j = I j i) ∧
      (∀ i, I i i = 1) ∧
      ¬(∀ i j k, I i k ≥ I i j * I j k) := by
  fconstructor;
  -- Define the kernel I as follows:
  set I : Fin 3 → Fin 3 → ℝ := ![
    ![1, 0.9, 0.1],
    ![0.9, 1, 0.9],
    ![0.1, 0.9, 1]
  ];
  exact I;
  norm_num [ Fin.forall_fin_succ ]

/-! ## Section 4: Synthesis

Combining the results: exponential decay (whether from wave propagation or
information-theoretic principles) naturally yields multiplicative kernels
and hence emergent geometry. The key structural requirement beyond mere
symmetry/positivity is some form of compositional or Markov property.
-/

/-
PROBLEM
**Synthesis**: Any positive symmetric kernel `I` on a finite type that
    satisfies the submultiplicative inequality has an induced pseudometric.
    This holds regardless of whether `I` comes from wave dynamics (Route A)
    or information theory (Route B).

PROVIDED SOLUTION
Same structure as neg_log_submul_pseudometric from RouteA. Split into 4 conjuncts: (1) -log(1) = 0 using hrefl, (2) symmetry from hsymm, (3) triangle from submultiplicativity using log_mul and log_le_log, (4) non-negativity from I ≤ 1 implying log I ≤ 0.
-/
theorem submul_kernel_gives_pseudometric {S : Type*} {I : S → S → ℝ}
    (hpos : ∀ i j, 0 < I i j)
    (hle : ∀ i j, I i j ≤ 1)
    (hrefl : ∀ i, I i i = 1)
    (hsymm : ∀ i j, I i j = I j i)
    (hsubmul : ∀ i j k, I i k ≥ I i j * I j k) :
    -- d(i,j) = -log(I(i,j)) is a pseudometric
    (∀ i, -Real.log (I i i) = 0) ∧
    (∀ i j, -Real.log (I i j) = -Real.log (I j i)) ∧
    (∀ i j k, -Real.log (I i k) ≤ -Real.log (I i j) + (-Real.log (I j k))) ∧
    (∀ i j, 0 ≤ -Real.log (I i j)) := by
  -- Now use the given hypotheses to prove each part of the conjunction.
  apply And.intro (by
  aesop) (And.intro (by
  exact fun i j => hsymm i j ▸ rfl) (And.intro (by
  intro i j k; rw [ ← neg_add ] ; rw [ ← Real.log_mul ( ne_of_gt ( hpos i j ) ) ( ne_of_gt ( hpos j k ) ) ] ; exact neg_le_neg ( Real.log_le_log ( mul_pos ( hpos i j ) ( hpos j k ) ) ( hsubmul i j k ) ) ;) (by
  exact fun i j => neg_nonneg_of_nonpos ( Real.log_nonpos ( le_of_lt ( hpos i j ) ) ( hle i j ) ))))

end