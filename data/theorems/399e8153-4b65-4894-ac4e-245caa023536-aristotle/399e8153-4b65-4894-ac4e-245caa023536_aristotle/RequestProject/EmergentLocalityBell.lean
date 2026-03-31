import Mathlib

open Real Finset BigOperators

/-!
# Emergent Locality and Bell Nonlocality: A Formal Framework

This file formalizes the relationship between emergent locality (from correlation-induced
geometry) and Bell nonlocality (from quantum entanglement), proving that they are compatible
and live at different conceptual levels.

## Overview of Assumptions

* **A (Fundamental degrees of freedom)**: A finite type `S` of fundamental nodes.
* **B (Global state ontology)**: A global, nonseparable state (not a product of local states).
* **C (Correlation kernel induces geometry)**: A symmetric positive kernel `I : S → S → ℝ`
  with `I(i,i) = 1` and multiplicative condition, inducing a pseudometric via `-log I`.
* **D (Emergent locality of couplings)**: Coupling `H(i,j) = exp(-d(i,j))` decays with distance.
* **E (Nonseparable preparation)**: The bipartite state is entangled (not separable across A|B).
* **F (Local measurements)**: Measurements act on local subsystems only.
* **G (No-signaling)**: Marginals are independent of distant measurement settings.

## Main Results

* `CorrelationKernel.dist_self`, `dist_comm`, `dist_nonneg`, `dist_triangle` —
  The emergent distance is a pseudometric (Assumption C).
* `chsh_algebraic_bound` — The core algebraic CHSH bound for product terms.
* `chsh_le_two_of_local` — Bell-local models satisfy CHSH ≤ 2 (Theorem 4).
* `toy_chsh_value_gt_two` — A toy model with emergent locality violates CHSH > 2 (Theorem 6).
* `toyNoSignaling` — The same toy model satisfies no-signaling (Theorem 7).
* `emergent_locality_not_implies_bell_locality` — Emergent locality ≠ Bell locality (Theorem 1).
* `metric_alone_insufficient` — Metric without entanglement gives no Bell violation (Theorem 5).
* `bell_nonseparability_compatible_with_emergent_locality` — The central compatibility
  theorem (Theorem 8).
-/

noncomputable section

-- ============================================================
-- PART I: Correlation Kernel and Emergent Geometry (Assumptions C, D)
-- ============================================================

/-- A correlation kernel on a type `S`: a symmetric positive function bounded in `(0, 1]`
    with diagonal entries equal to 1. -/
structure CorrelationKernel (S : Type*) where
  I : S → S → ℝ
  symm : ∀ i j, I i j = I j i
  pos : ∀ i j, 0 < I i j
  le_one : ∀ i j, I i j ≤ 1
  diag : ∀ i, I i i = 1

/-- The multiplicative correlation condition: `I(i,k) ≥ I(i,j) * I(j,k)`.
    This is the key assumption that makes the emergent distance satisfy the triangle
    inequality. -/
def CorrelationKernel.Multiplicative {S : Type*} (K : CorrelationKernel S) : Prop :=
  ∀ i j k, K.I i k ≥ K.I i j * K.I j k

/-- Emergent distance: `d(i,j) = -log(I(i,j))`. -/
def CorrelationKernel.dist {S : Type*} (K : CorrelationKernel S) (i j : S) : ℝ :=
  -Real.log (K.I i j)

/-
PROBLEM
The emergent distance is nonneg since `I(i,j) ≤ 1`.

PROVIDED SOLUTION
dist i j = -log(I(i,j)). Since 0 < I(i,j) ≤ 1, log(I(i,j)) ≤ 0, so -log(I(i,j)) ≥ 0. Use Real.log_nonpos and the hypotheses K.pos and K.le_one.
-/
theorem CorrelationKernel.dist_nonneg {S : Type*} (K : CorrelationKernel S) (i j : S) :
    0 ≤ K.dist i j := by
      exact neg_nonneg_of_nonpos ( Real.log_nonpos ( K.pos i j |> le_of_lt ) ( K.le_one i j ) )

/-
PROBLEM
`d(i,i) = 0` since `I(i,i) = 1`.

PROVIDED SOLUTION
dist i i = -log(I(i,i)) = -log(1) = 0. Use K.diag and Real.log_one.
-/
theorem CorrelationKernel.dist_self {S : Type*} (K : CorrelationKernel S) (i : S) :
    K.dist i i = 0 := by
      exact neg_eq_zero.mpr ( by rw [ K.diag i, Real.log_one ] )

/-
PROBLEM
`d(i,j) = d(j,i)` since `I` is symmetric.

PROVIDED SOLUTION
dist i j = -log(I(i,j)) = -log(I(j,i)) = dist j i. Use K.symm.
-/
theorem CorrelationKernel.dist_comm {S : Type*} (K : CorrelationKernel S) (i j : S) :
    K.dist i j = K.dist j i := by
      exact congr_arg Neg.neg ( congr_arg Real.log ( K.symm i j ) )

/-
PROBLEM
Triangle inequality: `d(i,k) ≤ d(i,j) + d(j,k)` when the multiplicative condition
    holds. Proof: from `I(i,k) ≥ I(i,j) * I(j,k)`, taking `-log` reverses the inequality
    and `-log(xy) = -log x + (- log y)`.

PROVIDED SOLUTION
From hK: I(i,k) ≥ I(i,j) * I(j,k). Since I values are positive, take -log of both sides (which reverses inequality): -log(I(i,k)) ≤ -log(I(i,j) * I(j,k)). Then use Real.log_mul (ne_of_gt (K.pos i j)) (ne_of_gt (K.pos j k)) to split: -log(I(i,j) * I(j,k)) = -log(I(i,j)) + (-log(I(j,k))). Key lemma: Real.log_le_log_of_le or just monotonicity of log (Real.log_le_log).
-/
theorem CorrelationKernel.dist_triangle {S : Type*} (K : CorrelationKernel S)
    (hK : K.Multiplicative) (i j k : S) :
    K.dist i k ≤ K.dist i j + K.dist j k := by
      unfold CorrelationKernel.dist at *;
      linarith [ Real.log_le_log ( mul_pos ( K.pos i j ) ( K.pos j k ) ) ( hK i j k ), Real.log_mul ( ne_of_gt ( K.pos i j ) ) ( ne_of_gt ( K.pos j k ) ) ]

/-- The coupling kernel `H(i,j) = exp(-d(i,j))`. This equals `I(i,j)` by construction. -/
def CorrelationKernel.coupling {S : Type*} (K : CorrelationKernel S) (i j : S) : ℝ :=
  Real.exp (-K.dist i j)

/-
PROBLEM
The coupling equals the correlation: `H(i,j) = I(i,j)`.
    Since `exp(-(-log(I))) = exp(log(I)) = I` for positive `I`.

PROVIDED SOLUTION
coupling i j = exp(-dist i j) = exp(-(-log(I(i,j)))) = exp(log(I(i,j))) = I(i,j). Use Real.exp_log (K.pos i j) after simplifying the double negation.
-/
theorem CorrelationKernel.coupling_eq {S : Type*} (K : CorrelationKernel S) (i j : S) :
    K.coupling i j = K.I i j := by
      unfold CorrelationKernel.coupling CorrelationKernel.dist
      simp [Real.exp_neg, Real.exp_log (K.pos i j)]

/-
PROBLEM
Coupling is monotone decreasing in distance (Assumption D):
    if `d(i,j) ≤ d(i',j')` then `H(i',j') ≤ H(i,j)`.

PROVIDED SOLUTION
coupling is exp(-d). Since exp is monotone and negation reverses order, if d(i,j) ≤ d(i',j') then -d(i',j') ≤ -d(i,j) and so exp(-d(i',j')) ≤ exp(-d(i,j)). Use Real.exp_le_exp or monotonicity of exp.
-/
theorem CorrelationKernel.coupling_antitone {S : Type*} (K : CorrelationKernel S)
    {i j i' j' : S} (h : K.dist i j ≤ K.dist i' j') :
    K.coupling i' j' ≤ K.coupling i j := by
      exact Real.exp_le_exp.2 ( neg_le_neg h )

-- ============================================================
-- PART II: CHSH / Bell Inequality Framework
-- ============================================================

/-- A Bell experiment: correlators `E(a,b)` for binary settings `a, b ∈ {false, true}`,
    bounded in `[-1, 1]`. -/
structure BellExperiment where
  E : Bool → Bool → ℝ
  E_abs_le_one : ∀ a b, |E a b| ≤ 1

/-- The CHSH combination: `S = E(0,0) + E(0,1) + E(1,0) - E(1,1)`. -/
def BellExperiment.chsh (B : BellExperiment) : ℝ :=
  B.E false false + B.E false true + B.E true false - B.E true true

/-
PROBLEM
Core algebraic CHSH bound: for `|a₀|, |a₁|, |b₀|, |b₁| ≤ 1`,
    `a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁ ≤ 2`.

    Proof sketch: rewrite as `a₀(b₀+b₁) + a₁(b₀-b₁)`, bound by
    `|b₀+b₁| + |b₀-b₁|`, then case-split on signs to get ≤ 2.

PROVIDED SOLUTION
From |a₀|, |a₁|, |b₀|, |b₁| ≤ 1, we have -1 ≤ a₀, a₁, b₀, b₁ ≤ 1. The expression equals a₀*(b₀+b₁) + a₁*(b₀-b₁). This is bounded by |a₀|*|b₀+b₁| + |a₁|*|b₀-b₁| ≤ |b₀+b₁| + |b₀-b₁|. Now |b₀+b₁| + |b₀-b₁| ≤ 2 when |b₀|, |b₁| ≤ 1 (by case analysis on signs). Try nlinarith with abs_le.mp ha₀, abs_le.mp ha₁, abs_le.mp hb₀, abs_le.mp hb₁, or polyrith after obtaining the individual bounds.
-/
theorem chsh_algebraic_bound {a₀ a₁ b₀ b₁ : ℝ}
    (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁ ≤ 2 := by
      cases abs_cases a₀ <;> cases abs_cases a₁ <;> cases abs_cases b₀ <;> cases abs_cases b₁ <;> push_cast [ * ] at * <;> nlinarith

/-
PROBLEM
Negative direction of the algebraic CHSH bound.

PROVIDED SOLUTION
Same as chsh_algebraic_bound but for the negation. Apply chsh_algebraic_bound with a₀ replaced by -a₀ and a₁ replaced by -a₁ (which preserve the absolute value bounds), or directly use nlinarith with the same bounds.
-/
theorem chsh_algebraic_bound_neg {a₀ a₁ b₀ b₁ : ℝ}
    (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    -(a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁) ≤ 2 := by
      cases abs_cases a₀ <;> cases abs_cases a₁ <;> cases abs_cases b₀ <;> cases abs_cases b₁ <;> push_cast [ * ] at * <;> nlinarith

/-- A Bell-local (hidden variable) decomposition of a Bell experiment.
    `E(a,b) = ∑ᵢ p(i) A(a,i) B(b,i)` with `A, B ∈ [-1,1]`, `p ≥ 0`, `∑ p = 1`. -/
structure BellLocalDecomp (B : BellExperiment) where
  n : ℕ
  p : Fin n → ℝ
  Aval : Bool → Fin n → ℝ
  Bval : Bool → Fin n → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum : ∑ i, p i = 1
  A_bound : ∀ a i, |Aval a i| ≤ 1
  B_bound : ∀ b i, |Bval b i| ≤ 1
  decomp : ∀ a b, B.E a b = ∑ i, p i * (Aval a i * Bval b i)

/-
PROBLEM
**Theorem 4 (Bell's Theorem for CHSH)**: Any Bell-local model satisfies CHSH ≤ 2.
    This formalizes that separable/local models obey the CHSH bound.

PROVIDED SOLUTION
Unfold chsh and use the decomp field to rewrite each E(a,b) as a sum. Then combine sums and apply chsh_algebraic_bound pointwise. Specifically: chsh = Σ p(i) * [A(0,i)*B(0,i) + A(0,i)*B(1,i) + A(1,i)*B(0,i) - A(1,i)*B(1,i)]. Each bracket ≤ 2 by chsh_algebraic_bound, so the whole sum ≤ Σ p(i) * 2 = 2. Use Finset.sum_le_sum and L.p_sum.
-/
theorem chsh_le_two_of_local (B : BellExperiment) (L : BellLocalDecomp B) :
    B.chsh ≤ 2 := by
      unfold BellExperiment.chsh;
      rw [ L.decomp ] at *;
      -- Apply the CHSH inequality to each term in the sum.
      have h_chsh : ∀ i, L.Aval false i * L.Bval false i + L.Aval false i * L.Bval true i + L.Aval true i * L.Bval false i - L.Aval true i * L.Bval true i ≤ 2 := by
        intro i; exact chsh_algebraic_bound ( by exact L.A_bound _ _ ) ( by exact L.A_bound _ _ ) ( by exact L.B_bound _ _ ) ( by exact L.B_bound _ _ ) ;
      rw [ L.decomp, L.decomp, L.decomp ];
      convert Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( h_chsh i ) ( L.p_nonneg i ) using 1 <;> norm_num [ mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib ] ; ring;
      rw [ ← Finset.sum_mul _ _ _, L.p_sum, one_mul ]

/-
PROBLEM
**Theorem 4 (other direction)**: Any Bell-local model satisfies -2 ≤ CHSH.

PROVIDED SOLUTION
Same structure as chsh_le_two_of_local but use chsh_algebraic_bound_neg. After rewriting chsh as sum, we get -2 ≤ Σ p(i) * bracket(i), which follows from each -bracket(i) ≤ 2 (i.e., bracket(i) ≥ -2) and the sum being a convex combination.
-/
theorem neg_two_le_chsh_of_local (B : BellExperiment) (L : BellLocalDecomp B) :
    -2 ≤ B.chsh := by
      -- Apply the algebraic CHSH bound negation to each term in the sum.
      have h_sum_bound : ∑ i ∈ Finset.univ, L.p i * (-(L.Aval false i * L.Bval false i + L.Aval false i * L.Bval true i + L.Aval true i * L.Bval false i - L.Aval true i * L.Bval true i)) ≤ ∑ i ∈ Finset.univ, L.p i * 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (L.p_nonneg i);
        grind +suggestions;
      simp_all +decide [ Finset.sum_add_distrib, mul_add, mul_sub, mul_comm, mul_left_comm ];
      simp_all +decide [ mul_comm, ← Finset.mul_sum _ _ _, BellExperiment.chsh ];
      linarith [ L.decomp true true, L.decomp false false, L.decomp false true, L.decomp true false, L.p_sum ]

/-- **Theorem 4 (absolute value form)**: |CHSH| ≤ 2 for Bell-local models. -/
theorem abs_chsh_le_two_of_local (B : BellExperiment) (L : BellLocalDecomp B) :
    |B.chsh| ≤ 2 := by
  rw [abs_le]
  exact ⟨by linarith [neg_two_le_chsh_of_local B L], chsh_le_two_of_local B L⟩

-- ============================================================
-- PART III: No-Signaling Framework (Assumption G)
-- ============================================================

/-- A no-signaling experiment: joint probabilities `P(x,y|a,b)` for binary outcomes
    and settings, satisfying normalization and the no-signaling conditions. -/
structure NoSignalingExperiment where
  /-- Joint probability `P(x, y | a, b)` -/
  P : Bool → Bool → Bool → Bool → ℝ
  /-- Probabilities are nonneg -/
  P_nonneg : ∀ x y a b, 0 ≤ P x y a b
  /-- Probabilities sum to 1 for each setting pair -/
  P_normalized : ∀ a b, P false false a b + P false true a b +
    P true false a b + P true true a b = 1
  /-- Alice's marginal is independent of Bob's setting -/
  no_signal_A : ∀ x a b₁ b₂,
    P x false a b₁ + P x true a b₁ = P x false a b₂ + P x true a b₂
  /-- Bob's marginal is independent of Alice's setting -/
  no_signal_B : ∀ y a₁ a₂ b,
    P false y a₁ b + P true y a₁ b = P false y a₂ b + P true y a₂ b

-- ============================================================
-- PART IV: Toy Model Construction (Theorems 3, 6, 7)
-- ============================================================

/-- The 4-node toy model correlation kernel.
    Nodes 0,1 = Alice subsystem, nodes 2,3 = Bob subsystem.
    All correlations are 1/2 (off-diagonal) and 1 (diagonal).
    This models a situation where all nodes are equally correlated. -/
def toyKernel : CorrelationKernel (Fin 4) where
  I := fun i j => if i = j then 1 else 1/2
  symm := by
    intro i j
    by_cases h : i = j <;> simp_all [eq_comm]
  pos := by intro i j; split_ifs <;> norm_num
  le_one := by intro i j; split_ifs <;> norm_num
  diag := by intro i; simp

/-
PROBLEM
The toy kernel satisfies the multiplicative condition:
    `I(i,k) ≥ I(i,j) * I(j,k)` for all nodes i, j, k.
    Since off-diagonal values are 1/2, we need 1/2 ≥ 1/2 * 1/2 = 1/4 (when all distinct)
    and 1 ≥ 1/2 * 1/2 (when i=k≠j), both of which hold.

PROVIDED SOLUTION
This is a finite check on Fin 4. The kernel is: I(i,j) = 1 if i=j, 1/2 otherwise. We need I(i,k) ≥ I(i,j)*I(j,k) for all i,j,k. Cases: (1) if i=k: I(i,k)=1 ≥ I(i,j)*I(j,k) which is either 1*1=1 (if i=j=k), 1/2*1/2=1/4 (if j≠i), or 1/2*1=1/2 (impossible since i=k≠j means I(j,k)=1/2 too). All cases: 1 ≥ 1/4 ✓. (2) if i≠k: I(i,k)=1/2. I(i,j)*I(j,k) is at most 1*1/2=1/2 (when j=i or j=k) or 1/2*1/2=1/4 (when j≠i and j≠k). So 1/2 ≥ 1/2 ✓ and 1/2 ≥ 1/4 ✓. Use decide or omega on Fin 4.
-/
theorem toyKernel_multiplicative : toyKernel.Multiplicative := by
  -- By definition of `toyKernel`, we know that its correlation kernel `I` satisfies the multiplicative condition.
  unfold CorrelationKernel.Multiplicative;
  unfold toyKernel; norm_num;
  intro i j k; split_ifs <;> norm_num;
  aesop

/-
PROBLEM
The toy Bell experiment: correlators from the Bell state `|Φ+⟩`.

    With optimal CHSH measurements:
    * `E(0,0) = E(0,1) = E(1,0) = 1/√2`
    * `E(1,1) = -1/√2`

    These values arise from the quantum mechanical prediction for the maximally
    entangled Bell state with appropriately chosen measurement bases.

PROVIDED SOLUTION
Need to show |1/√2| ≤ 1 and |-(1/√2)| ≤ 1. Since √2 ≥ 1 > 0, we have 1/√2 ≤ 1 and 1/√2 ≥ 0. So |1/√2| = 1/√2 ≤ 1 and |-(1/√2)| = 1/√2 ≤ 1. For cases on a, b: all four match cases give either 1/√2 or -(1/√2), both with absolute value ≤ 1. Use Real.one_le_sq_iff_one_le_abs or bound √2 ≥ 1 from sq_sqrt and 2 ≥ 1.
-/
def toyBellExperiment : BellExperiment where
  E := fun a b => match a, b with
    | false, false =>  1 / Real.sqrt 2
    | false, true  =>  1 / Real.sqrt 2
    | true,  false =>  1 / Real.sqrt 2
    | true,  true  => -(1 / Real.sqrt 2)
  E_abs_le_one := by
    intro a b; rcases a with ( _ | _ ) <;> rcases b with ( _ | _ ) <;> norm_num [ abs_le ] ;
    · exact inv_le_one_of_one_le₀ ( by rw [ abs_of_nonneg ] <;> exact Real.le_sqrt_of_sq_le ( by norm_num ) );
    · exact inv_le_one_of_one_le₀ ( by rw [ abs_of_nonneg ] <;> exact Real.le_sqrt_of_sq_le ( by norm_num ) );
    · exact inv_le_one_of_one_le₀ ( by rw [ abs_of_nonneg ] <;> exact Real.le_sqrt_of_sq_le ( by norm_num ) );
    · exact inv_le_one_of_one_le₀ ( by rw [ abs_of_nonneg ] <;> exact Real.le_sqrt_of_sq_le ( by norm_num ) )

/-
PROBLEM
The CHSH value of the toy model equals `4 / √2 = 2√2`.

PROVIDED SOLUTION
Unfold chsh and toyBellExperiment.E. chsh = 1/√2 + 1/√2 + 1/√2 - (-(1/√2)) = 1/√2 + 1/√2 + 1/√2 + 1/√2 = 4/√2. This is just ring arithmetic.
-/
theorem toy_chsh_eq : toyBellExperiment.chsh = 4 / Real.sqrt 2 := by
  unfold BellExperiment.chsh toyBellExperiment; ring;

/-
PROBLEM
**Theorem 6**: The CHSH value of the toy model exceeds 2, demonstrating Bell violation
    in a model with emergent locality.

PROVIDED SOLUTION
By toy_chsh_eq, chsh = 4/√2. We need 4/√2 > 2, i.e., 4 > 2*√2. Square both sides: 16 > 8, which is true. Or equivalently, 4/√2 = 2√2 and √2 > 1 (since 2 > 1). Use rw [toy_chsh_eq] then show 4/√2 > 2 using Real.sqrt_lt' or similar.
-/
theorem toy_chsh_value_gt_two : toyBellExperiment.chsh > 2 := by
  rw [ gt_iff_lt,toy_chsh_eq, lt_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-- The toy model joint probabilities.
    For the Bell state `|Φ+⟩` with correlator `E(a,b)`:
    * `P(x,y|a,b) = (1 + (-1)^{x⊕y} E(a,b)) / 4`
    Same-outcome probability is `(1 + E)/4`, different-outcome is `(1 - E)/4`.
    This gives uniform marginals: each individual outcome has probability 1/2. -/
def toyJointProb (x y a b : Bool) : ℝ :=
  let e := toyBellExperiment.E a b
  if x == y then (1 + e) / 4 else (1 - e) / 4

/-
PROBLEM
**Theorem 7**: The toy model satisfies no-signaling.
    The marginal probability for each party is 1/2 regardless of the other's setting.

PROVIDED SOLUTION
The joint probability is toyJointProb x y a b = if x == y then (1 + E(a,b))/4 else (1 - E(a,b))/4. For P_nonneg: since |E(a,b)| ≤ 1, both (1+E)/4 ≥ 0 and (1-E)/4 ≥ 0. For P_normalized: sum over x,y gives (1+E)/4 + (1-E)/4 + (1-E)/4 + (1+E)/4 = 1. For no_signal_A: P(x,false,a,b) + P(x,true,a,b). If x=false: (1+E)/4 + (1-E)/4 = 1/2, independent of b. If x=true: (1-E)/4 + (1+E)/4 = 1/2, independent of b. Similarly for no_signal_B. For each, unfold toyJointProb and the E values, then it reduces to showing 1/2 = 1/2 regardless of settings. The key is that for each fixed x, summing over y gives 1/2 regardless of a, b. Unfold toyJointProb, BEq instances for Bool, and simplify.
-/
def toyNoSignaling : NoSignalingExperiment where
  P := toyJointProb
  P_nonneg := by
    -- Since the absolute value of the E(a,b) values is at most 1, both (1 + E(a,b)) and (1 - E(a,b)) are non-negative.
    have h_abs : ∀ a b : Bool, |(toyBellExperiment.E a b)| ≤ 1 := by
      exact fun a b => toyBellExperiment.E_abs_le_one a b;
    intro x y a b; unfold toyJointProb; by_cases hx : x = y <;> norm_num [ hx, h_abs ] ;
    · linarith [ abs_le.mp ( h_abs a b ) ];
    · linarith [ abs_le.mp ( h_abs a b ) ]
  P_normalized := by
    intro a b; unfold toyJointProb toyBellExperiment
    cases a <;> cases b <;> simp <;> ring
  no_signal_A := by
    intro x a b₁ b₂; unfold toyJointProb toyBellExperiment
    cases x <;> cases a <;> cases b₁ <;> cases b₂ <;> simp <;> ring
  no_signal_B := by
    intro y a₁ a₂ b; unfold toyJointProb toyBellExperiment
    cases y <;> cases a₁ <;> cases a₂ <;> cases b <;> simp <;> ring

-- ============================================================
-- PART V: Main Theorems
-- ============================================================

/-- **Theorem 1**: Emergent locality does not imply Bell locality.
    We construct a model where couplings decay with emergent distance
    (i.e., locality holds at the coupling level) yet CHSH > 2
    (i.e., Bell factorization fails at the outcome level).

    This is one of the most important conceptual clarifications: local dynamics
    in emergent geometry is strictly weaker than Bell locality. -/
theorem emergent_locality_not_implies_bell_locality :
    ∃ (K : CorrelationKernel (Fin 4)) (B : BellExperiment),
      K.Multiplicative ∧ B.chsh > 2 :=
  ⟨toyKernel, toyBellExperiment, toyKernel_multiplicative, toy_chsh_value_gt_two⟩

/-- **Theorem 5**: A well-defined emergent metric without global nonseparability
    (i.e., with a Bell-local decomposition) cannot produce Bell violation.
    The metric structure is irrelevant — Bell locality alone forces CHSH ≤ 2.

    This shows that geometry alone is insufficient; global nonseparable state
    structure is necessary for Bell violation. -/
theorem metric_alone_insufficient {S : Type*} (_K : CorrelationKernel S)
    (_hK : _K.Multiplicative) (B : BellExperiment) (L : BellLocalDecomp B) :
    B.chsh ≤ 2 :=
  chsh_le_two_of_local B L

/-- **Theorem 8 (Central Compatibility Theorem)**: Bell-nonseparability is compatible
    with emergent locality.

    There exists a relational model in which:
    1. Geometry emerges from a valid correlation kernel with pseudometric,
    2. Couplings are local (monotone decreasing) in the emergent metric,
    3. Measurement statistics violate Bell factorization (CHSH > 2),
    4. No-signaling holds (marginals independent of distant settings).

    This is the cleanest theorem-level articulation of the result that
    emergent locality and Bell nonlocality are not contradictory, because
    they operate at different conceptual levels. -/
theorem bell_nonseparability_compatible_with_emergent_locality :
    ∃ (K : CorrelationKernel (Fin 4)) (B : BellExperiment) (NS : NoSignalingExperiment),
      K.Multiplicative ∧
      B.chsh > 2 ∧
      (∀ x a b₁ b₂,
        NS.P x false a b₁ + NS.P x true a b₁ =
        NS.P x false a b₂ + NS.P x true a b₂) ∧
      (∀ y a₁ a₂ b,
        NS.P false y a₁ b + NS.P true y a₁ b =
        NS.P false y a₂ b + NS.P true y a₂ b) :=
  ⟨toyKernel, toyBellExperiment, toyNoSignaling,
    toyKernel_multiplicative, toy_chsh_value_gt_two,
    toyNoSignaling.no_signal_A, toyNoSignaling.no_signal_B⟩

end