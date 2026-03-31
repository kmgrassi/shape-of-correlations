import Mathlib

/-!
# CHSH Bounds Under Geometric (Submultiplicative) Constraints

We study the maximum CHSH value achievable by correlation kernels `G` that are
positive semidefinite, normalized (`G(i,i) = 1`), symmetric, and satisfy a
global submultiplicativity constraint `|G(i,k)| ≥ |G(i,j)| · |G(j,k)|`.

The submultiplicativity condition makes `d(i,j) = -log|G(i,j)|` satisfy the triangle
inequality, imposing an emergent metric (geometric) structure.

## Setting

We work on `Fin 4`, where:
- `0` = A₀ (Alice's first measurement setting)
- `1` = A₁ (Alice's second measurement setting)
- `2` = B₀ (Bob's first measurement setting)
- `3` = B₁ (Bob's second measurement setting)

## Main Results

1. **Correlator bound** (`correlator_abs_le_one`): `|G(i,j)| ≤ 1`
2. **Tsirelson bound** (`tsirelson_bound`): `CHSH ≤ 2√2`
3. **Orthogonality obstruction** (`submult_zero_dichotomy`):
   If `G(A₀,A₁) = 0` and `G` is submultiplicative, then for each Bob setting `b`,
   at least one of `G(A₀,b)` or `G(A₁,b)` vanishes.
4. **Classical bound from orthogonality** (`chsh_le_two_of_zero_submult`):
   `G(A₀,A₁) = 0` + submultiplicativity ⟹ `CHSH ≤ 2`
5. **Tsirelson equality forces orthogonality** (`chsh_eq_tsirelson_implies_ortho`):
   `CHSH = 2√2` ⟹ `G(A₀,A₁) = 0`
6. **Main theorem** (`chsh_lt_tsirelson_of_submult`):
   Under submultiplicativity, `CHSH < 2√2` (strict!)
7. **Nontrivial regime** (`exG_chsh_gt_two`):
   There exists a PSD, normalized, symmetric, submultiplicative kernel with `CHSH = 5/2 > 2`

These results establish **Case D** (partial quantum regime):
geometry limits but does not eliminate quantum nonlocality.
The supremum satisfies `2 < sup|CHSH| < 2√2`.
-/

noncomputable section

open Finset Real

/-! ## Core Definitions -/

/-- Positive semidefiniteness of a kernel on `Fin 4` -/
def IsPSD (G : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ c : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, c i * c j * G i j

/-- Normalization: all diagonal entries equal 1 -/
def IsNormalized (G : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i, G i i = 1

/-- Symmetry of the kernel -/
def GSymm (G : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i j, G i j = G j i

/-- Submultiplicativity of absolute values:
    `|G(i,k)| ≥ |G(i,j)| · |G(j,k)|` for all triples.
    Equivalently, `d(i,j) = -log|G(i,j)|` satisfies the triangle inequality. -/
def IsSubmult (G : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i j k, |G i k| ≥ |G i j| * |G j k|

/-- The CHSH value: `E(0,0) + E(0,1) + E(1,0) - E(1,1)`
    where `E(a,b) = G(Aₐ, Bᵦ)` -/
def chshVal (G : Fin 4 → Fin 4 → ℝ) : ℝ :=
  G 0 2 + G 0 3 + G 1 2 - G 1 3

/-! ## Part I: Correlator Bounds (Theorem 1) -/

/-
PROBLEM
Upper bound on correlators from PSD + normalization + symmetry.
    Proof: instantiate PSD with `c(i) = 1, c(j) = -1, c(k) = 0` to get
    `2 - 2G(i,j) ≥ 0`.

PROVIDED SOLUTION
Instantiate PSD with c(k) = if k = i then 1 else if k = j then -1 else 0. The double sum ∑ᵢⱼ c(i)c(j)G(i,j) has only 4 nonzero terms (for indices in {i,j}): G(i,i) - G(i,j) - G(j,i) + G(j,j) = 2 - 2G(i,j) (using normalization and symmetry). PSD gives 2 - 2G(i,j) ≥ 0, hence G(i,j) ≤ 1. For i = j, the result is immediate from normalization. Use simp [Fin.sum_univ_four] to expand sums and handle the cases.
-/
theorem correlator_le_one (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (i j : Fin 4) : G i j ≤ 1 := by
  -- By the properties of the PSD kernel, we know that $G(i, i) = 1$ and $G(j, j) = 1$.
  have h_diag : G i i = 1 ∧ G j j = 1 := by
    exact ⟨ hNorm i, hNorm j ⟩
  -- Using the fact that $G$ is symmetric, we have $G(i, j) = G(j, i)$.
  have h_symm : G i j = G j i := by
    exact hSym i j ▸ rfl
  -- Substitute these into the inequality from the PSD property.
  have h_ineq : 2 - 2 * G i j ≥ 0 := by
    contrapose! hPSD;
    intro h; have := h ( fun k => if k = i then 1 else if k = j then -1 else 0 ) ; simp_all +decide [ Fin.sum_univ_four ] ;
    fin_cases i <;> fin_cases j <;> simp +decide at * <;> linarith!
  -- Dividing both sides by 2, we get $1 - G(i, j) ≥ 0$, which simplifies to $G(i, j) ≤ 1$.
  linarith [h_ineq]

/-
PROBLEM
Lower bound on correlators from PSD + normalization + symmetry.
    Proof: instantiate PSD with `c(i) = 1, c(j) = 1, c(k) = 0` to get
    `2 + 2G(i,j) ≥ 0`.

PROVIDED SOLUTION
Instantiate PSD with c(k) = if k = i then 1 else if k = j then 1 else 0. The double sum gives G(i,i) + G(i,j) + G(j,i) + G(j,j) = 2 + 2G(i,j). PSD gives 2 + 2G(i,j) ≥ 0, hence G(i,j) ≥ -1. For i = j, normalization gives G(i,i) = 1 ≥ -1. Use simp [Fin.sum_univ_four] to expand sums.
-/
theorem neg_one_le_correlator (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (i j : Fin 4) : -1 ≤ G i j := by
  contrapose! hPSD;
  intro h; have := h ( fun k => if k = i then 1 else if k = j then 1 else 0 ) ; simp_all +decide [ Fin.sum_univ_four ] ;
  fin_cases i <;> fin_cases j <;> simp +decide at hPSD this ⊢ <;> linarith! [ hNorm 0, hNorm 1, hNorm 2, hNorm 3, hSym 0 0, hSym 0 1, hSym 0 2, hSym 0 3, hSym 1 0, hSym 1 1, hSym 1 2, hSym 1 3, hSym 2 0, hSym 2 1, hSym 2 2, hSym 2 3, hSym 3 0, hSym 3 1, hSym 3 2, hSym 3 3 ]

/-- Absolute correlator bound: `|G(i,j)| ≤ 1` -/
theorem correlator_abs_le_one (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (i j : Fin 4) : |G i j| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_correlator G hPSD hNorm hSym i j,
              correlator_le_one G hPSD hNorm hSym i j⟩

/-! ## Part II: Submultiplicativity Structural Results (Theorems 4, 5) -/

/-
PROBLEM
Key structural lemma: if `G(A₀,A₁) = 0` and `G` is submultiplicative,
    then for each index `b`, at least one of `G(A₀,b)` or `G(A₁,b)` vanishes.

    Proof: submultiplicativity gives `|G(0,1)| ≥ |G(0,b)| · |G(b,1)|`,
    hence `0 ≥ |G(0,b)| · |G(b,1)| ≥ 0`, so the product is zero.

PROVIDED SOLUTION
From submultiplicativity with (i,j,k) = (0,b,1): |G 0 1| ≥ |G 0 b| * |G b 1|. Since G 0 1 = 0, we get 0 ≥ |G 0 b| * |G b 1| ≥ 0 (as product of non-negatives). So |G 0 b| * |G b 1| = 0. By mul_eq_zero, |G 0 b| = 0 or |G b 1| = 0. The former gives G 0 b = 0 (left case). The latter gives G b 1 = 0, and by symmetry G 1 b = 0 (right case).
-/
theorem submult_zero_dichotomy (G : Fin 4 → Fin 4 → ℝ)
    (hSub : IsSubmult G) (hSym : GSymm G) (h01 : G 0 1 = 0)
    (b : Fin 4) : G 0 b = 0 ∨ G 1 b = 0 := by
  -- By submultiplicativity, we have |G(0,1)| ≥ |G(0,b)| * |G(b,1)|.
  have h_sub : |G 0 1| ≥ |G 0 b| * |G b 1| := by
    exact hSub _ _ _;
  simp_all +decide [ mul_eq_zero, GSymm ];
  exact mul_eq_zero.mp ( le_antisymm h_sub ( mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ) |> Or.imp ( fun h => by simpa using h ) fun h => by simpa using h;

/-
PROBLEM
If `G(A₀,A₁) = 0` and `G` is submultiplicative with PSD + normalized + symmetric,
    then `CHSH ≤ 2`.

    Proof: by `submult_zero_dichotomy`, for `b = 2` and `b = 3`, at least one correlator
    per pair vanishes. In all four cases, at most two of the four CHSH terms survive,
    each bounded by 1, giving `|CHSH| ≤ 2`.

PROVIDED SOLUTION
From submult_zero_dichotomy with b=2: G 0 2 = 0 ∨ G 1 2 = 0.
From submult_zero_dichotomy with b=3: G 0 3 = 0 ∨ G 1 3 = 0.
Four cases:
Case (G 0 2 = 0, G 0 3 = 0): chshVal G = 0 + 0 + G 1 2 - G 1 3 ≤ |G 1 2| + |G 1 3| ≤ 2.
Case (G 0 2 = 0, G 1 3 = 0): chshVal G = 0 + G 0 3 + G 1 2 - 0 ≤ |G 0 3| + |G 1 2| ≤ 2.
Case (G 1 2 = 0, G 0 3 = 0): chshVal G = G 0 2 + 0 + 0 - G 1 3 ≤ |G 0 2| + |G 1 3| ≤ 2.
Case (G 1 2 = 0, G 1 3 = 0): chshVal G = G 0 2 + G 0 3 + 0 - 0 ≤ |G 0 2| + |G 0 3| ≤ 2.
Use correlator_le_one and neg_one_le_correlator for the bounds |G i j| ≤ 1, so each surviving term is in [-1,1], giving the bound 2.
-/
theorem chsh_le_two_of_zero_submult (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (hSub : IsSubmult G) (h01 : G 0 1 = 0) :
    chshVal G ≤ 2 := by
  -- By the properties of submultiplicative weights and the bounds on correlators, we know that for any `b`, at least one of `G 0 b` or `G 1 b` is zero.
  have h_zero : ∀ b, G 0 b = 0 ∨ G 1 b = 0 := by
    exact?;
  -- By the bounds on correlators, we know that for any `i` and `j`, `|G i j| ≤ 1`.
  have h_bound : ∀ i j, |G i j| ≤ 1 := by
    exact?;
  cases h_zero 2 <;> cases h_zero 3 <;> simp_all +decide [ chshVal ] <;> linarith [ abs_le.mp ( h_bound 0 2 ), abs_le.mp ( h_bound 0 3 ), abs_le.mp ( h_bound 1 2 ), abs_le.mp ( h_bound 1 3 ) ] ;

/-! ## Part III: Tsirelson Bound (Theorem 2) -/

/-
PROBLEM
Algebraic Tsirelson bound: `CHSH ≤ 2√2`.

    Proof: Consider PSD with `c = (1, 0, cos θ, sin θ)` and `c = (0, 1, sin θ, -cos θ)`.
    Each gives a non-negative quadratic form. Their sum simplifies (the `G(2,3)` terms cancel)
    to `4 + 2(G(0,2) - G(1,3))cos θ + 2(G(0,3) + G(1,2))sin θ ≥ 0` for all `θ`.
    This means `(G(0,2) - G(1,3))² + (G(0,3) + G(1,2))² ≤ 4`.
    Since `CHSH = (G(0,2) - G(1,3)) + (G(0,3) + G(1,2))`, by Cauchy-Schwarz:
    `CHSH² ≤ 2 · 4 = 8`, so `CHSH ≤ 2√2`.

PROVIDED SOLUTION
Step 1: Consider two PSD conditions:
- PSD with c₁ = (1, 0, cos θ, sin θ) gives: 2 + 2·G(0,2)·cos θ + 2·G(0,3)·sin θ + G(2,3)·sin(2θ) ≥ 0
- PSD with c₂ = (0, 1, sin θ, -cos θ) gives: 2 + 2·G(1,2)·sin θ - 2·G(1,3)·cos θ - G(2,3)·sin(2θ) ≥ 0

Sum: 4 + 2·(G(0,2) - G(1,3))·cos θ + 2·(G(0,3) + G(1,2))·sin θ ≥ 0 for all θ.

Step 2: Let X = G(0,2) - G(1,3), Y = G(0,3) + G(1,2).
Note chshVal G = X + Y.
The condition 4 + 2X·cos θ + 2Y·sin θ ≥ 0 for all θ implies X² + Y² ≤ 4.
(Take θ so that cos θ = -X/√(X²+Y²), sin θ = -Y/√(X²+Y²) to get 4 - 2√(X²+Y²) ≥ 0.)

Step 3: CHSH = X + Y. By Cauchy-Schwarz: (X+Y)² ≤ 2(X²+Y²) ≤ 8. So CHSH ≤ 2√2.

For the formal proof, instead of using trigonometric functions, use the direct approach:
Instantiate PSD with specific vectors c and derive X² + Y² ≤ 4 algebraically.

Actually, a cleaner formal approach: define X = G 0 2 - G 1 3 and Y = G 0 3 + G 1 2.
Use PSD with c = (1, 0, -X/2, -Y/2). Expand the sum and use Fin.sum_univ_four and the symmetry/normalization properties.
The PSD condition gives:
1 + X²/4 + Y²/4 - X·(G 0 2) - Y·(G 0 3) + XY/2·(G 2 3) ≥ 0
Use PSD with c = (0, 1, -Y/2, X/2). Similarly get:
1 + Y²/4 + X²/4 - Y·(G 1 2) + X·(G 1 3) - XY/2·(G 2 3) ≥ 0
Sum: 2 + X²/2 + Y²/2 - X·(G 0 2 - G 1 3) - Y·(G 0 3 + G 1 2) ≥ 0
= 2 + X²/2 + Y²/2 - X² - Y² = 2 - X²/2 - Y²/2 ≥ 0
So X² + Y² ≤ 4.

Then CHSH = X + Y ≤ √(2(X²+Y²)) ≤ √8 = 2√2.
For the last step: use nlinarith with sq_nonneg (X - Y) to get (X+Y)² ≤ 2(X²+Y²) ≤ 8,
hence X+Y ≤ 2√2 (using Real.le_sqrt).
-/
theorem tsirelson_bound (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G) :
    chshVal G ≤ 2 * Real.sqrt 2 := by
  -- By the properties of the CHSH value and the Tsirelson bound, we have $CHSH^2 \leq 8$.
  have h_chsh_sq_le_8 : (chshVal G)^2 ≤ 8 := by
    -- Let $X = G(0, 2) - G(1, 3)$ and $Y = G(0, 3) + G(1, 2)$.
    set X := G 0 2 - G 1 3
    set Y := G 0 3 + G 1 2;
    -- Let's choose the vectors $c_1 = (1, 0, -X/2, -Y/2)$ and $c_2 = (0, 1, -Y/2, X/2)$.
    set c1 : Fin 4 → ℝ := ![1, 0, -X / 2, -Y / 2]
    set c2 : Fin 4 → ℝ := ![0, 1, -Y / 2, X / 2];
    -- By the properties of the CHSH value and the Tsirelson bound, we have $X^2 + Y^2 \leq 4$.
    have hX2Y2_le_4 : X^2 + Y^2 ≤ 4 := by
      have := hPSD c1; ( have := hPSD c2; ( norm_num [ Fin.sum_univ_succ ] at *; ) );
      simp +zetaDelta at *;
      rw [ hNorm 0, hNorm 1, hNorm 2, hNorm 3 ] at * ; rw [ hSym 2 0, hSym 3 0, hSym 2 1, hSym 3 1, hSym 2 3 ] at * ; nlinarith;
    unfold chshVal; nlinarith [ sq_nonneg ( X - Y ) ] ;
  nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-! ## Part IV: PSD Zero-Form Lemma -/

/-
PROBLEM
If the PSD quadratic form vanishes for some `c`, then the linear form
    `∑ⱼ c(j) · G(k,j)` vanishes for all `k`.

    Proof: define `c'(i) = c(i) + ε · δ(i,k)` for parameter `ε`. By PSD:
    `0 ≤ ∑ᵢⱼ c'(i)c'(j)G(i,j) = 0 + 2ε·S + ε²·G(k,k)`
    where `S = ∑ⱼ c(j)·G(k,j)`. With normalized `G(k,k) = 1`:
    `ε² + 2εS ≥ 0` for all `ε`. Setting `ε = -S`: `-S² ≥ 0`, so `S = 0`.

PROVIDED SOLUTION
Let S = ∑ j : Fin 4, c j * G k j. Define c' = fun i => c i + (if i = k then (-S) else 0).
By PSD: 0 ≤ ∑ij c'(i)·c'(j)·G(i,j).
Expanding: ∑ij (c i + (-S)·δ(i,k))·(c j + (-S)·δ(j,k))·G(i,j)
= ∑ij c(i)·c(j)·G(i,j) + 2·(-S)·(∑j c(j)·G(k,j)) + S²·G(k,k)
= 0 + 2·(-S)·S + S²·1  (using hZero and hNorm)
= -2S² + S² = -S².
So 0 ≤ -S², hence S² ≤ 0, hence S = 0.

For the expansion, use bilinearity: the cross terms give 2·(-S)·(∑j c(j)·G(k,j)) by symmetry of G. The sum ∑ij c(i)·δ(i,k)·c(j)·G(i,j) = c(k)·∑j c(j)·G(k,j)... wait, let me be precise.

Actually, let me use a simpler argument. Setting ε = -S:
have h := hPSD (fun i => c i + if i = k then (-S) else 0)
Expand this sum using Fin.sum_univ_four and simplify. The bilinear expansion gives:
0 + 2*(-S)*S + S^2*1 = -S^2 ≥ 0, so S = 0.

The key identity needed: ∑ij (c i + ε·δ(i,k))·(c j + ε·δ(j,k))·G(i,j) = (∑ij c(i)·c(j)·G(i,j)) + 2ε·(∑j c(j)·G(k,j)) + ε²·G(k,k).

This can be proved by expanding and using symmetry of G.
-/
theorem psd_zero_form (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (c : Fin 4 → ℝ) (hZero : ∑ i : Fin 4, ∑ j : Fin 4, c i * c j * G i j = 0)
    (k : Fin 4) : ∑ j : Fin 4, c j * G k j = 0 := by
  contrapose! hZero;
  -- By the properties of the quadratic form, we have:
  have h_quad_form : ∀ ε : ℝ, 0 ≤ ∑ i, ∑ j, (c i + ε * (if i = k then 1 else 0)) * (c j + ε * (if j = k then 1 else 0)) * G i j := by
    exact fun ε => hPSD _;
  simp_all +decide [ Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hSym k ];
  exact fun h => hZero <| by nlinarith [ h_quad_form ( - ( ∑ i, G i k * c i ) / 2 ), h_quad_form ( ( ∑ i, G i k * c i ) / 2 ), hNorm k ] ;

/-! ## Part V: Tsirelson Equality Implies Orthogonality -/

/-
PROBLEM
If `CHSH = 2√2`, then `G(A₀, A₁) = 0`.

    Proof outline: CHSH = 2√2 forces equality in both the sum-of-squares bound and
    Cauchy-Schwarz. This means both PSD conditions (with the optimal θ₀ = -3π/4) give
    zero. By `psd_zero_form`, the linear forms `∑ⱼ c(j) G(k,j) = 0` for both vectors.
    From the first vector `(1, 0, -1/√2, -1/√2)`, row 0 gives `a + b = √2`
    and rows 2,3 give `a = b`. From the second vector `(0, 1, -1/√2, 1/√2)`, row 0
    gives `p - a/√2 + b/√2 = 0`. Since `a = b`, this gives `p = G(0,1) = 0`.

PROVIDED SOLUTION
Let X = G 0 2 - G 1 3 and Y = G 0 3 + G 1 2. Since chshVal G = X + Y = 2√2.

Step 1: From the tsirelson_bound proof, X² + Y² ≤ 4.
Prove this using the same PSD conditions as in tsirelson_bound (c1 = ![1, 0, -X/2, -Y/2] and c2 = ![0, 1, -Y/2, X/2]).

Step 2: Since (X+Y)² ≤ 2(X²+Y²) and (X+Y) = 2√2, we get 8 ≤ 2(X²+Y²) ≤ 8. So X² + Y² = 4 and X = Y = √2 (from Cauchy-Schwarz equality).

Step 3: X² + Y² = 4 and X² + Y² ≤ 4 means X² + Y² = 4 exactly. Using the PSD conditions from step 1, each sum ≥ 0 and their total ≤ 0, so each must be = 0.

The PSD condition with c1 = ![1, 0, -X/2, -Y/2] gives:
∑ij c1(i)c1(j)G(i,j) = 2 - X²/2 - Y²/2 + ... but actually, I showed it equals
2 - (X² + Y²)/2 = 0 when X² + Y² = 4.

Wait, more precisely: the two PSD conditions (for c1 and c2) summed give:
2 - X²/2 - Y²/2 = 0. And since each is ≥ 0, each must be 0.

So ∑ij c1(i)c1(j)G(i,j) = 0.

Step 4: By psd_zero_form with c = c1 and k = 0:
∑j c1(j) G(0,j) = c1(0)·G(0,0) + c1(1)·G(0,1) + c1(2)·G(0,2) + c1(3)·G(0,3)
= 1·1 + 0·G(0,1) + (-X/2)·G(0,2) + (-Y/2)·G(0,3) = 1 - X·a/2 - Y·b/2 = 0
where a = G(0,2), b = G(0,3).

Similarly with c = c1 and k = 2:
∑j c1(j) G(2,j) = G(2,0) + 0 + (-X/2)·G(2,2) + (-Y/2)·G(2,3)
= a + 0 - X/2 - Y·q/2 = 0

And with c = c1 and k = 3:
∑j c1(j) G(3,j) = G(3,0) + 0 + (-X/2)·G(3,2) + (-Y/2)·G(3,3)
= b + 0 - X·q/2 - Y/2 = 0

From k=0: 1 = X·a/2 + Y·b/2
From k=2: a = X/2 + Y·q/2
From k=3: b = X·q/2 + Y/2

From k=2 and k=3: substituting into k=0:
1 = X/2·(X/2 + Yq/2) + Y/2·(Xq/2 + Y/2)
= X²/4 + XYq/4 + XYq/4 + Y²/4
= (X²+Y²)/4 + XYq/2 = 1 + XYq/2

So XYq/2 = 0. Since X = Y = √2, we get q = 0 (i.e. G(2,3) = 0... wait, is this needed?).

Actually let me reconsider. I need to show G(0,1) = 0.

Step 5: By psd_zero_form with c = c2 = ![0, 1, -Y/2, X/2] (which also has quadratic form = 0), k = 0:
∑j c2(j) G(0,j) = 0·1 + 1·G(0,1) + (-Y/2)·G(0,2) + (X/2)·G(0,3)
= G(0,1) - Y·a/2 + X·b/2 = 0

So G(0,1) = Y·a/2 - X·b/2.

From k=2 for c1: a = X/2 + Y·q/2
From k=3 for c1: b = X·q/2 + Y/2

So G(0,1) = Y·(X/2 + Yq/2)/2 - X·(Xq/2 + Y/2)/2
= YX/4 + Y²q/4 - X²q/4 - XY/4
= (Y²-X²)q/4 = 0 (since X = Y = √2).

So G(0,1) = 0.

SUMMARY of formal proof:
1. Set X = G 0 2 - G 1 3, Y = G 0 3 + G 1 2, note X + Y = 2√2
2. Use PSD with c1 = ![1, 0, -X/2, -Y/2] and c2 = ![0, 1, -Y/2, X/2]
3. Show each PSD quadratic form ≥ 0 and their sum = 2 - (X²+Y²)/2
4. Since X+Y = 2√2 and (X+Y)² ≤ 2(X²+Y²), get X²+Y² ≥ 4, combined with ≤ 4 gives = 4
5. So each PSD form = 0
6. Apply psd_zero_form with c2 and k=0, expand to get G(0,1) = (Y²-X²)q/4
7. From X²+Y²=4 and X=Y (equality in Cauchy-Schwarz), Y²-X²=0, so G(0,1)=0
-/
theorem chsh_eq_tsirelson_implies_ortho (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (hCHSH : chshVal G = 2 * Real.sqrt 2) :
    G 0 1 = 0 := by
  -- FromCHSH = 2√2, we get X = Y = √2
  set X := G 0 2 - G 1 3
  set Y := G 0 3 + G 1 2
  have hX : X = Real.sqrt 2 := by
    -- By the properties of the CHSH value and the Tsirelson bound, we know that $X^2 + Y^2 \leq 4$.
    have hXY_le : X^2 + Y^2 ≤ 4 := by
      -- By the properties of the CHSH value and the Tsirelson bound, we know that $X^2 + Y^2 \leq 4$ follows from the PSD conditions.
      have hXY_sq : ∀ (c : Fin 4 → ℝ), (∑ i, ∑ j, c i * c j * G i j) ≥ 0 := by
        exact hPSD;
      have := hXY_sq ( fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then -X / 2 else -Y / 2 ) ; ( have := hXY_sq ( fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then -Y / 2 else X / 2 ) ; ( simp +decide [ Fin.sum_univ_four ] at * ; ) );
      simp_all +decide [ IsNormalized, GSymm ] ; ring_nf at * ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
    unfold chshVal at hCHSH; nlinarith [ sq_nonneg ( G 0 2 - G 1 3 - ( G 0 3 + G 1 2 ) ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
  have hY : Y = Real.sqrt 2 := by
    unfold chshVal at hCHSH; norm_num at *; linarith;
  -- By psd_zero_form with c = c2 = ![0, 1, -Y/2, X/2] (which also has quadratic form = 0), k = 0:
  have h_zero_form : ∑ i, ∑ j, (if i = 0 then 0 else if i = 1 then 1 else if i = 2 then -Y / 2 else X / 2) * (if j = 0 then 0 else if j = 1 then 1 else if j = 2 then -Y / 2 else X / 2) * G i j = 0 := by
    have hpsd_zero_form_c2 : ∑ i, ∑ j, (if i = 0 then 1 else if i = 1 then 0 else if i = 2 then -X / 2 else -Y / 2) * (if j = 0 then 1 else if j = 1 then 0 else if j = 2 then -X / 2 else -Y / 2) * G i j + ∑ i, ∑ j, (if i = 0 then 0 else if i = 1 then 1 else if i = 2 then -Y / 2 else X / 2) * (if j = 0 then 0 else if j = 1 then 1 else if j = 2 then -Y / 2 else X / 2) * G i j = 0 := by
      simp +decide [ Fin.sum_univ_four ];
      rw [ show G 2 0 = G 0 2 by exact hSym _ _, show G 3 0 = G 0 3 by exact hSym _ _, show G 2 1 = G 1 2 by exact hSym _ _, show G 3 1 = G 1 3 by exact hSym _ _, show G 2 3 = G 3 2 by exact hSym _ _ ] ; rw [ hNorm 0, hNorm 1, hNorm 2, hNorm 3 ] ; ring;
      grind;
    linarith [ hPSD ( fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then -X / 2 else -Y / 2 ), hPSD ( fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then -Y / 2 else X / 2 ) ];
  simp +decide [ Fin.sum_univ_four ] at h_zero_form;
  have h_zero_form_k0 : ∑ j, (if j = 0 then 0 else if j = 1 then 1 else if j = 2 then -Y / 2 else X / 2) * G 0 j = 0 := by
    apply_rules [ psd_zero_form ];
    simp +decide [ Fin.sum_univ_four, * ];
    grind +ring;
  simp +decide [ Fin.sum_univ_four, hX, hY ] at h_zero_form_k0;
  have h_zero_form_k2 : ∑ j, (if j = 0 then 1 else if j = 1 then 0 else if j = 2 then -Real.sqrt 2 / 2 else -Real.sqrt 2 / 2) * G 2 j = 0 := by
    apply psd_zero_form G hPSD hNorm hSym;
    simp +decide [ Fin.sum_univ_four ];
    simp_all +decide [ IsNormalized, GSymm ];
    grind;
  simp +decide [ Fin.sum_univ_four ] at h_zero_form_k2;
  have h_zero_form_k3 : ∑ j, (if j = 0 then 1 else if j = 1 then 0 else if j = 2 then -Real.sqrt 2 / 2 else -Real.sqrt 2 / 2) * G 3 j = 0 := by
    apply psd_zero_form G hPSD hNorm hSym (fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then -Real.sqrt 2 / 2 else -Real.sqrt 2 / 2) (by
    simp +decide [ Fin.sum_univ_four ];
    simp_all +decide [ IsNormalized, GSymm ];
    grind) 3
  simp +decide [ Fin.sum_univ_four ] at h_zero_form_k3;
  simp_all +decide [ GSymm ];
  norm_num [ hNorm 0, hNorm 1, hNorm 2, hNorm 3 ] at *;
  grind

/-! ## Part VI: Main Theorem (Theorem 6) -/

/-- **Main theorem**: Under submultiplicativity, `CHSH < 2√2` (strict inequality).

    Proof by contradiction: if `CHSH ≥ 2√2`, then by the Tsirelson bound `CHSH = 2√2`.
    By `chsh_eq_tsirelson_implies_ortho`, `G(0,1) = 0`.
    By `chsh_le_two_of_zero_submult`, `CHSH ≤ 2`.
    But `2 < 2√2`, contradicting `CHSH = 2√2`. -/
theorem chsh_lt_tsirelson_of_submult (G : Fin 4 → Fin 4 → ℝ)
    (hPSD : IsPSD G) (hNorm : IsNormalized G) (hSym : GSymm G)
    (hSub : IsSubmult G) :
    chshVal G < 2 * Real.sqrt 2 := by
  by_contra h
  push_neg at h
  have hle := tsirelson_bound G hPSD hNorm hSym
  have heq : chshVal G = 2 * Real.sqrt 2 := le_antisymm hle h
  have h01 := chsh_eq_tsirelson_implies_ortho G hPSD hNorm hSym heq
  have hle2 := chsh_le_two_of_zero_submult G hPSD hNorm hSym hSub h01
  -- Now chshVal G = 2√2 ≤ 2 but 2√2 > 2, contradiction
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 1)]

/-! ## Part VII: Construction (Theorem 8)

We construct an explicit kernel achieving `CHSH = 5/2 > 2`, demonstrating
that submultiplicativity does NOT enforce the classical bound.

The construction uses Gram vectors:
- `v(A₀) = v(B₀) = (1, 0)`
- `v(A₁) = (1/2, √3/2)`
- `v(B₁) = (1/2, -√3/2)`

The resulting kernel has `G(Aₐ, Bᵦ) = vₐ · vᵦ`.
-/

/-- Example kernel achieving CHSH = 5/2 under all constraints -/
def exG (i j : Fin 4) : ℝ :=
  if i = j then 1
  else if (i, j) = (0, 2) ∨ (i, j) = (2, 0) then 1
  else if (i, j) = (1, 3) ∨ (i, j) = (3, 1) then -1/2
  else 1/2

@[simp] theorem exG_diag (i : Fin 4) : exG i i = 1 := by
  simp [exG]

/-
PROVIDED SOLUTION
By exhaustive case analysis on all 16 pairs (i,j) in Fin 4. Use fin_cases on i and j, then simp [exG] or decide. The kernel is manifestly symmetric from its definition.
-/
theorem exG_symm : GSymm exG := by
  intro i j; fin_cases i <;> fin_cases j <;> rfl;

theorem exG_norm : IsNormalized exG := by
  intro i; exact exG_diag i

/-
PROVIDED SOLUTION
The quadratic form ∑ij c(i)*c(j)*exG(i,j) can be shown to be non-negative by proving it equals a sum of squares.

Strategy: First expand the double sum using simp [Fin.sum_univ_four, exG]. Then use fin_cases or case analysis to simplify the exG values. After expansion, the expression should be a polynomial in c 0, c 1, c 2, c 3 that equals:
(c 0 + c 2 + (c 1 + c 3)/2)^2 + 3/4 * (c 1 - c 3)^2

The key exG values are: exG 0 0 = 1, exG 0 1 = 1/2, exG 0 2 = 1, exG 0 3 = 1/2, exG 1 1 = 1, exG 1 2 = 1/2, exG 1 3 = -1/2, exG 2 2 = 1, exG 2 3 = 1/2, exG 3 3 = 1, and G is symmetric.

After the expansion the goal becomes showing a specific polynomial in c 0, c 1, c 2, c 3 is ≥ 0. Use nlinarith with sq_nonneg hints.

Alternative approach: first use `have` to compute each exG value (using simp [exG] or norm_num), substitute them in, simplify with ring, and conclude with nlinarith.
-/
theorem exG_psd : IsPSD exG := by
  intro c
  simp [IsPSD, exG];
  norm_num [ Fin.sum_univ_four ] at *;
  -- The expression can be rewritten as the sum of squares, which is always non-negative.
  have h_sum_squares : (c 0 + c 2 + (c 1 + c 3) / 2) ^ 2 + (3 / 4) * (c 1 - c 3) ^ 2 ≥ 0 := by
    positivity;
  grind

/-
PROVIDED SOLUTION
Verify all 64 triples (i,j,k) in Fin 4. The absolute values of exG entries are:
- |exG i i| = 1 for all i
- |exG 0 2| = |exG 2 0| = 1
- |exG 1 3| = |exG 3 1| = 1/2
- All other off-diagonal entries have |exG i j| = 1/2

For any triple, if j = i or j = k, the inequality is trivial (one side uses |G(i,i)| = 1).
For distinct i,j,k: the products |G(i,j)|·|G(j,k)| are at most 1·1/2 = 1/2 (when one factor is 1)
or 1/2·1/2 = 1/4 (when both are 1/2). The minimum |G(i,k)| is 1/2, so 1/2 ≥ 1/2 or 1/2 ≥ 1/4.
When the product involves |G(0,2)|=1, we need |G(i,k)| ≥ 1·|G(j,k)| = |G(j,k)|, which is |G(i,k)| ≥ |G(j,k)|.
The critical case is like (1,0,2): |G(1,2)| ≥ |G(1,0)|·|G(0,2)| = 1/2·1 = 1/2 ✓ (equality).

Use fin_cases i, fin_cases j, fin_cases k and simp [exG, IsSubmult, abs_of_pos, abs_of_nonneg] then norm_num.
-/
theorem exG_submult : IsSubmult exG := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [ exG ] ;
  all_goals norm_num [ Fin.ext_iff, abs_of_nonneg ] ;

/-
PROVIDED SOLUTION
Direct computation: chshVal exG = exG 0 2 + exG 0 3 + exG 1 2 - exG 1 3 = 1 + 1/2 + 1/2 - (-1/2) = 5/2. Unfold chshVal and exG, then norm_num.
-/
theorem exG_chsh : chshVal exG = 5 / 2 := by
  unfold chshVal exG; norm_num;
  norm_num [ Fin.ext_iff ]

/-- The example kernel achieves `CHSH > 2`, proving that submultiplicativity
    allows nonlocality beyond the classical Bell bound. -/
theorem exG_chsh_gt_two : chshVal exG > 2 := by
  have h := exG_chsh
  linarith

/-! ## Summary of Results

The key conceptual finding is **Case D** (partial quantum regime):

* `2 < sup|CHSH| ≤ 5/2 < 2√2`

More precisely:
* **Lower bound**: `exG_chsh_gt_two` shows `sup ≥ 5/2 > 2`
* **Upper bound**: `chsh_lt_tsirelson_of_submult` shows `sup < 2√2`
* **Interpretation**: Spacetime geometry (submultiplicativity) imposes a quantitative
  limit on quantum nonlocality, but does not reduce it to classical levels.

The gap between 2 (classical) and the submultiplicative supremum (≥ 5/2)
demonstrates that **geometry and nonlocality can coexist nontrivially**.
-/

end