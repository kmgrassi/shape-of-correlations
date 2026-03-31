/-
# Construction: CHSH > 2 Under Submultiplicativity (Theorem 5 / Assumption C)

We construct an explicit normalized PSD kernel satisfying Bell-sector
submultiplicativity with CHSH > 2, demonstrating that geometry does not
force Bell classicality.

## Construction

Use the symmetric ansatz with parameter c ∈ (0, 1):
  G(A₀,B₀) = G(A₀,B₁) = G(A₁,B₀) = c
  G(A₁,B₁) = -c
  G(A₀,A₁) = G(B₀,B₁) = c²  (minimal for submultiplicativity)
  CHSH = 4c

The 4×4 matrix:
  [1   c²  c   c ]
  [c²  1   c  -c ]
  [c   c   1   c²]
  [c  -c   c²  1 ]

This is PSD when c⁴ + 2c³ + 2c² ≤ 1 (from eigenvalue analysis).

For c = 51/100:
  - CHSH = 204/100 = 2.04 > 2
  - c⁴ + 2c³ + 2c² = 0.8531... < 1 ✓ (PSD)
  - s = c² satisfies submultiplicativity constraints ✓
-/
import Mathlib
import RequestProject.Defs

open Real

noncomputable section

/-! ## The explicit construction with c = 51/100 -/

/-- The kernel value c = 51/100 -/
def c₀ : ℝ := 51 / 100

/-- The internal overlap s = c² = 2601/10000 -/
def s₀ : ℝ := c₀ ^ 2

/-- The explicit 4×4 kernel matrix parametrized by (c, s=c²).
    Indices: 0 = A₀, 1 = A₁, 2 = B₀, 3 = B₁ -/
def bellKernel (c : ℝ) : Fin 4 → Fin 4 → ℝ := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => c ^ 2
  | 0, 2 => c
  | 0, 3 => c
  | 1, 0 => c ^ 2
  | 1, 1 => 1
  | 1, 2 => c
  | 1, 3 => -c
  | 2, 0 => c
  | 2, 1 => c
  | 2, 2 => 1
  | 2, 3 => c ^ 2
  | 3, 0 => c
  | 3, 1 => -c
  | 3, 2 => c ^ 2
  | 3, 3 => 1

/-
PROBLEM
The CHSH value of bellKernel(c) equals 4c

PROVIDED SOLUTION
Unfold CHSH_val and bellKernel, then compute: bellKernel c 0 2 + bellKernel c 0 3 + bellKernel c 1 2 - bellKernel c 1 3 = c + c + c - (-c) = 4c. Use simp/ring.
-/
theorem bellKernel_chsh (c : ℝ) :
    CHSH_val (bellKernel c) 0 1 2 3 = 4 * c := by
  unfold CHSH_val bellKernel; ring!;

/-
PROBLEM
bellKernel is symmetric

PROVIDED SOLUTION
Check all 16 cases by fin_cases on i, j and verify G(i,j) = G(j,i) by simp.
-/
theorem bellKernel_symmetric (c : ℝ) :
    IsSymmetricKernel (bellKernel c) := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_cast;

/-
PROBLEM
bellKernel is normalized

PROVIDED SOLUTION
Check all 4 cases by fin_cases on i and verify G(i,i) = 1. Each diagonal entry is 1 by definition.
-/
theorem bellKernel_normalized (c : ℝ) :
    IsNormalizedKernel (bellKernel c) := by
  intro i; fin_cases i <;> rfl;

/-
PROBLEM
bellKernel satisfies Bell-sector submultiplicativity when 0 ≤ c ≤ 1

PROVIDED SOLUTION
We need to verify |G(i,k)| ≥ |G(i,j)|*|G(j,k)| for all i,j,k ∈ {0,1,2,3}. By case analysis (fin_cases on i, j, k), most cases are trivial:
- When j = i or j = k, the constraint is |G(i,k)| ≥ |G(i,i)|*|G(i,k)| = |G(i,k)| (since diagonal is 1), which holds.
- The binding constraints are: |G(0,1)| ≥ |G(0,2)|*|G(2,1)| and similar, i.e., c² ≥ c*c = c², which holds.
- For constraints involving the negative entry G(1,3) = -c: |G(0,1)| ≥ |G(0,3)|*|G(3,1)| = c*c = c², and c² ≥ c² ✓.
- Other cases: |G(i,k)| = c and the product ≤ c²*c = c³ ≤ c since c ≤ 1.

Use fin_cases to enumerate all 64 cases and verify each with norm_num or nlinarith using hc0 and hc1.
-/
theorem bellKernel_submult (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    BellSubmult (bellKernel c) 0 1 2 3 := by
  intro i hi j hj k hk; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp +decide at hi hj hk ⊢;
  all_goals unfold bellKernel; norm_num [ abs_of_nonneg, hc0, hc1 ] ;
  all_goals nlinarith [ pow_nonneg hc0 3 ] ;

/-
PROBLEM
bellKernel is PSD when 0 ≤ c and c⁴ + 2c³ + 2c² ≤ 1.
    The proof uses the block structure [[A,B],[B,A]] where A = [[1,c²],[c²,1]], B = [[c,c],[c,-c]].
    The eigenvalues are 1 ± √(c⁴+2c³+2c²) and 1 ± √(c⁴-2c³+2c²), all nonneg under the hypothesis.

PROVIDED SOLUTION
Unfold IsPSDKernel and bellKernel. For coefficient vector a : Fin 4 → ℝ, expand the sum over Fin 4 using Fin.sum_univ_four. The quadratic form becomes:

Q = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + 2*c^2*(a 0 * a 1 + a 2 * a 3) + 2*c*(a 0 * a 2 + a 0 * a 3 + a 1 * a 2 - a 1 * a 3)

Write this as a sum of nonneg terms. Key decomposition:

Let p = a 0 + a 2, q = a 1 + a 3, r = a 0 - a 2, t = a 1 - a 3.
Then Q = (1/2)*((1+c)*p^2 + 2*c*(c+1)*p*q + (1-c)*q^2) + (1/2)*((1-c)*r^2 - 2*c*(1-c)*r*t + (1+c)*t^2)

Actually, simpler: the quadratic form can be shown nonneg using nlinarith with the right auxiliary squares. The hypothesis c^4 + 2c^3 + 2c^2 ≤ 1 and 0 ≤ c ensure all eigenvalues are nonneg.

Try: unfold everything, simp with Fin.sum_univ_four, ring_nf, then nlinarith with:
- sq_nonneg (a 0 + a 2 + c*(a 1 + a 3))
- sq_nonneg (a 0 - a 2 - c*(a 1 - a 3))
- sq_nonneg (a 1 + a 3)
- sq_nonneg (a 1 - a 3)
- sq_nonneg c
- hc0, hc, and various products
-/
theorem bellKernel_psd (c : ℝ) (hc0 : 0 ≤ c) (hc : c ^ 4 + 2 * c ^ 3 + 2 * c ^ 2 ≤ 1) :
    IsPSDKernel (bellKernel c) := by
  intro a
  set p := a 0 + a 2
  set q := a 1 + a 3
  set r := a 0 - a 2
  set t := a 1 - a 3
  have h_pos : (1/2)*((1+c)*p^2 + 2*c*(c+1)*p*q + (1-c)*q^2) + (1/2)*((1-c)*r^2 - 2*c*(1-c)*r*t + (1+c)*t^2) ≥ 0 := by
    -- Since the discriminant is non-positive, the quadratic form is non-negative.
    have h_quadratic_nonneg : ∀ p q : ℝ, (1 + c) * p ^ 2 + 2 * c * (c + 1) * p * q + (1 - c) * q ^ 2 ≥ 0 := by
      intro p q; nlinarith [ sq_nonneg ( ( 1 + c ) * p + c * ( c + 1 ) * q ) ] ;
    have h_quadratic_nonneg2 : ∀ r t : ℝ, (1 - c) * r ^ 2 - 2 * c * (1 - c) * r * t + (1 + c) * t ^ 2 ≥ 0 := by
      intros r t; nlinarith [ sq_nonneg ( r - t * c ), sq_nonneg ( t - r * c ), sq_nonneg ( r + t * c ), sq_nonneg ( t + r * c ) ] ;
    exact add_nonneg ( mul_nonneg ( by norm_num ) ( h_quadratic_nonneg p q ) ) ( mul_nonneg ( by norm_num ) ( h_quadratic_nonneg2 r t ) );
  convert h_pos using 1 ; ring!;
  unfold bellKernel; norm_num [ Fin.sum_univ_four ] ; ring;

/-- **Theorem 5 (Assumption C):** There exists a normalized PSD kernel satisfying
    Bell-sector submultiplicativity with |CHSH| > 2.

    We use c = 51/100 = 0.51, giving CHSH = 2.04 > 2. -/
theorem exists_submult_chsh_gt_two :
    ∃ G : Fin 4 → Fin 4 → ℝ,
      IsSymmetricKernel G ∧ IsNormalizedKernel G ∧ IsPSDKernel G ∧
      BellSubmult G 0 1 2 3 ∧ CHSH_val G 0 1 2 3 > 2 := by
  refine ⟨bellKernel c₀, bellKernel_symmetric c₀, bellKernel_normalized c₀, ?_, ?_, ?_⟩
  · exact bellKernel_psd c₀ (by unfold c₀; norm_num) (by unfold c₀; norm_num)
  · exact bellKernel_submult c₀ (by unfold c₀; norm_num) (by unfold c₀; norm_num)
  · rw [bellKernel_chsh]
    unfold c₀
    norm_num

/-! ## Symmetric ansatz analysis -/

-- Under the symmetric ansatz with s = c², the PSD condition reduces to
-- c⁴ + 2c³ + 2c² ≤ 1 (from the binding eigenvalue constraint).
-- The maximum CHSH under the symmetric ansatz with submultiplicativity
-- is 4·c_max where c_max is the largest root of c⁴+2c³+2c²=1 in (0,1).
-- Numerically c_max ≈ 0.5437, giving CHSH_max ≈ 2.175.

end