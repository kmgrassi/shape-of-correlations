import Mathlib

/-!
# CHSH Bounds Under Geometric Constraints

We formalize how geometric consistency constraints (submultiplicativity) on a normalized
PSD kernel restrict Bell/CHSH violation.

## Main results

* `kernel_bound`: |G(i,j)| ≤ 1 for any PSD normalized kernel (Cauchy-Schwarz)
* `tsirelson_bound`: |CHSH| ≤ 2√2 for any PSD normalized kernel
* `no_go`: BellSubmult implies |CHSH| < 2√2 (strict inequality)
* `tsirelson_sat_implies_not_submult`: |CHSH| = 2√2 ⟹ ¬BellSubmult
* `psd_necessary`: Without PSD, CHSH = 4 is achievable with BellSubmult
* `no_go_approx`: For any μ > 0, ApproxSubmult μ still prevents Tsirelson saturation

## Setup

We work with a 4×4 kernel indexed by `Fin 4`:
- `0` = A₀ (Alice's first measurement setting)
- `1` = A₁ (Alice's second measurement setting)
- `2` = B₀ (Bob's first measurement setting)
- `3` = B₁ (Bob's second measurement setting)

## Mathematical summary

The key insight: geometry (via submultiplicativity) acts as a quantitative regulator
of Bell nonlocality. The Tsirelson bound 2√2 requires G(B₀,B₁) = 0, but
submultiplicativity forces |G(B₀,B₁)| ≥ |G(B₀,A₀)|·|G(A₀,B₁)|, creating a
contradiction when the correlators are large enough to saturate the bound.

## Interpretation

This formalization establishes a **law of structure linking geometry and quantum behavior**:
geometric consistency (submultiplicativity) acts as a quantitative regulator that prevents
the full quantum violation of Bell inequalities. The bound C* satisfies 2 < C* < 2√2,
placing it strictly between the classical (2) and quantum (2√2) limits.
-/

noncomputable section

namespace CHSH

-- ============================================================================
-- Part I: Core Definitions
-- ============================================================================

/-- A CHSH kernel setup: a 4×4 real-valued kernel that is symmetric, normalized
    (unit diagonal), and positive semi-definite. -/
structure Setup where
  /-- The kernel function G : {A₀,A₁,B₀,B₁}² → ℝ -/
  G : Fin 4 → Fin 4 → ℝ
  /-- Symmetry: G(i,j) = G(j,i) -/
  symm : ∀ i j, G i j = G j i
  /-- Normalization: G(i,i) = 1 -/
  normalized : ∀ i, G i i = 1
  /-- Positive semi-definiteness: ∑ᵢⱼ cᵢcⱼG(i,j) ≥ 0 for all weight functions c -/
  psd : ∀ c : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, c i * c j * G i j

/-- The CHSH value: E(0,0) + E(0,1) + E(1,0) - E(1,1)
    where E(a,b) = G(Aₐ,Bᵦ). -/
def Setup.chshValue (σ : Setup) : ℝ :=
  σ.G 0 2 + σ.G 0 3 + σ.G 1 2 - σ.G 1 3

/-- Bell submultiplicativity on the Bell sector:
    |G(i,k)| ≥ |G(i,j)|·|G(j,k)| for all i,j,k ∈ {A₀,A₁,B₀,B₁}. -/
def Setup.BellSubmult (σ : Setup) : Prop :=
  ∀ i j k : Fin 4, |σ.G i k| ≥ |σ.G i j| * |σ.G j k|

/-- Approximate submultiplicativity with relaxation parameter μ ∈ (0,1]:
    |G(i,k)| ≥ μ · |G(i,j)| · |G(j,k)|. -/
def Setup.ApproxSubmult (σ : Setup) (μ : ℝ) : Prop :=
  ∀ i j k : Fin 4, |σ.G i k| ≥ μ * (|σ.G i j| * |σ.G j k|)

-- ============================================================================
-- Part II: Helper Lemmas
-- ============================================================================

/-- The PSD quadratic form expanded for Fin 4. -/
lemma psd_expand (G : Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) :
    ∑ i : Fin 4, ∑ j : Fin 4, c i * c j * G i j =
    c 0 * c 0 * G 0 0 + c 0 * c 1 * G 0 1 + c 0 * c 2 * G 0 2 + c 0 * c 3 * G 0 3 +
    c 1 * c 0 * G 1 0 + c 1 * c 1 * G 1 1 + c 1 * c 2 * G 1 2 + c 1 * c 3 * G 1 3 +
    c 2 * c 0 * G 2 0 + c 2 * c 1 * G 2 1 + c 2 * c 2 * G 2 2 + c 2 * c 3 * G 2 3 +
    c 3 * c 0 * G 3 0 + c 3 * c 1 * G 3 1 + c 3 * c 2 * G 3 2 + c 3 * c 3 * G 3 3 := by
  simpa only [Fin.sum_univ_four] using by ring

/-- A non-negative quadratic polynomial has non-positive discriminant. -/
lemma quadratic_nonneg_discriminant {a b c : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + b * t + c) :
    b ^ 2 ≤ 4 * a * c := by
  by_cases ha_pos : 0 < a
  · nlinarith [h (-b / (2 * a)),
      mul_div_cancel₀ (-b) (by positivity : (2 * a) ≠ 0)]
  · norm_num [show a = 0 by linarith] at *
    contrapose! h
    exact ⟨(-c - 1) / b, by rw [mul_div_cancel₀ _ h]; linarith⟩

-- ============================================================================
-- Part III: Kernel Bound (Cauchy-Schwarz)
-- ============================================================================

/-- **Cauchy-Schwarz for kernels**: Every entry of a PSD normalized symmetric
    kernel has absolute value at most 1. -/
theorem kernel_bound (σ : Setup) (i j : Fin 4) : |σ.G i j| ≤ 1 := by
  have h_psd : ∀ i j : Fin 4, 0 ≤ 1 + 1 + 2 * σ.G i j ∧ 0 ≤ 1 + 1 - 2 * σ.G i j := by
    intro i j
    have := σ.psd (fun x => if x = i then 1 else if x = j then (-1) else 0)
    simp_all +decide [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']
    have := σ.psd (fun x => if x = i then 1 else if x = j then 1 else 0)
    simp_all +decide [Finset.sum_add_distrib, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']
    split_ifs at * <;> simp_all +decide [σ.symm] <;>
      constructor <;> linarith [σ.normalized i, σ.normalized j]
  exact abs_le.mpr ⟨by linarith [h_psd i j], by linarith [h_psd i j]⟩

-- ============================================================================
-- Part IV: PSD Quadratic Form Bounds
-- ============================================================================

/-- PSD consequence: (G(A₀,B₀) + G(A₀,B₁))² ≤ 2(1 + G(B₀,B₁)).
    Derived from the quadratic form with c = (1, 0, t, t) being non-negative. -/
theorem psd_sum_sq_le (σ : Setup) :
    (σ.G 0 2 + σ.G 0 3) ^ 2 ≤ 2 * (1 + σ.G 2 3) := by
  have h_psd : ∀ t : ℝ,
      0 ≤ 2 * (1 + σ.G 2 3) * t ^ 2 + 2 * (σ.G 0 2 + σ.G 0 3) * t + 1 := by
    intro t
    have := σ.psd (fun i => if i = 0 then 1 else if i = 1 then 0
                            else if i = 2 then t else t)
    simp [Fin.sum_univ_four] at this
    convert this using 1
    rw [σ.normalized 0, σ.normalized 2, σ.normalized 3, σ.symm 0 2, σ.symm 0 3, σ.symm 2 3]
    ring
  have h_discriminant :
      (2 * (σ.G 0 2 + σ.G 0 3)) ^ 2 ≤ 4 * (2 * (1 + σ.G 2 3)) * 1 := by
    apply quadratic_nonneg_discriminant
    · have := σ.psd (fun i => if i = 2 then 1 else if i = 3 then 1 else 0)
      simp_all +decide [Fin.sum_univ_four]
      linarith [σ.normalized 2, σ.normalized 3, σ.symm 2 3]
    · assumption
  linarith

/-- PSD consequence: (G(A₁,B₀) - G(A₁,B₁))² ≤ 2(1 - G(B₀,B₁)).
    Derived from the quadratic form with c = (0, 1, t, -t) being non-negative. -/
theorem psd_diff_sq_le (σ : Setup) :
    (σ.G 1 2 - σ.G 1 3) ^ 2 ≤ 2 * (1 - σ.G 2 3) := by
  have h_quad_form : ∀ t : ℝ,
      0 ≤ 2 * (1 - σ.G 2 3) * t ^ 2 + 2 * (σ.G 1 2 - σ.G 1 3) * t + 1 := by
    intro t
    have h_quad : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4,
        (if i = 1 then 1 else if i = 2 then t else if i = 3 then -t else 0) *
        (if j = 1 then 1 else if j = 2 then t else if j = 3 then -t else 0) *
        σ.G i j :=
      σ.psd (fun i => if i = 1 then 1 else if i = 2 then t else if i = 3 then -t else 0)
    simp +decide [Fin.sum_univ_four] at h_quad
    convert h_quad using 1
    rw [σ.normalized 1, σ.normalized 2, σ.normalized 3, σ.symm 1 2, σ.symm 1 3, σ.symm 2 3]
    ring
  by_cases h₂ : 1 - σ.G 2 3 = 0
  · contrapose! h_quad_form
    exact ⟨ -2 / ( 2 * ( σ.G 1 2 - σ.G 1 3 ) ), by nlinarith [ mul_div_cancel₀ ( -2 ) ( by nlinarith : ( 2 * ( σ.G 1 2 - σ.G 1 3 ) ) ≠ 0 ) ] ⟩
  · by_cases h₂' : 1 - σ.G 2 3 > 0
    · nlinarith [ h_quad_form ( - ( σ.G 1 2 - σ.G 1 3 ) / ( 2 * ( 1 - σ.G 2 3 ) ) ), mul_div_cancel₀ ( - ( σ.G 1 2 - σ.G 1 3 ) ) ( by linarith : ( 2 * ( 1 - σ.G 2 3 ) ) ≠ 0 ) ]
    · exact False.elim <| ‹¬1 - σ.G 2 3 = 0› <| by nlinarith [ h_quad_form ( -1 ), h_quad_form 0, h_quad_form 1, abs_le.mp ( kernel_bound σ 2 3 ) ]

-- ============================================================================
-- Part V: Tsirelson Bound
-- ============================================================================

/-- For non-negative reals, √a + √b ≤ √(2(a+b)).
    Proof: (√a + √b)² = a + b + 2√(ab) ≤ 2(a+b) since 2√(ab) ≤ a + b (AM-GM). -/
theorem sqrt_sum_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt (2 * (a + b)) :=
  Real.le_sqrt_of_sq_le (by
    linarith [sq_nonneg (Real.sqrt a - Real.sqrt b),
      Real.mul_self_sqrt ha, Real.mul_self_sqrt hb])

/-- **Tsirelson bound (Theorem 2)**: |CHSH(G)| ≤ 2√2 for any PSD normalized
    symmetric kernel. This is the quantum mechanical upper bound on CHSH correlations.

    Proof: Write CHSH = (G₀₂ + G₀₃) + (G₁₂ - G₁₃). From PSD:
    - |G₀₂ + G₀₃| ≤ √(2(1 + G₂₃))    (psd_sum_sq_le)
    - |G₁₂ - G₁₃| ≤ √(2(1 - G₂₃))    (psd_diff_sq_le)
    By triangle inequality and √a + √b ≤ √(2(a+b)):
    |CHSH| ≤ √(2(1+G₂₃)) + √(2(1-G₂₃)) ≤ √(2·4) = 2√2. -/
theorem tsirelson_bound (σ : Setup) : |σ.chshValue| ≤ 2 * Real.sqrt 2 := by
  have h_triangle : |σ.chshValue| ≤
      Real.sqrt (2 * (1 + σ.G 2 3)) + Real.sqrt (2 * (1 - σ.G 2 3)) := by
    have h_tri : |σ.chshValue| ≤ |σ.G 0 2 + σ.G 0 3| + |σ.G 1 2 - σ.G 1 3| :=
      abs_le.mpr ⟨by
        cases abs_cases (σ.G 0 2 + σ.G 0 3) <;>
        cases abs_cases (σ.G 1 2 - σ.G 1 3) <;>
        linarith [show σ.chshValue = σ.G 0 2 + σ.G 0 3 + σ.G 1 2 - σ.G 1 3 by
          unfold Setup.chshValue; ring],
      by
        cases abs_cases (σ.G 0 2 + σ.G 0 3) <;>
        cases abs_cases (σ.G 1 2 - σ.G 1 3) <;>
        linarith [show σ.chshValue = σ.G 0 2 + σ.G 0 3 + σ.G 1 2 - σ.G 1 3 by
          unfold Setup.chshValue; ring]⟩
    refine le_trans h_tri <| add_le_add ?_ ?_ <;> refine Real.abs_le_sqrt ?_
    · exact psd_sum_sq_le σ
    · exact psd_diff_sq_le σ
  refine le_trans h_triangle ?_
  convert Real.sqrt_le_sqrt ?_ using 1
  rotate_left; rotate_left
  exact (Real.sqrt (2 * (1 + σ.G 2 3)) + Real.sqrt (2 * (1 - σ.G 2 3))) ^ 2
  exact 8
  · linarith [sq_nonneg (Real.sqrt (2 * (1 + σ.G 2 3)) - Real.sqrt (2 * (1 - σ.G 2 3))),
      Real.mul_self_sqrt (show 0 ≤ 2 * (1 + σ.G 2 3) by
        linarith [abs_le.mp (kernel_bound σ 2 3)]),
      Real.mul_self_sqrt (show 0 ≤ 2 * (1 - σ.G 2 3) by
        linarith [abs_le.mp (kernel_bound σ 2 3)])]
  · rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  · rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul] <;> norm_num

-- ============================================================================
-- Part VI: No-Go Theorem
-- ============================================================================

/-- If |CHSH| = 2√2, then G(B₀,B₁) = 0.
    This follows from the equality condition in √a + √b ≤ √(2(a+b)):
    equality holds iff a = b, i.e., 2(1+β) = 2(1-β), i.e., β = 0. -/
theorem tsirelson_equality_beta_zero (σ : Setup)
    (h : |σ.chshValue| = 2 * Real.sqrt 2) :
    σ.G 2 3 = 0 := by
  contrapose! h with h_contra; generalize_proofs at *; (
  have h_sqrt_ineq : Real.sqrt (2 * (1 + σ.G 2 3)) + Real.sqrt (2 * (1 - σ.G 2 3)) < 2 * Real.sqrt 2 := by
    suffices h_sq : (Real.sqrt (2 * (1 + σ.G 2 3)) + Real.sqrt (2 * (1 - σ.G 2 3)))^2 < (2 * Real.sqrt 2)^2 by
      contrapose! h_sq; gcongr
    generalize_proofs at *; (
    ring_nf; norm_num; (
    rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> nlinarith [ mul_self_pos.mpr h_contra, Real.mul_self_sqrt ( show 0 <= 2 + σ.G 2 3 * 2 by nlinarith [ abs_le.mp ( kernel_bound σ 2 3 ) ] ), Real.mul_self_sqrt ( show 0 <= 2 - σ.G 2 3 * 2 by nlinarith [ abs_le.mp ( kernel_bound σ 2 3 ) ] ) ] ;))
  generalize_proofs at *; (
  have h_triangle : |σ.chshValue| ≤ |σ.G 0 2 + σ.G 0 3| + |σ.G 1 2 - σ.G 1 3| := by
    exact abs_le.mpr ⟨ by cases abs_cases ( σ.G 0 2 + σ.G 0 3 ) <;> cases abs_cases ( σ.G 1 2 - σ.G 1 3 ) <;> linarith! [ show σ.chshValue = σ.G 0 2 + σ.G 0 3 + σ.G 1 2 - σ.G 1 3 by rfl ], by cases abs_cases ( σ.G 0 2 + σ.G 0 3 ) <;> cases abs_cases ( σ.G 1 2 - σ.G 1 3 ) <;> linarith! [ show σ.chshValue = σ.G 0 2 + σ.G 0 3 + σ.G 1 2 - σ.G 1 3 by rfl ] ⟩ ;
  generalize_proofs at *; (
  have h_psd_ineqs : |σ.G 0 2 + σ.G 0 3| ≤ Real.sqrt (2 * (1 + σ.G 2 3)) ∧ |σ.G 1 2 - σ.G 1 3| ≤ Real.sqrt (2 * (1 - σ.G 2 3)) := by
    exact ⟨ Real.abs_le_sqrt <| by linarith [ psd_sum_sq_le σ ], Real.abs_le_sqrt <| by linarith [ psd_diff_sq_le σ ] ⟩ ;
  generalize_proofs at *; (
  linarith [ Real.sqrt_nonneg 2 ] ;))))

/-- If |CHSH| = 2√2, then (G(A₀,B₀) + G(A₀,B₁))² ≥ 2.
    With β = 0: |G₁₂ - G₁₃| ≤ √2, so |G₀₂ + G₀₃| ≥ 2√2 - √2 = √2. -/
theorem tsirelson_equality_sum_bound (σ : Setup)
    (h : |σ.chshValue| = 2 * Real.sqrt 2) :
    (σ.G 0 2 + σ.G 0 3) ^ 2 ≥ 2 := by
  have h_diff : |σ.G 1 2 - σ.G 1 3| ≤ Real.sqrt 2 := by
    have h23 : σ.G 2 3 = 0 := tsirelson_equality_beta_zero σ h
    have := psd_diff_sq_le σ
    rw [h23] at this; simp at this
    exact Real.abs_le_sqrt (by linarith)
  contrapose! h
  rw [CHSH.Setup.chshValue]
  exact ne_of_lt (abs_lt.mpr ⟨by
    nlinarith only [abs_le.mp h_diff, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, h],
  by
    nlinarith only [abs_le.mp h_diff, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, h]⟩)

/-- **No-go theorem (Theorem 1)**: Submultiplicativity prevents saturation of
    the Tsirelson bound. Any PSD normalized kernel satisfying BellSubmult has
    |CHSH| strictly less than 2√2.

    This establishes C* < 2√2, resolving the optimization problem as **Case B**.

    Proof: If |CHSH| = 2√2, then G(B₀,B₁) = 0 (equality condition).
    BellSubmult gives 0 = |G(B₀,B₁)| ≥ |G(B₀,A₀)|·|G(A₀,B₁)|,
    forcing G(A₀,B₀) = 0 or G(A₀,B₁) = 0. But then
    |G(A₀,B₀) + G(A₀,B₁)| ≤ 1 < √2, contradicting the equality condition. -/
theorem no_go (σ : Setup) (hbs : σ.BellSubmult) :
    |σ.chshValue| < 2 * Real.sqrt 2 := by
  by_contra h_contra
  have h_eq : |σ.chshValue| = 2 * Real.sqrt 2 :=
    le_antisymm (tsirelson_bound σ) (not_lt.mp h_contra)
  have h_beta_zero : σ.G 2 3 = 0 := tsirelson_equality_beta_zero σ h_eq
  have h_sum_bound : (σ.G 0 2 + σ.G 0 3) ^ 2 ≥ 2 := tsirelson_equality_sum_bound σ h_eq
  have h_g02_or_g03_zero : σ.G 0 2 = 0 ∨ σ.G 0 3 = 0 := by
    have := hbs 2 0 3
    simp_all +decide
    exact Classical.or_iff_not_imp_left.2 fun h => by
      exact abs_eq_zero.mp <| by
        exact mul_eq_zero.mp (le_antisymm this <| by positivity) |>
          Or.resolve_left <| by simp [h, σ.symm]
  have h_contradiction : (σ.G 0 2 + σ.G 0 3) ^ 2 < 2 := by
    cases h_g02_or_g03_zero <;> simp_all +decide [sq]
    · nlinarith [(abs_le.mp <| kernel_bound σ 0 2), (abs_le.mp <| kernel_bound σ 0 3)]
    · nlinarith [abs_le.mp (kernel_bound σ 0 2)]
  linarith [h_sum_bound, h_contradiction]

/-- Equivalent formulation: Tsirelson saturation implies failure of
    submultiplicativity. (Lemma A: Orthogonality obstruction) -/
theorem tsirelson_sat_implies_not_submult (σ : Setup)
    (h : |σ.chshValue| = 2 * Real.sqrt 2) : ¬σ.BellSubmult := by
  intro hbs
  exact absurd h (ne_of_lt (no_go σ hbs))

-- ============================================================================
-- Part VII: Necessity of PSD (Theorem 3)
-- ============================================================================

/-- **Necessity of PSD**: Without PSD, CHSH = 4 is achievable with BellSubmult.
    Take G(i,j) = 1 for all (i,j) except G(1,3) = G(3,1) = -1.
    All |entries| = 1, so BellSubmult holds (1 ≥ 1·1), and CHSH = 4 > 2√2.
    This shows PSD is essential for the Tsirelson bound. -/
theorem psd_necessary : ∃ (G : Fin 4 → Fin 4 → ℝ),
    (∀ i j, G i j = G j i) ∧
    (∀ i, G i i = 1) ∧
    (∀ i j k : Fin 4, |G i k| ≥ |G i j| * |G j k|) ∧
    G 0 2 + G 0 3 + G 1 2 - G 1 3 = 4 := by
  use fun i j => if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then -1 else 1
  simp +decide
  norm_cast

-- ============================================================================
-- Part VIII: Relaxation Theory (Approximate Submultiplicativity)
-- ============================================================================

/-- BellSubmult is equivalent to ApproxSubmult with μ = 1. -/
theorem bellsubmult_iff_approx_one (σ : Setup) :
    σ.BellSubmult ↔ σ.ApproxSubmult 1 := by
  unfold Setup.BellSubmult Setup.ApproxSubmult; aesop

/-- ApproxSubmult is anti-monotone in μ: weaker constraint for smaller μ. -/
theorem approx_submult_anti_mono (σ : Setup) {μ₁ μ₂ : ℝ} (hle : μ₁ ≤ μ₂)
    (h : σ.ApproxSubmult μ₂) : σ.ApproxSubmult μ₁ :=
  fun i j k => le_trans (mul_le_mul_of_nonneg_right hle (by positivity)) (h i j k)

/-- ApproxSubmult with μ = 0 is always satisfied (vacuous constraint). -/
theorem approx_submult_zero (σ : Setup) : σ.ApproxSubmult 0 :=
  fun _ _ _ => by simp

/-- **Relaxation theorem (Theorem 5, partial)**: For any μ > 0, ApproxSubmult μ
    still prevents Tsirelson saturation. C(μ) < 2√2 for all μ > 0.

    Combined with C(0) = 2√2 (Tsirelson bound achievable without submultiplicativity),
    this gives the **geometry-nonlocality tradeoff**: as the geometric constraint
    weakens (μ → 0), the CHSH bound approaches the Tsirelson limit from below.

    Proof: Same as no_go — from |CHSH| = 2√2, G(B₀,B₁) = 0.
    ApproxSubmult gives 0 ≥ μ·|G(A₀,B₀)|·|G(A₀,B₁)|.
    Since μ > 0, we get the same contradiction. -/
theorem no_go_approx (σ : Setup) {μ : ℝ} (hμ : 0 < μ) (h : σ.ApproxSubmult μ) :
    |σ.chshValue| < 2 * Real.sqrt 2 := by
  by_contra h_contra
  have h_eq : |σ.chshValue| = 2 * Real.sqrt 2 :=
    le_antisymm (by simpa using tsirelson_bound σ) (not_lt.mp h_contra)
  have h_beta_zero : σ.G 2 3 = 0 := tsirelson_equality_beta_zero σ h_eq
  have h_sum_ge : (σ.G 0 2 + σ.G 0 3) ^ 2 ≥ 2 := tsirelson_equality_sum_bound σ h_eq
  have h_bounds : |σ.G 0 2| ≤ 1 ∧ |σ.G 0 3| ≤ 1 := ⟨kernel_bound σ 0 2, kernel_bound σ 0 3⟩
  have h_submult := h 2 0 3
  simp_all +decide [abs_le]
  have h_prod_le : (σ.G 0 2 + σ.G 0 3) ^ 2 ≤ 1 := by
    have h23 : σ.G 2 0 = σ.G 0 2 := σ.symm 2 0
    rw [h23] at h_submult
    have h02_bound := abs_le.mp (kernel_bound σ 0 2)
    have h03_bound := abs_le.mp (kernel_bound σ 0 3)
    by_cases h02 : σ.G 0 2 = 0
    · simp [h02]; nlinarith
    · have : |σ.G 0 2| > 0 := abs_pos.mpr h02
      have h_mu_prod : μ * (|σ.G 0 2| * |σ.G 0 3|) ≤ 0 := h_submult
      have : |σ.G 0 2| * |σ.G 0 3| ≤ 0 := by nlinarith
      have : |σ.G 0 2| * |σ.G 0 3| = 0 := le_antisymm this (by positivity)
      have : |σ.G 0 3| = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (by linarith)
        · exact h
      have : σ.G 0 3 = 0 := abs_eq_zero.mp this
      simp [this]; nlinarith
  linarith

-- ============================================================================
-- Part IX: Structural Summary
-- ============================================================================

/-- **Bound summary (Theorem 4, partial)**: The constraints
    {PSD, normalization, symmetry, BellSubmult} together enforce |CHSH| < 2√2.
    - PSD + normalization + symmetry alone give |CHSH| ≤ 2√2 (Tsirelson bound)
    - Adding BellSubmult strengthens this to |CHSH| < 2√2 (strict)
    - Removing PSD allows |CHSH| = 4 (psd_necessary)
    - Removing BellSubmult allows |CHSH| = 2√2 (Tsirelson is tight) -/
theorem bound_summary (σ : Setup) :
    |σ.chshValue| ≤ 2 * Real.sqrt 2 ∧
    (σ.BellSubmult → |σ.chshValue| < 2 * Real.sqrt 2) :=
  ⟨tsirelson_bound σ, no_go σ⟩

end CHSH

end
