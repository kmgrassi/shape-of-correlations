import Mathlib

/-!
# Emergent Space from Correlation Kernels

We formalize a finite relational toy model of emergent space.
Given a finite type `S` and a symmetric correlation kernel `I : S → S → ℝ`
with `0 < I i j ≤ 1` and `I i i = 1`, we define the emergent distance
`d i j = -log(I i j)` and prove it forms a pseudometric (and metric under
an additional condition).

## Main results

* `CorrKernel.d_nonneg`, `CorrKernel.d_self`, `CorrKernel.d_symm` — basic distance axioms
* `CorrKernel.d_triangle` — triangle inequality from multiplicative condition on `I`
* `CorrKernel.d_pseudometric` — packaging of the pseudometric axioms
* `CorrKernel.d_eq_zero_iff` — upgrade to metric under separating hypothesis
* `CorrKernel.coupling_eq_I` — the coupling `exp(-d)` recovers the kernel `I`
* `CorrKernel.coupling_anti` — interaction strength decreases with emergent distance
* `CorrKernel.recovery` — if `I` comes from Euclidean distances, `d` recovers them exactly
-/

noncomputable section

open Real

/-! ## Correlation Kernel and Emergent Distance -/

/-- A correlation kernel on a finite type `S`. -/
structure CorrKernel (S : Type*) [Fintype S] [DecidableEq S] where
  I : S → S → ℝ
  symm : ∀ i j, I i j = I j i
  pos : ∀ i j, 0 < I i j
  le_one : ∀ i j, I i j ≤ 1
  diag : ∀ i, I i i = 1

namespace CorrKernel

variable {S : Type*} [Fintype S] [DecidableEq S] (K : CorrKernel S)

/-- The emergent distance induced by a correlation kernel. -/
def d (i j : S) : ℝ := -Real.log (K.I i j)

/-! ## Basic Distance Properties -/

theorem d_nonneg (i j : S) : 0 ≤ K.d i j :=
  neg_nonneg_of_nonpos (Real.log_nonpos (le_of_lt (K.pos i j)) (K.le_one i j))

theorem d_self (i : S) : K.d i i = 0 := by
  simp [CorrKernel.d, K.diag]

theorem d_symm (i j : S) : K.d i j = K.d j i := by
  rw [CorrKernel.d, CorrKernel.d]; simp [CorrKernel.symm]

/-! ## Triangle Inequality -/

/-- A correlation kernel satisfies the multiplicative triangle inequality. -/
def MultTriangle (K : CorrKernel S) : Prop :=
  ∀ i j k, K.I i k ≥ K.I i j * K.I j k

/-- If `I i k ≥ I i j * I j k` for all triples, the emergent distance
    satisfies the triangle inequality. -/
theorem d_triangle (h : K.MultTriangle) (i j k : S) :
    K.d i k ≤ K.d i j + K.d j k := by
  unfold CorrKernel.d
  linarith [Real.log_le_log (mul_pos (K.pos i j) (K.pos j k)) (h i j k),
            Real.log_mul (ne_of_gt (K.pos i j)) (ne_of_gt (K.pos j k))]

/-! ## Pseudometric and Metric -/

/-- The emergent distance forms a pseudometric when the multiplicative
    triangle inequality holds. -/
theorem d_pseudometric (h : K.MultTriangle) :
    ∀ i j k, 0 ≤ K.d i j ∧ K.d i i = 0 ∧ K.d i j = K.d j i ∧
      K.d i k ≤ K.d i j + K.d j k :=
  fun i j k => ⟨K.d_nonneg i j, K.d_self i, K.d_symm i j, K.d_triangle h i j k⟩

/-- A correlation kernel is separating if `I i j = 1 ↔ i = j`. -/
def Separating (K : CorrKernel S) : Prop :=
  ∀ i j, K.I i j = 1 ↔ i = j

/-- Under the separating condition, `d i j = 0 ↔ i = j`,
    upgrading the pseudometric to a metric. -/
theorem d_eq_zero_iff (hsep : K.Separating) (i j : S) :
    K.d i j = 0 ↔ i = j := by
  simp [CorrKernel.d]
  exact ⟨fun h => (hsep i j).1 (h.elim (fun h => by linarith [K.pos i j])
    fun h => h.elim (fun h => by linarith [K.pos i j])
      fun h => by linarith [K.pos i j]),
    fun h => Or.inr <| Or.inl <| (hsep i j).2 h⟩

/-! ## Coupling and Locality -/

/-- The coupling strength between two nodes. -/
def coupling (i j : S) : ℝ := Real.exp (-K.d i j)

/-- Coupling equals the original correlation: `exp(-d i j) = I i j`. -/
theorem coupling_eq_I (i j : S) : K.coupling i j = K.I i j := by
  unfold CorrKernel.coupling CorrKernel.d
  rw [neg_neg, Real.exp_log (K.pos i j)]

/-- Coupling is strictly positive. -/
theorem coupling_pos (i j : S) : 0 < K.coupling i j :=
  Real.exp_pos _

/-- Coupling is at most 1. -/
theorem coupling_le_one (i j : S) : K.coupling i j ≤ 1 := by
  rw [K.coupling_eq_I]; exact K.le_one i j

/-- Interaction strength decreases as emergent distance increases:
    if `d i j ≤ d i' j'` then `coupling i' j' ≤ coupling i j`. -/
theorem coupling_anti (i j i' j' : S)
    (hle : K.d i j ≤ K.d i' j') :
    K.coupling i' j' ≤ K.coupling i j := by
  exact Real.exp_le_exp.mpr (neg_le_neg hle)

/-! ## Recovery of Euclidean Geometry -/

/-- If the kernel arises from Euclidean distances via `I i j = exp(-‖x i - x j‖)`,
    then the emergent metric recovers the Euclidean distance exactly. -/
theorem recovery {n : ℕ} (x : S → EuclideanSpace ℝ (Fin n))
    (hI : ∀ i j, K.I i j = Real.exp (-‖x i - x j‖)) (i j : S) :
    K.d i j = ‖x i - x j‖ := by
  unfold CorrKernel.d; simp [hI]

end CorrKernel
end
