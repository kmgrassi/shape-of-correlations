/-
# Emergent Space from Correlations

Formalization of the idea that spatial geometry can emerge from correlation
structure on an abstract set of degrees of freedom.

Given a set S of degrees of freedom with a correlation function
  corr : S → S → ℝ
satisfying certain axioms, we define a distance
  d(i,j) = -log(corr(i,j))
and prove it yields a pseudometric (and, with an additional separation axiom, a metric).

We then define locality and interaction strength, showing that interaction
strength is a decreasing function of the emergent distance.
-/

import Mathlib

open Real

noncomputable section

/-! ## Correlation Structure -/

/-- A `CorrStructure` on a type `S` packages a correlation function with
the axioms that make `-log ∘ corr` a pseudometric. -/
structure CorrStructure (S : Type*) where
  /-- Correlation between degrees of freedom, valued in (0, 1]. -/
  corr : S → S → ℝ
  /-- Correlations are strictly positive. -/
  corr_pos : ∀ i j, 0 < corr i j
  /-- Correlations are at most 1. -/
  corr_le_one : ∀ i j, corr i j ≤ 1
  /-- Self-correlation is maximal. -/
  corr_self : ∀ i, corr i i = 1
  /-- Correlation is symmetric. -/
  corr_symm : ∀ i j, corr i j = corr j i
  /-- Submultiplicativity: the key axiom that yields the triangle inequality. -/
  corr_submul : ∀ i j k, corr i k * corr k j ≤ corr i j

namespace CorrStructure

variable {S : Type*} (C : CorrStructure S)

/-! ## Emergent Distance -/

/-- The emergent distance: `d(i,j) = -log(corr(i,j))`. -/
def dist (i j : S) : ℝ := -Real.log (C.corr i j)

/-- The emergent distance is nonneg (since `corr ≤ 1` implies `log ≤ 0`). -/
theorem dist_nonneg (i j : S) : 0 ≤ C.dist i j :=
  neg_nonneg.2 (Real.log_nonpos (C.corr_pos i j |> le_of_lt) (C.corr_le_one i j))

/-- `d(i,i) = 0`. -/
theorem dist_self (i : S) : C.dist i i = 0 := by
  unfold dist; rw [C.corr_self i]; simp

/-- Symmetry of the emergent distance. -/
theorem dist_symm (i j : S) : C.dist i j = C.dist j i := by
  rw [dist, dist, C.corr_symm]

/-- Triangle inequality for the emergent distance.
  Equivalent to submultiplicativity of `corr` under `-log`. -/
theorem dist_triangle (i j k : S) : C.dist i j ≤ C.dist i k + C.dist k j := by
  unfold dist
  rw [← neg_add,
    ← Real.log_mul (ne_of_gt <| C.corr_pos _ _) (ne_of_gt <| C.corr_pos _ _)]
  exact neg_le_neg
    (Real.log_le_log (mul_pos (C.corr_pos _ _) (C.corr_pos _ _)) (C.corr_submul _ _ _))

/-- The emergent distance satisfies all pseudometric axioms:
  `dist_nonneg`, `dist_self`, `dist_symm`, `dist_triangle`. -/
theorem pseudometric_axioms :
    (∀ i j, 0 ≤ C.dist i j) ∧
    (∀ i, C.dist i i = 0) ∧
    (∀ i j, C.dist i j = C.dist j i) ∧
    (∀ i j k, C.dist i j ≤ C.dist i k + C.dist k j) :=
  ⟨C.dist_nonneg, C.dist_self, C.dist_symm, C.dist_triangle⟩

/-! ## Metric Upgrade -/

/-- A correlation structure is *separating* if maximal correlation implies identity. -/
def IsSeparating : Prop := ∀ i j, C.corr i j = 1 → i = j

/-- If `corr(i,j) = 1 → i = j`, then `d(i,j) = 0 ↔ i = j`. -/
theorem dist_eq_zero_iff_eq (hsep : C.IsSeparating) (i j : S) :
    C.dist i j = 0 ↔ i = j := by
  constructor
  · intro h
    have : C.corr i j = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (C.corr_pos i j) (neg_eq_zero.mp h)
    exact hsep i j this
  · rintro rfl; exact dist_self _ _

/-! ## Interaction Strength and Locality -/

/-- Interaction strength as a function of correlation: any monotone
    increasing function `f` applied to the correlation value. -/
def interactionStrength (f : ℝ → ℝ) (i j : S) : ℝ := f (C.corr i j)

/-- Two degrees of freedom are `ε`-local if their emergent distance is at most `ε`. -/
def IsLocal (ε : ℝ) (i j : S) : Prop := C.dist i j ≤ ε

/-- `ε`-locality is equivalent to correlation being at least `exp(-ε)`. -/
theorem isLocal_iff_corr_ge (ε : ℝ) (i j : S) :
    C.IsLocal ε i j ↔ Real.exp (-ε) ≤ C.corr i j := by
  unfold IsLocal
  rw [← Real.log_le_log_iff (Real.exp_pos _) (C.corr_pos i j), Real.log_exp]
  unfold dist; constructor <;> intro h <;> linarith

/-- Interaction strength (via a monotone `f`) decreases with emergent distance. -/
theorem interaction_decreases_with_distance
    {f : ℝ → ℝ} (hf : Monotone f)
    {i j j' : S} (hd : C.dist i j ≤ C.dist i j') :
    C.interactionStrength f i j' ≤ C.interactionStrength f i j := by
  unfold interactionStrength dist at *
  exact hf (by rw [neg_le_neg_iff, Real.log_le_log_iff] at hd
               <;> linarith [C.corr_pos i j, C.corr_pos i j'])

/-! ## Exponential Decay -/

/-- With exponential interaction `J(i,j) = exp(-α · d(i,j))` for `α > 0`,
    the interaction equals `corr(i,j) ^ α`. -/
theorem exp_interaction_eq_corr_pow (α : ℝ) (i j : S) :
    Real.exp (-α * C.dist i j) = C.corr i j ^ α := by
  rw [Real.rpow_def_of_pos (C.corr_pos i j)]
  unfold dist; ring_nf

/-! ## Metric Embedding -/

/-- A map `φ : S → (Fin n → ℝ)` is a `(1+ε)`-distortion embedding of the
    emergent metric into `ℝ^n` if distances are preserved up to factor `(1+ε)`. -/
def IsLowDistortionEmbedding (φ : S → (Fin n → ℝ)) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ i j,
    C.dist i j ≤ ‖φ i - φ j‖ ∧
    ‖φ i - φ j‖ ≤ (1 + ε) * C.dist i j

/-- If a low-distortion embedding exists, then `ε`-local degrees of freedom
    map to Euclidean-nearby points: `‖φ i - φ j‖ ≤ (1+ε) * δ`.
    This is the formal statement of "space lives inside the wave." -/
theorem embedding_preserves_locality
    {φ : S → (Fin n → ℝ)} {ε δ : ℝ}
    (hemb : C.IsLowDistortionEmbedding φ ε)
    {i j : S} (hloc : C.IsLocal δ i j) :
    ‖φ i - φ j‖ ≤ (1 + ε) * δ :=
  le_trans (hemb.2 i j |>.2) (mul_le_mul_of_nonneg_left hloc (by linarith [hemb.1]))

end CorrStructure

end
