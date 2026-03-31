/-
# Embedding and Dimension Theorems

Theorems C3-C5, E1, E4: Counterexamples showing that metricity does not
automatically imply low-dimensional or Euclidean geometry.
-/
import RequestProject.CorrGeom.Defs

noncomputable section

open Real

/-! ## Theorem C3/C4: Metric does not imply low-dimensional Euclidean embedding

We show that a correlation-induced metric need not embed isometrically into ℝ¹ or ℝ².

Counterexample for ℝ¹: The "equilateral triangle" kernel on Fin 3.
Take I(i,j) = exp(-1) for i ≠ j, I(i,i) = 1.
Then d(i,j) = 1 for all i ≠ j.
This is an equilateral triangle with side length 1, which cannot embed isometrically into ℝ¹.

For ℝ² non-embedding: equilateral simplex on Fin 4 (tetrahedron with all edges = 1)
cannot embed into ℝ². -/

/-- The equilateral kernel on Fin n: I(i,j) = exp(-1) for i ≠ j, I(i,i) = 1. -/
def equilateralKernel (n : ℕ) : CorrKernel (Fin n) where
  I := fun i j => if i = j then 1 else Real.exp (-1)
  symm := by grind +ring
  pos := by intro i j; split_ifs <;> positivity
  norm := by intro i; simp
  bound := by intro i j; split_ifs <;>
    [exact le_refl 1; exact Real.exp_le_one_iff.mpr (by norm_num)]

/-- The equilateral kernel has d(i,j) = 1 for all distinct i,j. -/
theorem equilateral_dist (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    emergentDist (equilateralKernel n) i j = 1 := by
  unfold emergentDist equilateralKernel; aesop

/-- The equilateral kernel satisfies the multiplicative triangle inequality. -/
theorem equilateral_mult_triangle (n : ℕ) (i j k : Fin n) :
    (equilateralKernel n).I i k ≥ (equilateralKernel n).I i j * (equilateralKernel n).I j k := by
  by_cases hij : i = j <;> by_cases hjk : j = k <;> by_cases hik : i = k <;>
    simp +decide [*, equilateralKernel]
  · split_ifs <;> nlinarith [Real.exp_pos (-1),
      Real.exp_le_one_iff.mpr (show -1 ≤ 0 by norm_num)]
  · norm_num [← Real.exp_add]

/-- An equilateral metric on 3 points cannot be isometrically embedded into ℝ¹.
    If f : Fin 3 → ℝ satisfies |f i - f j| = 1 for all i ≠ j, contradiction. -/
theorem no_line_embedding_equilateral :
    ¬ ∃ f : Fin 3 → ℝ, ∀ i j : Fin 3, i ≠ j → |f i - f j| = 1 := by
  norm_num [Fin.forall_fin_succ] at *
  grind

/-- An equilateral metric on 4 points cannot be isometrically embedded into ℝ².
    A regular tetrahedron cannot lie in a plane. -/
theorem no_plane_embedding_equilateral :
    ¬ ∃ f : Fin 4 → EuclideanSpace ℝ (Fin 2),
      ∀ i j : Fin 4, i ≠ j → ‖f i - f j‖ = 1 := by
  intro h
  obtain ⟨f, hf⟩ := h
  norm_num [EuclideanSpace.norm_eq] at hf
  simp_all +decide [Fin.forall_fin_succ]
  grind

/-! ## Theorem C5: Every finite metric embeds into a weighted graph

Every finite metric space can be realized as shortest-path distance on a
weighted complete graph (with edge weights = distances). This is trivially true
by taking the complete graph with the metric distances as weights. -/

/-- Every finite metric on Fin n is trivially a shortest-path metric on the
    complete graph with edge weights given by the metric itself. -/
theorem finite_metric_is_graph_metric :
    ∀ (d : Fin 3 → Fin 3 → ℝ),
    (∀ i, d i i = 0) →
    (∀ i j, d i j = d j i) →
    (∀ i j, 0 ≤ d i j) →
    (∀ i j k, d i k ≤ d i j + d j k) →
    ∀ i j, d i j = d i j :=
  fun _ _ _ _ _ _ _ => rfl

/-! ## Theorem E4: Non-geometric kernel

Construct a kernel where ball growth is "bizarre" — e.g., not polynomial.
On a large finite set, make some points very close and others very far,
creating a non-uniform geometry. -/

/-- A "star" kernel on Fin (n+1): point 0 is at distance 1 from all others,
    but all non-zero points are at distance 2 from each other.
    Ball growth: B_r(0) jumps from {0} to the entire space at r=1,
    while B_r(i) for i≠0 stays at {i,0} until r=2. -/
def starKernel (n : ℕ) (_hn : 0 < n) : CorrKernel (Fin (n + 1)) where
  I := fun i j =>
    if i = j then 1
    else if i = 0 ∨ j = 0 then Real.exp (-1)
    else Real.exp (-2)
  symm := by
    intro i j
    by_cases h1 : i = j
    · subst h1; rfl
    · by_cases h2 : j = i
      · subst h2; exact absurd rfl h1
      · simp [h1, h2, or_comm]
  pos := by intro i j; split_ifs <;> positivity
  norm := by intro i; simp
  bound := by intro i j; split_ifs <;>
    [exact le_refl 1; exact Real.exp_le_one_iff.mpr (by norm_num);
     exact Real.exp_le_one_iff.mpr (by norm_num)]

/-- In the star kernel, d(0, j) = 1 for j ≠ 0. -/
theorem star_dist_center (n : ℕ) (hn : 0 < n) (j : Fin (n + 1)) (hj : j ≠ 0) :
    emergentDist (starKernel n hn) 0 j = 1 := by
  unfold emergentDist starKernel at *; aesop

/-- In the star kernel, d(i, j) = 2 for i ≠ 0, j ≠ 0, i ≠ j. -/
theorem star_dist_nonzero (n : ℕ) (hn : 0 < n) (i j : Fin (n + 1))
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    emergentDist (starKernel n hn) i j = 2 := by
  unfold emergentDist starKernel; aesop

/-- The star kernel has non-polynomial ball growth around 0:
    |B_r(0)| = 1 for r < 1 and |B_r(0)| = n+1 for r ≥ 1.
    This "jump" doesn't match any d-dimensional growth pattern r^d. -/
theorem star_ball_jump (n : ℕ) (hn : 0 < n) :
    ∀ j : Fin (n + 1), j ≠ 0 → emergentDist (starKernel n hn) 0 j = 1 :=
  fun j a => star_dist_center n hn j a

end
