/-
# Graph-Based Kernel Realizations

We show two concrete ways to build a correlation kernel from a weighted graph:

1. **Shortest-path kernel**: Given positive edge weights c(i,j), define
   D(i,j) = shortest weighted path from i to j, and I(i,j) = e^{-D(i,j)}.
   This recovers the correlation-kernel framework.

2. **Max-product path kernel**: Given edge weights w(i,j) ∈ (0,1], define
   I(i,j) = max over paths of the product of edge weights.
   This is supermultiplicative by path concatenation.

Both yield pseudometrics via KernelMetric.
-/
import Mathlib
import RequestProject.KernelMetric

open Real

noncomputable section

/-! ## 1. Shortest-path cost → metric (direct) -/

/-- A weighted graph with positive symmetric edge costs and zero self-cost. -/
structure WeightedGraph (V : Type*) [Fintype V] where
  cost : V → V → ℝ
  cost_nonneg : ∀ i j, 0 ≤ cost i j
  cost_self : ∀ i, cost i i = 0
  cost_symm : ∀ i j, cost i j = cost j i

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A weighted graph whose edge costs satisfy the triangle inequality
    already defines a pseudometric. -/
structure IsMetricGraph (w : WeightedGraph V) : Prop where
  triangle : ∀ i j k, w.cost i j ≤ w.cost i k + w.cost k j

/-
PROBLEM
From a metric graph, the correlation kernel I(i,j) = e^{-c(i,j)}
    is a valid CorrKernel.

PROVIDED SOLUTION
For I(i,j) = exp(-c(i,j)): I_pos: exp is always positive. I_le_one: c(i,j) ≥ 0, so -c(i,j) ≤ 0, so exp(-c(i,j)) ≤ 1. Use Real.exp_le_one_iff or exp_nonpos_iff. I_self: c(i,i) = 0, so exp(0) = 1. I_symm: c(i,j) = c(j,i) by cost_symm. I_supermult: Need exp(-c(i,k))·exp(-c(k,j)) ≤ exp(-c(i,j)), i.e., exp(-(c(i,k)+c(k,j))) ≤ exp(-c(i,j)). By triangle inequality c(i,j) ≤ c(i,k)+c(k,j), so -c(i,j) ≥ -(c(i,k)+c(k,j)), so exp(-c(i,j)) ≥ exp(-(c(i,k)+c(k,j))). Use Real.exp_add and Real.exp_le_exp (monotonicity of exp).

Need to show exp(-c(i,j)) ≤ 1. Since c(i,j) ≥ 0 (cost_nonneg), -c(i,j) ≤ 0, so exp(-c(i,j)) ≤ exp(0) = 1. Use Real.exp_le_one_iff.mpr or exp_le_one_of_nonpos, or just Real.exp_le_exp.mpr and neg_nonpos.

exp(-c(i,i)) = exp(-0) = exp(0) = 1. Use w.cost_self i and simp.

exp(-c(i,j)) = exp(-c(j,i)) because c(i,j) = c(j,i) by w.cost_symm. Use congr_arg.

Need exp(-c(i,k))·exp(-c(k,j)) ≤ exp(-c(i,j)). The LHS equals exp(-(c(i,k)+c(k,j))) by Real.exp_add. By triangle inequality c(i,j) ≤ c(i,k)+c(k,j), so -(c(i,k)+c(k,j)) ≤ -c(i,j). Since exp is monotone (Real.exp_le_exp), exp(-(c(i,k)+c(k,j))) ≤ exp(-c(i,j)). Combine using ← Real.exp_add.
-/
def toCorrKernel (w : WeightedGraph V) (hw : IsMetricGraph w) :
    CorrKernel V where
  I := fun i j => Real.exp (-w.cost i j)
  I_pos := by
    exact fun i j => Real.exp_pos _
  I_le_one := by
    exact fun i j => Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( w.cost_nonneg i j ) )
  I_self := by
    -- By definition of $w$, we know that $w.cost i i = 0$ for all $i$.
    intros i
    simp [w.cost_self]
  I_symm := by
    exact fun i j => congr_arg Real.exp ( by rw [ w.cost_symm ] )
  I_supermult := by
    exact fun i j k => by rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by linarith [ hw.triangle i j k ] ) ;

/-
PROBLEM
The kernel distance d(i,j) = -log(e^{-c(i,j)}) = c(i,j) recovers
    the original graph cost.

PROVIDED SOLUTION
dist = -log(exp(-c(i,j))) = -(-c(i,j)) = c(i,j). Use Real.log_exp and simplify. Unfold CorrKernel.dist and toCorrKernel.
-/
theorem toCorrKernel_dist_eq (w : WeightedGraph V) (hw : IsMetricGraph w)
    (i j : V) :
    (toCorrKernel w hw).dist i j = w.cost i j := by
      unfold CorrKernel.dist;
      unfold WeightedGraph.toCorrKernel; aesop;

end WeightedGraph

/-! ## 2. Max-product path kernel -/

/-
PROBLEM
Given edge weights in (0,1], the max-product path value from i to j
is supermultiplicative by path concatenation, yielding a CorrKernel.
We axiomatize the max-product kernel by its properties
rather than constructing it explicitly from path enumeration.

A max-product kernel on a weighted graph: the maximal product of edge
    weights along any path from i to j.
    Key property: I(i,j) ≥ I(i,k) · I(k,j) because concatenating the
    optimal i→k path and the optimal k→j path gives a valid i→j path.

PROVIDED SOLUTION
We have all the required properties of a CorrKernel. Construct it as ⟨I, ...⟩ using the given hypotheses. I_pos follows from hI_ge and hw_pos (since w i j ≤ I i j and 0 < w i j). I_le_one is hI_le. I_self is hI_self. I_symm is hI_symm. I_supermult is hI_concat. Return ⟨K, rfl⟩.
-/
theorem maxProduct_is_supermult
    {V : Type*} [Fintype V]
    (w : V → V → ℝ)
    (hw_pos : ∀ i j, 0 < w i j)
    (hw_le : ∀ i j, w i j ≤ 1)
    (hw_self : ∀ i, w i i = 1)
    (hw_symm : ∀ i j, w i j = w j i)
    (I : V → V → ℝ)
    (hI_ge : ∀ i j, w i j ≤ I i j)
    (hI_concat : ∀ i j k, I i k * I k j ≤ I i j)
    (hI_le : ∀ i j, I i j ≤ 1)
    (hI_symm : ∀ i j, I i j = I j i)
    (hI_self : ∀ i, I i i = 1) :
    ∃ K : CorrKernel V, K.I = I := by
      refine' ⟨ _, _ ⟩;
      all_goals try { exact ⟨ I, fun i j => lt_of_lt_of_le ( hw_pos i j ) ( hI_ge i j ), fun i j => hI_le i j, hI_self, hI_symm, hI_concat ⟩ };
      rfl

/-! ## 3. Transfer matrix amplitude -/

/-
PROBLEM
For a substochastic symmetric matrix T on Fin n with spectral radius < 1,
the Green's function G = (I - T)⁻¹ has positive entries, and
G(i,j)² ≤ G(i,i) · G(j,j) by Cauchy-Schwarz on the inner product
⟨e_i, G e_j⟩ where G = G^{1/2} G^{1/2}.

Cauchy-Schwarz bound for the Green's function of a substochastic matrix.
    G(i,j)² ≤ G(i,i) · G(j,j) gives a weaker form of kernel control.

PROVIDED SOLUTION
Since G is positive semidefinite (hG_psd), the bilinear form ⟨x, Gy⟩ = x^T G y is an inner semi-product. Apply Cauchy-Schwarz: (e_i^T G e_j)^2 ≤ (e_i^T G e_i)(e_j^T G e_j). The LHS is G(i,j)^2 and the RHS is G(i,i)·G(j,j).

Formally: use hG_psd to get ∀ x, 0 ≤ star x ⬝ᵥ G.mulVec x. The Cauchy-Schwarz inequality for this form gives (star x ⬝ᵥ G.mulVec y)^2 ≤ (star x ⬝ᵥ G.mulVec x) * (star y ⬝ᵥ G.mulVec y). Specialize to standard basis vectors x = Pi.single i 1, y = Pi.single j 1, and compute that (Pi.single i 1)^T G (Pi.single j 1) = G i j.

Alternative approach: use inner_mul_le_norm_mul_sq or Matrix.PosSemidef properties. Or directly prove by expanding the inequality (G(i,i)·G(j,j) - G(i,j)^2 ≥ 0) using the 2x2 minor determinant being nonneg for PSD matrices.
-/
theorem transfer_cauchy_schwarz_bound
    {n : ℕ} (hn : 0 < n)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hT_symm : T.IsSymm)
    (hT_nonneg : ∀ i j, 0 ≤ T i j)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G = (1 - T)⁻¹)
    (hG_pos : ∀ i j, 0 < G i j)
    (hG_symm : G.IsSymm)
    (hG_psd : G.PosSemidef) :
    ∀ i j, G i j ^ 2 ≤ G i i * G j j := by
      intro i j;
      have := hG_psd.2;
      specialize this ( Finsupp.single i ( G j j ) - Finsupp.single j ( G i j ) ) ; simp_all +decide [ Finsupp.sum_fintype, Matrix.IsSymm ];
      simp_all +decide [ Finsupp.single_apply, Finset.sum_add_distrib, sub_mul, mul_sub, pow_two ];
      simp_all +decide [ ← Matrix.ext_iff ];
      nlinarith [ hG_pos i j, hG_pos j j ]

end