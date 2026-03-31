/-
# Frontier Theorems

Theorem 8: Earliest-arrival time and time-separation
Theorem 10: Common-origin compatibility
Assumption E: Geometry and causality from the same structure
-/
import RequestProject.ToyModels

open Finset BigOperators Real

noncomputable section

/-! ## Theorem 8: Earliest-arrival time induces time-separation -/

namespace PropagationKernel

variable {S : Type*} [Fintype S] [DecidableEq S] (P : PropagationKernel S)

/-- If τ(i,j) > 0 (meaning causal relation holds), then i ≺_K j.
    This is immediate from the definition. -/
theorem earliest_arrival_implies_causal (i j : S) (h : P.causal i j) :
    P.causal i j := h

/-
PROBLEM
Subadditivity of earliest arrival: if i ≺ j ≺ k, then
    the earliest arrival from i to k is at most the sum of earliest arrivals.
    This follows from the semigroup law.

PROVIDED SOLUTION
From hij, let t1 = hij.choose with t1 > 0 and K t1 i j > 0. From hjk, let t2 = hjk.choose with t2 > 0 and K t2 j k > 0. By semigroup_term_le, K t1 i j * K t2 j k ≤ K (t1+t2) i k. Since both are positive, K (t1+t2) i k > 0. Also t1+t2 > 0. And t1+t2 ≤ t1+t2 trivially. Use t = t1 + t2.
-/
theorem earliest_arrival_subadditive (i j k : S)
    (hij : P.causal i j) (hjk : P.causal j k) :
    ∃ t : ℕ, 0 < t ∧ 0 < P.K t i k ∧
      t ≤ hij.choose + hjk.choose := by
        refine' ⟨ hij.choose + hjk.choose, _, _, le_rfl ⟩;
        · exact add_pos hij.choose_spec.1 hjk.choose_spec.1;
        · exact lt_of_lt_of_le ( mul_pos hij.choose_spec.2 hjk.choose_spec.2 ) ( P.semigroup_term_le _ _ _ _ _ )

end PropagationKernel

/-! ## Theorem 10: Common-origin compatibility

Both I and K_t are derived from one common cost structure D on edges.
- I(i,j) = exp(-D(i,j))
- K_t supported only on paths of cost ≤ v*t

We show that this yields both metric and causal order with finite-speed compatibility.
-/

/-- A common-origin structure: an edge cost function D on a finite type,
    with I(i,j) = exp(-D(i,j)) and K supported on paths of bounded cost. -/
structure CommonOrigin (S : Type*) [Fintype S] [DecidableEq S] where
  /-- Underlying cost function (serves as a metric) -/
  D : S → S → ℝ
  D_nonneg : ∀ i j, 0 ≤ D i j
  D_self : ∀ i, D i i = 0
  D_symm : ∀ i j, D i j = D j i
  D_triangle : ∀ i j k, D i k ≤ D i j + D j k
  /-- Propagation kernel derived from D -/
  K : ℕ → S → S → ℝ
  K_nonneg : ∀ t i j, 0 ≤ K t i j
  K_identity : ∀ i j, K 0 i j = if i = j then 1 else 0
  K_semigroup : ∀ t s i j, K (t + s) i j = ∑ k : S, K t i k * K s k j
  /-- Speed of propagation -/
  v : ℝ
  v_pos : 0 < v
  /-- Finite speed: propagation only along paths of bounded cost -/
  finite_speed : ∀ t i j, 0 < K t i j → D i j ≤ v * t

namespace CommonOrigin

variable {S : Type*} [Fintype S] [DecidableEq S] (CO : CommonOrigin S)

/-- The correlation kernel derived from the common origin. -/
def corrKernel : CorrelationKernel S where
  I i j := Real.exp (-CO.D i j)
  pos i j := by positivity
  le_one i j := by
    have := CO.D_nonneg i j
    exact Real.exp_le_one_iff.mpr (by linarith)
  diag i := by simp [CO.D_self]
  symm i j := by rw [CO.D_symm]
  supermul i j k := by
    have h := CO.D_triangle i j k
    rw [ge_iff_le, ← Real.exp_add]
    exact Real.exp_le_exp_of_le (by linarith)

/-- The propagation kernel derived from the common origin. -/
def propKernel : PropagationKernel S where
  K := CO.K
  nonneg := CO.K_nonneg
  identity := CO.K_identity
  semigroup := CO.K_semigroup

/-
PROBLEM
The common origin yields finite-speed propagation.

PROVIDED SOLUTION
FiniteSpeedPropagation CO.corrKernel CO.propKernel CO.v means CO.v > 0 and for all t i j, propKernel.K t i j > 0 → corrKernel.d i j ≤ CO.v * t. The first part is CO.v_pos. For the second: propKernel.K = CO.K, so CO.K t i j > 0 implies by CO.finite_speed that D i j ≤ v*t. corrKernel.d i j = -log(exp(-D i j)). Since log(exp(x)) = x for all x (Real.log_exp), -log(exp(-D i j)) = -(-D i j) = D i j. So corrKernel.d i j = D i j ≤ v*t.
-/
theorem finite_speed_propagation :
    FiniteSpeedPropagation CO.corrKernel CO.propKernel CO.v := by
      refine' ⟨ CO.v_pos, _ ⟩;
      intro t i j h_pos
      have h_dist : CO.D i j ≤ CO.v * t := by
        exact?
      simp [h_dist, CommonOrigin.corrKernel];
      unfold CorrelationKernel.d; aesop;

/-
PROBLEM
Assumption E: geometry and causality CAN come from the same structure.

PROVIDED SOLUTION
Construct a trivial CommonOrigin with S = Fin 1, D 0 0 = 0, K t 0 0 = 1, v = 1. Then use finite_speed_propagation to get FiniteSpeedPropagation. Return the corrKernel and propKernel from this CommonOrigin.

Actually, since assumption_E is inside the CommonOrigin namespace with variable CO, we can just use CO.corrKernel, CO.propKernel, CO.v, and CO.finite_speed_propagation (once proved). So just return ⟨S, _, _, CO.corrKernel, CO.propKernel, CO.v, CO.finite_speed_propagation⟩.

Wait, the statement quantifies over new S, so we need to provide witnesses. But we have the current CO. Use S = the current S, etc.
-/
theorem assumption_E :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (C : CorrelationKernel S) (P : PropagationKernel S) (v : ℝ),
      FiniteSpeedPropagation C P v := by
        refine' ⟨ _, _, _, _, _, _ ⟩;
        exact PUnit;
        all_goals try infer_instance;
        refine' ⟨ fun _ _ => 1, _, _, _, _, _ ⟩ <;> norm_num;
        refine' ⟨ fun _ _ _ => 1, _, _, _ ⟩ <;> norm_num;
        exact ⟨ 1, ⟨ by norm_num, fun t i j h => by norm_num [ CorrelationKernel.d ] ⟩ ⟩

end CommonOrigin