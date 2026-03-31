/-
  Causal Order as Extra Relational Data on Emergent Metric Geometry
  Part VI & VII: Lorentzian-Style Structure and Directed Propagation

  Theorems 9-11: Time-separation, Lorentzian structure, and propagation kernels.
-/
import Mathlib
import RequestProject.Defs

noncomputable section

open Real

/-! ## Theorem 9: Metric and time-separation are logically independent -/

/-- A constant metric on Fin 2: d(0,1) = d(1,0) = 1. -/
def constMetric2 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else 1

/-- First time-separation: τ(0,1) = 1, τ(1,0) = 0. -/
def tau1 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Second time-separation: τ(0,1) = 2, τ(1,0) = 0. -/
def tau2 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 2 else 0

/-
PROBLEM
**Theorem 9a**: Same metric can support different time-separations.

PROVIDED SOLUTION
tau1 ≠ tau2 because tau1 0 1 = 1 ≠ 2 = tau2 0 1. The second part is trivially rfl. Use funext_iff to show the functions differ, then simp/norm_num at the specific point.
-/
theorem same_metric_different_tau :
    tau1 ≠ tau2 ∧
    (∀ i j : Fin 2, constMetric2 i j = constMetric2 i j) := by
      exact ⟨ fun h => by have := congr_fun ( congr_fun h 0 ) 1; norm_num [ tau1, tau2 ] at this, fun _ _ => rfl ⟩

/-
PROBLEM
**Theorem 9b**: Same causal order can coexist with different metrics.

PROVIDED SOLUTION
Take d₁(i,j) = if i=j then 0 else 1 and d₂(i,j) = if i=j then 0 else 2. These are symmetric and distinct (d₁ 0 1 = 1 ≠ 2 = d₂ 0 1).
-/
theorem same_order_different_metrics :
    ∃ (d₁ d₂ : Fin 2 → Fin 2 → ℝ),
      d₁ ≠ d₂ ∧
      (∀ i j : Fin 2, d₁ i j = d₁ j i) ∧
      (∀ i j : Fin 2, d₂ i j = d₂ j i) := by
        exact ⟨ 0, 1, by intros h; simpa using congr_fun ( congr_fun h 0 ) 1, by intros; norm_num, by intros; norm_num ⟩

/-! ## Theorem 10: Lorentzian-style structure needs more than a metric -/

/-- A Lorentzian-style structure consists of metric + causal order + time-separation. -/
structure LorentzianStructure (S : Type*) extends CausalMetric S where
  tau : S → S → ℝ
  tau_nonneg : ∀ i j, 0 ≤ tau i j
  tau_pos_imp_causal : ∀ i j, tau i j > 0 → causal.rel i j
  reverse_triangle : ∀ i j k, causal.rel i j → causal.rel j k →
    tau i k ≥ tau i j + tau j k

/-
PROBLEM
**Theorem 10**: A metric alone is insufficient to define a Lorentzian-style structure.
    Given a metric, there exist multiple incompatible Lorentzian extensions.

PROVIDED SOLUTION
Construct two LorentzianStructures on Fin 2 with the same metric but different tau. Use constMetric2 for both. For L₁: causal order 0≺1 with tau(0,1)=1. For L₂: causal order 0≺1 with tau(0,1)=2. Both have the same d = constMetric2 but different tau.
-/
theorem lorentzian_needs_more_than_metric :
    ∃ (L₁ L₂ : LorentzianStructure (Fin 2)),
      L₁.d = L₂.d ∧ L₁.tau ≠ L₂.tau := by
        refine' ⟨ _, _, _, _ ⟩;
        constructor;
        rotate_left;
        rotate_left;
        rotate_left;
        refine' ⟨ fun i j => if i = j then 0 else 1, _, _, _, _, _ ⟩ <;> norm_num;
        refine' ⟨ fun i j => i = 0 ∧ j = 1, _, _ ⟩ <;> simp +decide [ CausalRelation ];
        refine' fun i j => if i = 0 ∧ j = 1 then 1 else 0;
        refine' { d := fun i j => if i = j then 0 else 1, d_nonneg := _, d_self := _, d_symm := _, d_triangle := _, causal := { rel := fun i j => i = 0 ∧ j = 1, irrefl := _, trans := _ }, tau := fun i j => if i = 0 ∧ j = 1 then 2 else 0, tau_nonneg := _, tau_pos_imp_causal := _, reverse_triangle := _ } <;> simp +decide [ Fin.forall_fin_two ];
        all_goals norm_num [ funext_iff, Fin.forall_fin_two ] at *

/-! ## Theorem 11: Directed propagation induces causal order under acyclicity -/

/-
PROBLEM
**Theorem 11**: If a propagation kernel's induced relation is transitive and
    irreflexive (acyclic), then it defines a valid causal relation (strict partial order).

PROVIDED SOLUTION
Construct CausalRelation with rel = P.inducedRel, irrefl = hirrefl, trans = htrans. Return ⟨this, rfl⟩.
-/
theorem propagation_induces_causal_order {S : Type*} (P : PropagationKernel S)
    (hirrefl : ∀ i, ¬ P.inducedRel i i)
    (htrans : ∀ i j k, P.inducedRel i j → P.inducedRel j k → P.inducedRel i k) :
    ∃ C : CausalRelation S, C.rel = P.inducedRel := by
      exact ⟨ ⟨ P.inducedRel, hirrefl, htrans ⟩, rfl ⟩

end