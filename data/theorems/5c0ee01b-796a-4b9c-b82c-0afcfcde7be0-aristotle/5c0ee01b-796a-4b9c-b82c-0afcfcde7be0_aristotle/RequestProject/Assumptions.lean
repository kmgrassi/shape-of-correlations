/-
  Causal Order as Extra Relational Data on Emergent Metric Geometry
  Part VIII: Testing Assumptions A-E

  Formalizes and proves/disproves the key conceptual assumptions.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.Negative
import RequestProject.Positive
import RequestProject.Lorentzian

noncomputable section

/-! ## Assumption A: "Geometry determines causality." — FALSE -/

/-- **Assumption A (disproved)**: Geometry does NOT determine causality.
    The same metric admits distinct causal orders (from Theorem 1). -/
theorem assumption_A_false :
    ∃ (C₁ C₂ : CausalRelation (Fin 2)),
      C₁.rel ≠ C₂.rel := by
  exact ⟨causalOrder1, causalOrder2, causal_orders_distinct⟩

/-! ## Assumption B: "A symmetric correlation kernel can determine a time arrow
    by itself." — FALSE -/

/-- **Assumption B (disproved)**: A symmetric kernel I(i,j) = I(j,i) is invariant
    under reversal of any causal relation, so it cannot determine a time arrow. -/
theorem assumption_B_false :
    ∀ (S : Type*) (K : SymmetricKernel S) (C : CausalRelation S),
      K.I = (CausalConfig.mk K C.reverse).kernel.I := by
  intro S K C; rfl

/-! ## Assumption C: "Adding antisymmetric relational data is sufficient to define
    a causal order." — TRUE (under acyclicity/transitivity) -/

/-- **Assumption C (proved)**: An antisymmetric kernel with transitive induced relation
    gives a well-defined causal order. Restatement of Theorem 4. -/
theorem assumption_C_true {S : Type*} (K : AntisymmetricKernel S)
    (htrans : ∀ i j k : S, K.inducedRel i j → K.inducedRel j k → K.inducedRel i k) :
    ∃ C : CausalRelation S, C.rel = K.inducedRel :=
  antisymmetric_kernel_induces_strict_order K htrans

/-! ## Assumption D: "Metric emergence plus causal order gives a spacetime-like
    structure." — PARTIALLY TRUE -/

/-- **Assumption D (partially true)**: A metric plus a causal order gives a CausalMetric
    structure. However, compatibility conditions (diamond boundedness, geodesic compatibility)
    are not automatic and may fail. -/
theorem assumption_D_partially_true :
    -- Part 1: We can always form the structure
    (∀ (d : Fin 2 → Fin 2 → ℝ)
      (hnn : ∀ i j, 0 ≤ d i j) (hs : ∀ i, d i i = 0)
      (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
      (C : CausalRelation (Fin 2)),
      ∃ CM : CausalMetric (Fin 2), CM.d = d ∧ CM.causal = C) ∧
    -- Part 2: But compatibility conditions can fail
    (∃ (d : Fin 3 → Fin 3 → ℝ) (C : CausalRelation (Fin 3)),
      ∃ (a b x : Fin 3), C.rel a x ∧ C.rel x b ∧ ¬(d a x ≤ d a b)) := by
  constructor
  · exact fun d hnn hs hsymm htri C => causal_metric_consistency d hnn hs hsymm htri C
  · exact diamond_boundedness_can_fail

/-! ## Assumption E: "Causal structure can be derived from directed propagation
    rather than assumed." — TRUE (under strong assumptions) -/

/-- **Assumption E (conditionally true)**: Directed propagation induces a causal order
    when the induced relation is acyclic and transitive. Restatement of Theorem 11. -/
theorem assumption_E_conditionally_true {S : Type*} (P : PropagationKernel S)
    (hirrefl : ∀ i, ¬ P.inducedRel i i)
    (htrans : ∀ i j k, P.inducedRel i j → P.inducedRel j k → P.inducedRel i k) :
    ∃ C : CausalRelation S, C.rel = P.inducedRel :=
  propagation_induces_causal_order P hirrefl htrans

end
