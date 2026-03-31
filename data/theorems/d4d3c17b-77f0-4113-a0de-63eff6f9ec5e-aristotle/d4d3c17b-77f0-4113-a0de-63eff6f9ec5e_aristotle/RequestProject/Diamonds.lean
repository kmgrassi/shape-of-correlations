/-
# Causal Diamonds

Theorems 4-5: Well-definedness of causal diamonds and trivial propagation.
-/
import RequestProject.CoreTheorems

open Finset BigOperators Real

noncomputable section

namespace PropagationKernel

variable {S : Type*} [Fintype S] [DecidableEq S] (P : PropagationKernel S)

/-! ## Theorem 4: Causal diamonds are well-defined -/

/-
PROBLEM
If a does not causally precede b, the diamond is empty.

PROVIDED SOLUTION
If ¬causal a b, and diamond(a,b) is nonempty with some x in it, then causal a x and causal x b hold. By transitivity (causal_trans), causal a b holds, contradiction. So diamond must be empty. Use Set.eq_empty_of_forall_not_mem. For any x, if x ∈ diamond a b then causal a x ∧ causal x b, so by causal_trans we get causal a b, contradicting h.
-/
theorem diamond_empty_of_not_causal (a b : S) (h : ¬P.causal a b) :
    P.diamond a b = ∅ := by
      -- Assume there exists an element x in the diamond. Then by definition, causal a x and causal x b hold.
      by_contra h_nonempty
      obtain ⟨x, hx⟩ : ∃ x, x ∈ P.diamond a b := by
        exact Set.nonempty_iff_ne_empty.2 h_nonempty;
      exact h ( causal_trans P a x b hx.1 hx.2 )

/-
PROBLEM
If ≺_K is a strict partial order, diamonds respect transitivity:
    if x ∈ ◊(a,b) then a ≺ x ≺ b, hence a ≺ b by transitivity.

PROVIDED SOLUTION
If x ∈ diamond(a,b), then causal a x and causal x b. By causal_trans, causal a b.
-/
theorem diamond_implies_causal (a b : S) (x : S)
    (hx : x ∈ P.diamond a b) : P.causal a b := by
      exact P.causal_trans a x b hx.1 hx.2 |> fun ⟨ t, ht, h ⟩ => ⟨ t, ht, h ⟩

/-! ## Theorem 5: Trivial propagation gives trivial diamonds -/

/-- A propagation kernel is trivial if K_t(i,j) = 0 for all i ≠ j and t > 0. -/
def Trivial : Prop :=
  ∀ t : ℕ, 0 < t → ∀ i j : S, i ≠ j → P.K t i j = 0

/-
PROBLEM
Under trivial propagation, no causal relation holds between distinct points.

PROVIDED SOLUTION
Unfold causal: ¬∃ t > 0, K t i j > 0. For any t > 0, since i ≠ j, K t i j = 0 by triviality. So K t i j > 0 is impossible.
-/
theorem trivial_no_causal (htriv : P.Trivial) (i j : S) (hne : i ≠ j) :
    ¬P.causal i j := by
      exact fun ⟨ t, ht, h ⟩ => h.ne' ( htriv t ht i j hne )

/-
PROBLEM
Under trivial acyclic propagation, the causal relation is empty.

PROVIDED SOLUTION
For any i, j: if i = j, use causal_irrefl (from acyclicity). If i ≠ j, use trivial_no_causal. Either way, ¬causal i j.
-/
theorem trivial_acyclic_causal_empty (htriv : P.Trivial) (hacyclic : P.Acyclic) (i j : S) :
    ¬P.causal i j := by
      -- Assume there exists t > 0 such that K t i j > 0.
      by_contra h_contra
      obtain ⟨t, ht_pos, ht_pos_K⟩ : ∃ t > 0, 0 < P.K t i j := by
        exact h_contra;
      by_cases hij : i = j <;> simp_all +decide [ PropagationKernel.Trivial ];
      exact ht_pos_K.ne' ( hacyclic _ _ ht_pos )

/-
PROBLEM
Under trivial acyclic propagation, all diamonds are empty.

PROVIDED SOLUTION
Since causal is empty (trivial_acyclic_causal_empty), in particular ¬causal a b, so diamond_empty_of_not_causal applies. Or directly: for any x, causal a x is false by trivial_acyclic_causal_empty, so x ∉ diamond(a,b).
-/
theorem trivial_acyclic_diamonds_empty (htriv : P.Trivial) (hacyclic : P.Acyclic)
    (a b : S) : P.diamond a b = ∅ := by
      -- Apply the theorem that states the causal relation is empty under trivial acyclic propagation.
      have h_empty : ∀ i j : S, ¬P.causal i j := by
        exact?;
      exact Set.eq_empty_of_forall_notMem fun x hx => h_empty _ _ hx.1

end PropagationKernel