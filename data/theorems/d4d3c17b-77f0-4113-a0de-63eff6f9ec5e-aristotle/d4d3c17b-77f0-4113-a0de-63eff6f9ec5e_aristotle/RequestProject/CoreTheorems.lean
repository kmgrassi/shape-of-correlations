/-
# Core Theorems

Theorems 1-3: Irreflexivity, transitivity, and strict partial order
from the propagation kernel.
-/
import RequestProject.Basic

open Finset BigOperators Real

noncomputable section

namespace PropagationKernel

variable {S : Type*} [Fintype S] [DecidableEq S] (P : PropagationKernel S)

/-! ## Theorem 1: Irreflexivity under acyclicity -/

/-
PROBLEM
Under acyclicity, the derived causal relation is irreflexive.

PROVIDED SOLUTION
Unfold causal: ¬(∃ t > 0, K t i i > 0). By acyclicity, K t i i = 0 for all t > 0, so K t i i > 0 is impossible.
-/
theorem causal_irrefl (hacyclic : P.Acyclic) (i : S) : ¬P.causal i i := by
  exact fun ⟨ t, ht, h ⟩ => by linarith [ hacyclic i t ht ] ;

/-! ## Theorem 2: Transitivity from semigroup law -/

/-
PROBLEM
A key lemma: the semigroup sum is at least the single term K_t(i,j) * K_s(j,k).
    This follows because K (t+s) i k = ∑ m, K t i m * K s m k ≥ K t i j * K s j k,
    since all terms are nonneg.

PROVIDED SOLUTION
K(t+s)(i,k) = ∑_m K(t)(i,m) * K(s)(m,k). Each term is nonneg (product of nonneg values). The j-term is K(t)(i,j)*K(s)(j,k). So K(t)(i,j)*K(s)(j,k) ≤ ∑_m .... Use Finset.single_le_sum to extract the j-th term from the sum over all of Finset.univ.
-/
lemma semigroup_term_le (t s : ℕ) (i j k : S) :
    P.K t i j * P.K s j k ≤ P.K (t + s) i k := by
      rw [ P.semigroup ];
      exact Finset.single_le_sum ( fun x _ => mul_nonneg ( P.nonneg t i x ) ( P.nonneg s x k ) ) ( Finset.mem_univ j )

/-
PROBLEM
Under semigroup composition, the causal relation is transitive.

PROVIDED SOLUTION
From hij get t1 > 0, K t1 i j > 0. From hjk get t2 > 0, K t2 j k > 0. Use semigroup_term_le to get K t1 i j * K t2 j k ≤ K (t1+t2) i k. Since both factors are positive, the product is positive, so K(t1+t2)(i,k) > 0. And t1+t2 > 0. Witness t = t1 + t2.
-/
theorem causal_trans (i j k : S) (hij : P.causal i j) (hjk : P.causal j k) :
    P.causal i k := by
      -- By the semigroup law, we have $K_{t_1 + t_2}(i, k) \geq K_{t_1}(i, j) \cdot K_{t_2}(j, k)$.
      have h_semigroup : P.K (hij.choose + hjk.choose) i k ≥ P.K hij.choose i j * P.K hjk.choose j k := by
        apply semigroup_term_le;
      exact ⟨ hij.choose + hjk.choose, add_pos hij.choose_spec.1 hjk.choose_spec.1, lt_of_lt_of_le ( mul_pos hij.choose_spec.2 hjk.choose_spec.2 ) h_semigroup ⟩

/-! ## Theorem 3: Strict partial order -/

/-- Under semigroup composition and acyclicity, the causal relation is a
    strict partial order (irreflexive and transitive). -/
theorem causal_strictPartialOrder (hacyclic : P.Acyclic) :
    IsStrictOrder S P.causal where
  irrefl := P.causal_irrefl hacyclic
  trans _ _ _ := P.causal_trans _ _ _

/-! ## Assumption A test: Propagation support does NOT automatically define causal order
    without acyclicity. We show that without acyclicity, irreflexivity can fail. -/

/-
PROBLEM
Without acyclicity, the causal relation may be reflexive (i.e., not irreflexive).
    This is witnessed by any kernel with K_t(i,i) > 0 for some t > 0.

PROVIDED SOLUTION
Construct S = Fin 1 (a single point), and K t i j = 1 for all t, i, j. Then K satisfies semigroup (sum over single element gives 1*1=1), identity (K 0 i i = 1), nonneg. Then K 1 0 0 = 1 > 0, so causal 0 0 holds (take t=1). Note: the semigroup law K(t+s)(i,j) = ∑_k K(t)(i,k)*K(s)(k,j) = K(t)(i,0)*K(s)(0,j) = 1*1 = 1. Identity: K(0)(i,j) = if i=j then 1 else 0, but with Fin 1, i=j always, so K(0)(i,j)=1. This works.
-/
theorem assumption_A_false :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (P : PropagationKernel S),
      ∃ i : S, P.causal i i := by
        fconstructor;
        exact ULift ( Fin 2 );
        use inferInstance, inferInstance, ⟨ fun t i j => if i = j then 1 else 0, by
          aesop, by
          aesop, by
          aesop ⟩, 0
        generalize_proofs at *;
        exact ⟨ 1, by norm_num, by norm_num ⟩

/-! ## Assumption B test: Semigroup + acyclicity are sufficient for strict partial order -/

/-- Semigroup + acyclicity ⟹ strict partial order. This is Theorem 3 above. -/
theorem assumption_B_true :
    ∀ (S : Type) [Fintype S] [DecidableEq S] (P : PropagationKernel S),
      P.Acyclic → IsStrictOrder S P.causal :=
  fun S _ _ P h => P.causal_strictPartialOrder h

end PropagationKernel