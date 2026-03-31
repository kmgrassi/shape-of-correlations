/-
# Wave-First Quantum Theory: Observer Measure Theorems

## Theorem 14: Infinite support with finite measure (summable weights)
## Theorem 15: Finite base measure but divergent observer measure
## Theorem 16: Finite observer measure iff bounded observer content
-/
import Mathlib

open scoped NNReal ENNReal

/-! ## Theorem 14: Infinite support does not imply pathological measure

An infinite family of configurations can still define finite total
observer-measure if the weights are summable.

Example: μ(n) = 2⁻ⁿ, w(n) = 1, then ∑ μ(n) w(n) < ∞. -/

noncomputable def mu14 : ℕ → ℝ := fun n => (1 / 2) ^ n
noncomputable def w14 : ℕ → ℝ := fun _ => 1

theorem infinite_support_finite_measure :
    Summable (fun n => mu14 n * w14 n) := by
  unfold mu14 w14
  simpa using summable_geometric_two

theorem infinite_support_finite_measure_value :
    HasSum (fun n => mu14 n * w14 n) 2 := by
  convert hasSum_geometric_two using 1; unfold mu14 w14; aesop

/-! ## Theorem 15: Divergence from observer content growth

Even finite or summable base measure can yield divergent observer
measure if observer-weight grows too fast.

Example: μ(n) = 2⁻ⁿ, w(n) = 2ⁿ, then ∑ μ(n) < ∞ but ∑ μ(n)w(n) = ∞. -/

noncomputable def mu15 : ℕ → ℝ := fun n => (1 / 2) ^ n
noncomputable def w15 : ℕ → ℝ := fun n => (2 : ℝ) ^ n

theorem base_measure_summable :
    Summable mu15 := by
  exact summable_geometric_two

theorem observer_measure_diverges :
    ¬ Summable (fun n => mu15 n * w15 n) := by
  unfold mu15 w15
  norm_num [← mul_pow]
  norm_num [summable_const_iff]

/-! ## Theorem 16: Finite observer measure iff bounded observer content

For all finite (summable) configuration measures μ, finiteness of the
observer-measure ∑ μ(n) w(n) is equivalent to w being bounded.

Forward direction: if w is bounded, then μ summable implies μ·w summable.
Backward direction (contrapositive): if w is unbounded, there exists a
summable μ such that μ·w is not summable. -/

/-- Forward direction: bounded observer content implies finite observer measure. -/
theorem bounded_weight_implies_finite_observer_measure
    (μ w : ℕ → ℝ) (hμ_nn : ∀ n, 0 ≤ μ n) (hμ_sum : Summable μ)
    (hw_nn : ∀ n, 0 ≤ w n) (C : ℝ) (hw_bdd : ∀ n, w n ≤ C) :
    Summable (fun n => μ n * w n) := by
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (hμ_nn n) (hw_nn n))
    (fun n => mul_le_mul_of_nonneg_left (hw_bdd n) (hμ_nn n)) (hμ_sum.mul_right C)

/-- Backward direction (contrapositive): unbounded observer content means there exists
    a summable configuration measure whose observer measure diverges. -/
theorem unbounded_weight_divergent_observer_measure
    (w : ℕ → ℝ) (hw_nn : ∀ n, 0 ≤ w n)
    (hw_unbdd : ∀ C : ℝ, ∃ n, w n > C) :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧ Summable μ ∧ ¬ Summable (fun n => μ n * w n) := by
  obtain ⟨n_k, hn_k⟩ : ∃ n_k : ℕ → ℕ, StrictMono n_k ∧ ∀ k, w (n_k k) > k := by
    have h_seq : ∀ k, ∃ n > k, w n > k := by
      contrapose! hw_unbdd
      exact ⟨ Max.max ( ∑ n ∈ Finset.range ( hw_unbdd.choose + 1 ), w n ) ( hw_unbdd.choose : ℝ ), fun n => if hn : n ≤ hw_unbdd.choose then Finset.single_le_sum ( fun a _ => hw_nn a ) ( Finset.mem_range_succ_iff.mpr hn ) |> le_trans <| le_max_left _ _ else le_trans ( hw_unbdd.choose_spec n <| not_le.mp hn ) <| le_max_right _ _ ⟩
    choose f hf using h_seq
    use fun k => Nat.recOn k ( f 0 ) fun k ih => f ( ih + 1 )
    refine' ⟨ strictMono_nat_of_lt_succ _, fun k => _ ⟩
    · grind
    · induction' k with k ih
      · simpa using hf 0 |>.2
      · exact lt_of_le_of_lt ( mod_cast by linarith [ hf ( Nat.rec ( f 0 ) ( fun k ih => f ( ih + 1 ) ) k + 1 ), show Nat.rec ( f 0 ) ( fun k ih => f ( ih + 1 ) ) k ≥ k from Nat.recOn k ( by linarith [ hf 0 ] ) fun k ih => by linarith [ hf ( Nat.rec ( f 0 ) ( fun k ih => f ( ih + 1 ) ) k + 1 ) ] ] ) ( hf _ |>.2 )
  set μ : ℕ → ℝ := fun n => ∑' k, if n = n_k k then (1 / (k + 1 : ℝ) ^ 2) else 0
  use μ
  refine' ⟨ fun n => tsum_nonneg fun k => by positivity, _, _ ⟩
  · have h_summable : Summable (fun k : ℕ => (1 / (k + 1 : ℝ) ^ 2)) := by
      simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two
    refine' summable_of_sum_le _ _
    exact ∑' k : ℕ, ( 1 / ( k + 1 : ℝ ) ^ 2 )
    · exact fun n => tsum_nonneg fun k => by positivity
    · intro u; rw [ Finset.sum_congr rfl fun x hx => tsum_eq_sum <| ?_ ]
      rotate_left
      use fun x => Finset.filter ( fun k => x = n_k k ) ( Finset.range ( u.sup id + 1 ) )
      · simp +zetaDelta at *
        exact fun k hk₁ hk₂ => False.elim <| hk₁ ( Finset.le_sup ( f := id ) hx |> le_trans ( hk₂.symm ▸ hn_k.1.id_le _ ) ) hk₂
      · refine' le_trans _ ( Summable.sum_le_tsum ( Finset.range ( u.sup id + 1 ) ) ( fun _ _ => by positivity ) h_summable )
        rw [ Finset.sum_sigma' ]
        refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) _
        exact Finset.image ( fun k => ⟨ n_k k, k ⟩ ) ( Finset.range ( u.sup id + 1 ) )
        · intro x hx; aesop
        · exact fun _ _ _ => by positivity
        · rw [ Finset.sum_image ] <;> aesop
  · have h_sum : ¬ Summable (fun k => (w (n_k k)) / (k + 1 : ℝ) ^ 2) := by
      suffices h_comp : ¬ Summable (fun k : ℕ => (k : ℝ) / (k + 1) ^ 2) by
        exact fun h => h_comp <| h.of_nonneg_of_le ( fun k => by positivity ) fun k => by gcongr ; linarith [ hn_k.2 k ]
      have h_harmonic : ∀ k : ℕ, (k : ℝ) / (k + 1) ^ 2 ≥ 1 / (4 * k) := by
        rintro ( _ | _ | k ) <;> norm_num
        rw [ inv_mul_eq_div, div_le_div_iff₀ ] <;> ring <;> nlinarith
      exact fun h => absurd ( h.of_nonneg_of_le ( fun k => by positivity ) h_harmonic ) ( by simpa [ summable_mul_right_iff ] using Real.not_summable_natCast_inv )
    contrapose! h_sum
    convert h_sum.comp_injective hn_k.1.injective using 1
    ext k; simp [μ]
    rw [ tsum_eq_single k ] <;> simp +contextual [ hn_k.1.injective.eq_iff ] ; ring
    grind
