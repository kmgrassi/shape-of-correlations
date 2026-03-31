/-
# Compatibility with Emergent Metric

Theorems 6-7: Compatibility is not automatic, but finite-speed propagation
implies metric-causal compatibility.
-/
import RequestProject.Diamonds

open Finset BigOperators Real

noncomputable section

/-! ## Theorem 6: Compatibility is not automatic

We construct an explicit counterexample where:
- d is a valid emergent metric (from a correlation kernel)
- ≺_K is a strict partial order from propagation
- but metric boundedness of diamonds fails
-/

/-! ### Counterexample construction

We use S = Fin 3 = {0, 1, 2}.
- Propagation: 0 → 1 → 2 (directed chain), so ≺_K gives 0 ≺ 1 ≺ 2 and 0 ≺ 2.
- Metric: d(0,2) is very small but d(0,1) + d(1,2) is large.
  This violates metric boundedness of diamonds since 1 ∈ ◊(0,2) but d(0,1) > d(0,2).

Concretely:
- I(0,1) = I(1,0) = exp(-10)  (far apart in metric)
- I(1,2) = I(2,1) = exp(-10)  (far apart)
- I(0,2) = I(2,0) = exp(-1)   (close in metric)
- I(i,i) = 1
- d(0,1) = 10, d(1,2) = 10, d(0,2) = 1
- So 1 ∈ ◊(0,2) but d(0,1) = 10 > 1 = d(0,2). Compatibility fails.

We need supermultiplicativity: I(i,k) ≥ I(i,j) * I(j,k).
- I(0,2) = exp(-1) ≥ exp(-10) * exp(-10) = exp(-20). ✓
-/

/-
PROBLEM
Assumption C test: Metric emergence does NOT automatically make causal order compatible.
    There exist a correlation kernel and a propagation kernel where:
    - ≺_K is a strict partial order,
    - but MetricBoundedDiamonds fails.

PROVIDED SOLUTION
Use S = Fin 3 = {0, 1, 2}.

Correlation kernel I:
- I(i,i) = 1 for all i
- I(0,1) = I(1,0) = exp(-10)
- I(1,2) = I(2,1) = exp(-10)
- I(0,2) = I(2,0) = exp(-1)
This gives d(0,1) = 10, d(1,2) = 10, d(0,2) = 1.
Supermultiplicativity: I(i,k) ≥ I(i,j)*I(j,k).
- I(0,2) = exp(-1) ≥ exp(-10)*exp(-10) = exp(-20) ✓
- I(0,1) = exp(-10) ≥ I(0,k)*I(k,1) for all k: worst case k=2, I(0,2)*I(2,1) = exp(-1)*exp(-10) = exp(-11) ≤ exp(-10) ✓
- All other cases similar.

Propagation kernel: use the chain propagation on Fin 3 (chainPropKernel 2).
This gives causal 0→1, 1→2, 0→2. It's acyclic.

Diamond ◊(0,2) = {x : causal 0 x ∧ causal x 2} = {1} (since causal 0 1 and causal 1 2).

MetricBoundedDiamonds requires d(0,1) ≤ d(0,2), i.e. 10 ≤ 1, which is FALSE.

So MetricBoundedDiamonds fails.

The actual construction in Lean: define the correlation kernel on Fin 3 with the given I function, and use chainPropKernel 2 for propagation. Show acyclicity (chain_acyclic), then show MetricBoundedDiamonds is false by exhibiting x = 1 ∈ diamond(0,2) with d(0,1) > d(0,2).
-/
theorem assumption_C_false :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (C : CorrelationKernel S) (P : PropagationKernel S),
      P.Acyclic ∧ ¬MetricBoundedDiamonds C P := by
        by_contra h;
        obtain ⟨C, P, hP_acyclic, hP_not_metric_bounded⟩ : ∃ (C : CorrelationKernel (Fin 3)) (P : PropagationKernel (Fin 3)), P.Acyclic ∧ ¬MetricBoundedDiamonds C P := by
          -- Define the correlation kernel C on Fin 3 with the given I function.
          set C : CorrelationKernel (Fin 3) := {
            I := fun i j => if i = j then 1 else if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 then Real.exp (-10) else if i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1 then Real.exp (-10) else Real.exp (-1),
            pos := by
              exact fun i j => by split_ifs <;> positivity;,
            le_one := by
              exact fun i j => by split_ifs <;> norm_num [ Real.exp_le_one_iff ] ;,
            diag := by
              simp +decide,
            symm := by
              simp +decide [ Fin.forall_fin_succ ],
            supermul := by
              simp +decide [ Fin.forall_fin_succ ];
              norm_num [ ← Real.exp_add ]
          };
          refine' ⟨ C, _, _, _ ⟩;
          refine' ⟨ fun t i j => if i.val + t = j.val then 1 else 0, _, _, _ ⟩ <;> simp +decide [ PropagationKernel.Acyclic ];
          all_goals norm_cast;
          all_goals norm_num [ MetricBoundedDiamonds ];
          all_goals norm_num [ PropagationKernel.diamond, PropagationKernel.causal ];
          all_goals norm_num [ Fin.forall_fin_succ, Fin.exists_fin_succ, PropagationKernel.Acyclic ];
          · rintro ( _ | _ | t ) ( _ | _ | s ) <;> simp +arith +decide [ Fin.sum_univ_succ ];
          · exact fun t ht => ne_of_gt ht;
          · simp +decide [ C, CorrelationKernel.d ];
            exact Or.inl <| Or.inr <| Or.inr <| Or.inl ⟨ ⟨ 1, by norm_num ⟩, ⟨ 1, by norm_num ⟩ ⟩;
        exact h ⟨ _, _, _, C, P, hP_acyclic, hP_not_metric_bounded ⟩

/-! ## Theorem 7: Finite-speed propagation implies metric-causal compatibility -/

variable {S : Type*} [Fintype S] [DecidableEq S]
  (C : CorrelationKernel S) (P : PropagationKernel S)

/-
PROBLEM
Under finite-speed propagation, if i ≺_K j via time t,
    then d(i,j) ≤ v * t. In particular, causal influence respects metric cones.

PROVIDED SOLUTION
From hij, get t > 0 with K t i j > 0. From hfs, K t i j > 0 implies d(i,j) ≤ v*t. Return ⟨t, ht_pos, hd⟩.
-/
theorem causal_respects_metric_cones (v : ℝ)
    (hfs : FiniteSpeedPropagation C P v)
    (i j : S) (hij : P.causal i j) :
    ∃ t : ℕ, 0 < t ∧ C.d i j ≤ v * t := by
      exact hij.imp fun t ht => ⟨ ht.1, hfs.2 t i j ht.2 ⟩

/-
PROBLEM
Under finite-speed propagation, causal diamonds are metrically bounded.
    If x ∈ ◊(a,b), there exist witness times t₁, t₂ such that
    d(a,x) ≤ v*t₁ and d(x,b) ≤ v*t₂.

PROVIDED SOLUTION
x ∈ diamond(a,b) means causal a x and causal x b. From causal a x get t1 > 0 with K t1 a x > 0, then d(a,x) ≤ v*t1 by finite speed. From causal x b get t2 > 0 with K t2 x b > 0, then d(x,b) ≤ v*t2. Return ⟨t1, t2, ...⟩.
-/
theorem diamond_metrically_bounded (v : ℝ)
    (hfs : FiniteSpeedPropagation C P v)
    (a b x : S) (hx : x ∈ P.diamond a b) :
    ∃ t₁ t₂ : ℕ, 0 < t₁ ∧ 0 < t₂ ∧ C.d a x ≤ v * t₁ ∧ C.d x b ≤ v * t₂ := by
      -- By definition of causal, there exist t₁ and t₂ such that t₁ > 0, P.K t₁ a x > 0, and t₂ > 0, P.K t₂ x b > 0.
      obtain ⟨t₁, ht₁_pos, ht₁⟩ : ∃ t₁ : ℕ, 0 < t₁ ∧ 0 < P.K t₁ a x := by
        exact hx.1
      obtain ⟨t₂, ht₂_pos, ht₂⟩ : ∃ t₂ : ℕ, 0 < t₂ ∧ 0 < P.K t₂ x b := by
        exact hx.2;
      exact ⟨ t₁, t₂, ht₁_pos, ht₂_pos, hfs.2 t₁ a x ht₁, hfs.2 t₂ x b ht₂ ⟩

/-- Assumption D test: Finite propagation speed IS sufficient for metric-causal compatibility
    (in the sense that causal influence respects metric cones). -/
theorem assumption_D_true (v : ℝ)
    (hfs : FiniteSpeedPropagation C P v)
    (i j : S) (hij : P.causal i j) :
    ∃ t : ℕ, 0 < t ∧ C.d i j ≤ v * t :=
  causal_respects_metric_cones C P v hfs i j hij