import RequestProject.Defs
import RequestProject.Geometry
import RequestProject.Causality
import RequestProject.Bell

/-!
# Part VI & VIII: Unified Coexistence Theorem and Toy Model

We construct an explicit `RelationalOrigin` on `Fin 4` and prove that
geometry, causality, and Bell-violating no-signaling statistics coexist.
-/

open Real

noncomputable section

/-! ## Toy model construction on Fin 4

  Nodes: 0, 1, 2, 3
  Alice subsystem: {0, 1}, Bob subsystem: {2, 3}
  D(i,j) = if i = j then 0 else 1  (uniform discrete metric)
  τ(i) = i  (time ordering)
  v = 1
  phaseParam = π/4
-/

/-- The uniform discrete metric on Fin 4 -/
def toyD (i j : Fin 4) : ℝ := if i = j then 0 else 1

/-
PROVIDED SOLUTION
Unfold toyD. If i=j then 0 ≥ 0, else 1 ≥ 0.
-/
theorem toyD_nonneg (i j : Fin 4) : 0 ≤ toyD i j := by
  unfold toyD; split_ifs <;> norm_num;

/-
PROVIDED SOLUTION
Unfold toyD, i=i is true so result is 0.
-/
theorem toyD_self (i : Fin 4) : toyD i i = 0 := by
  exact if_pos rfl

/-
PROVIDED SOLUTION
Unfold toyD. If i=j then j=i and both are 0. If i≠j then j≠i and both are 1.
-/
theorem toyD_symm (i j : Fin 4) : toyD i j = toyD j i := by
  unfold toyD; split_ifs <;> tauto;

/-
PROVIDED SOLUTION
Unfold toyD. If i=k then LHS=0, RHS≥0. If i≠k, LHS=1. If i=j then j≠k so RHS=0+1=1. If j=k then i≠j so RHS=1+0=1. If i≠j and j≠k then RHS=1+1=2≥1.
-/
theorem toyD_triangle (i j k : Fin 4) : toyD i k ≤ toyD i j + toyD j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [ toyD ]

/-- The toy relational origin -/
def toyOrigin : RelationalOrigin (Fin 4) where
  D := toyD
  D_nonneg := toyD_nonneg
  D_self := toyD_self
  D_symm := toyD_symm
  D_triangle := toyD_triangle
  τ := fun i => (i : ℝ)
  v := 1
  v_pos := one_pos
  phaseParam := π / 4

/-! ## Theorem 7: Common-origin coexistence theorem -/

/-- d_R is a pseudometric in the toy model -/
theorem toy_pseudometric :
    (∀ i j, 0 ≤ toyOrigin.d_R i j) ∧
    (∀ i, toyOrigin.d_R i i = 0) ∧
    (∀ i j, toyOrigin.d_R i j = toyOrigin.d_R j i) ∧
    (∀ i j k, toyOrigin.d_R i k ≤ toyOrigin.d_R i j + toyOrigin.d_R j k) :=
  d_R_pseudometric toyOrigin

/-
PROBLEM
The toy model has a metric (not just pseudometric)

PROVIDED SOLUTION
By metric_emergence, d_R(i,j) = D(i,j) = toyD(i,j). If toyD(i,j) = 0 then by definition of toyD, i = j. Use metric_emergence and unfold toyD.
-/
theorem toy_metric : ∀ i j : Fin 4, toyOrigin.d_R i j = 0 → i = j := by
  rintro i j h; fin_cases i <;> fin_cases j <;> norm_num [metric_emergence, toyOrigin] at h ⊢;
  all_goals unfold toyD at h; simp +decide at h;

/-- Coupling decreases with distance in the toy model -/
theorem toy_coupling_locality (i j k : Fin 4)
    (h : toyOrigin.d_R i j ≤ toyOrigin.d_R i k) :
    toyOrigin.H_R i k ≤ toyOrigin.H_R i j :=
  coupling_decreases_with_distance toyOrigin i j k h

/-- The causal relation is a strict partial order in the toy model -/
theorem toy_causal_spo :
    (∀ i, ¬toyOrigin.causal i i) ∧
    (∀ i j k, toyOrigin.causal i j → toyOrigin.causal j k → toyOrigin.causal i k) :=
  causal_strict_partial_order toyOrigin

/-- Finite-speed compatibility holds in the toy model -/
theorem toy_finite_speed (i j : Fin 4) (t : ℝ) (ht : 0 < t)
    (hprop : toyOrigin.K_pos t i j) :
    toyOrigin.d_R i j ≤ toyOrigin.v * t :=
  finite_speed_compat toyOrigin i j t ht hprop

/-- The toy model has CHSH = 2√2 > 2 -/
theorem toy_CHSH_violation : toyOrigin.CHSH_val > 2 :=
  CHSH_violation toyOrigin rfl

/-- The toy model satisfies no-signaling -/
theorem toy_no_signaling_alice (a b b' : Fin 2) (x : Bool) :
    toyOrigin.P_Alice a b x = toyOrigin.P_Alice a b' x :=
  no_signaling_alice toyOrigin a b b' x

theorem toy_no_signaling_bob (a a' b : Fin 2) (y : Bool) :
    toyOrigin.P_Bob a b y = toyOrigin.P_Bob a' b y :=
  no_signaling_bob toyOrigin a a' b y

/-
PROBLEM
**Main Coexistence Theorem**: There exists a `RelationalOrigin` such that:
  1. d_R is a metric
  2. Coupling is local (decreases with distance)
  3. Causal relation is a strict partial order
  4. Finite-speed compatibility holds
  5. CHSH > 2 (Bell violation)
  6. No-signaling holds

PROVIDED SOLUTION
Use toyOrigin as witness. All properties follow from previously proved theorems:
1. Metric: d_R_pseudometric toyOrigin + toy_metric
2. Coupling locality: coupling_decreases_with_distance toyOrigin
3. Strict partial order: causal_strict_partial_order toyOrigin
4. Finite-speed: finite_speed_compat toyOrigin
5. CHSH > 2: CHSH_violation toyOrigin rfl
6. No-signaling: no_signaling_alice toyOrigin and no_signaling_bob toyOrigin
-/
theorem common_origin_coexistence :
    ∃ (R : RelationalOrigin (Fin 4)),
      -- 1. Metric
      ((∀ i j, 0 ≤ R.d_R i j) ∧ (∀ i, R.d_R i i = 0) ∧
       (∀ i j, R.d_R i j = R.d_R j i) ∧ (∀ i j k, R.d_R i k ≤ R.d_R i j + R.d_R j k) ∧
       (∀ i j, R.d_R i j = 0 → i = j)) ∧
      -- 2. Coupling locality
      (∀ i j k, R.d_R i j ≤ R.d_R i k → R.H_R i k ≤ R.H_R i j) ∧
      -- 3. Strict partial order
      ((∀ i, ¬R.causal i i) ∧ (∀ i j k, R.causal i j → R.causal j k → R.causal i k)) ∧
      -- 4. Finite-speed compatibility
      (∀ i j t, 0 < t → R.K_pos t i j → R.d_R i j ≤ R.v * t) ∧
      -- 5. Bell CHSH > 2
      R.CHSH_val > 2 ∧
      -- 6. No-signaling
      (∀ a b b' x, R.P_Alice a b x = R.P_Alice a b' x) ∧
      (∀ a a' b y, R.P_Bob a b y = R.P_Bob a' b y) := by
        use toyOrigin;
        refine' ⟨ _, _, _, _, _ ⟩;
        · exact ⟨ toy_pseudometric.1, toy_pseudometric.2.1, toy_pseudometric.2.2.1, toy_pseudometric.2.2.2, toy_metric ⟩;
        · exact?;
        · exact?;
        · exact?;
        · exact ⟨ by exact? , fun a b b' x => by exact? , fun a a' b y => by exact? ⟩

end