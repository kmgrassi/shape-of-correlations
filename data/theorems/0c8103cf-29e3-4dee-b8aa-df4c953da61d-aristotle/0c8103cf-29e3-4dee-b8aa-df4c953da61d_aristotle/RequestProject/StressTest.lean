import RequestProject.Defs
import RequestProject.Geometry
import RequestProject.Causality
import RequestProject.Bell

/-!
# Part VII: Stress-Testing the Assumptions

We prove/disprove the five key assumptions about the common-origin framework.
-/

open Real

noncomputable section

/-- Helper: the uniform discrete metric on Fin 4 -/
private def uniD (i j : Fin 4) : ℝ := if i = j then 0 else 1

private lemma uniD_nonneg (i j : Fin 4) : 0 ≤ uniD i j := by
  unfold uniD; split <;> linarith

private lemma uniD_self (i : Fin 4) : uniD i i = 0 := by
  unfold uniD; simp

private lemma uniD_symm (i j : Fin 4) : uniD i j = uniD j i := by
  unfold uniD; split <;> split <;> simp_all

private lemma uniD_triangle (i j k : Fin 4) : uniD i k ≤ uniD i j + uniD j k := by
  unfold uniD; split <;> split <;> split <;> simp_all <;> linarith

/-! ## Assumption A: "Geometry + causality ⟹ Bell violation automatically"

Expected: **FALSE**. We exhibit a common-origin structure with valid geometry
and causality but CHSH ≤ 2. -/

/-- A Bell-local relational origin: phaseParam = π/2 gives cos(π/2) = 0 and CHSH = 0 ≤ 2. -/
def bellLocalOrigin : RelationalOrigin (Fin 4) where
  D := uniD
  D_nonneg := uniD_nonneg
  D_self := uniD_self
  D_symm := uniD_symm
  D_triangle := uniD_triangle
  τ := fun i => (i : ℝ)
  v := 1
  v_pos := one_pos
  phaseParam := π / 2

/-
PROBLEM
Assumption A is false: geometry + causality do NOT automatically imply Bell violation

PROVIDED SOLUTION
bellLocalOrigin.phaseParam = π/2. By CHSH_eq_four_cos, CHSH = 4·cos(π/2) = 4·0 = 0 ≤ 2. Use Real.cos_pi_div_two.
-/
theorem assumption_A_false : bellLocalOrigin.CHSH_val ≤ 2 := by
  unfold RelationalOrigin.CHSH_val;
  unfold bellLocalOrigin; norm_num [ RelationalOrigin.E_R ] ;

/-! ## Assumption B: "A common-origin structure can support all three."

Expected: **TRUE**. -/

/-
PROVIDED SOLUTION
Use originA (phaseParam = π/4) as witness. Metric properties from d_R_nonneg, d_R_self. Causal irreflexivity from causal_irrefl. CHSH > 2 from CHSH_violation with rfl.
-/
theorem assumption_B_true :
    ∃ (R : RelationalOrigin (Fin 4)),
      -- metric
      (∀ i j, 0 ≤ R.d_R i j) ∧ (∀ i, R.d_R i i = 0) ∧
      -- strict partial order
      (∀ i, ¬R.causal i i) ∧
      -- Bell CHSH > 2
      R.CHSH_val > 2 := by
        refine' ⟨ _, _, _, _, _ ⟩;
        refine' ⟨ fun _ _ => 0, _, _, _, _, 0, _, _, _ ⟩ <;> norm_num [ RelationalOrigin.d_R, RelationalOrigin.causal ];
        exact 1;
        all_goals norm_num [ RelationalOrigin.d_R, RelationalOrigin.causal, RelationalOrigin.CHSH_val ] at *;
        exact 0;
        · unfold RelationalOrigin.I_R; norm_num;
        · unfold RelationalOrigin.I_R; norm_num;
        · unfold RelationalOrigin.E_R; norm_num;

/-! ## Assumption C: "Finite-speed compatibility conflicts with Bell violation."

Expected: **FALSE**. -/

/-
PROVIDED SOLUTION
Use originA as witness. finite_speed_compat gives the first conjunct, CHSH_violation originA rfl gives the second.
-/
theorem assumption_C_false :
    ∃ (R : RelationalOrigin (Fin 4)),
      (∀ i j t, 0 < t → R.K_pos t i j → R.d_R i j ≤ R.v * t) ∧
      R.CHSH_val > 2 := by
        -- By assumption_C_false, there exists a common-origin structure R with.CHSH_val > 2.
        obtain ⟨R, hR⟩ : ∃ R : RelationalOrigin (Fin 4), R.CHSH_val > 2 := by
          -- By assumption_B_true, there exists a common-origin structure R with CHSH > 2. We can use this R.
          obtain ⟨R, hR⟩ := assumption_B_true;
          use R;
          aesop; -- This should complete the proof.;
        use R;
        exact ⟨ fun i j t ht h => by simpa [ metric_emergence ] using h, hR ⟩

/-! ## Assumption D: "Bell violation requires nonlocal couplings in the emergent metric."

Expected: **FALSE**. -/

/-
PROVIDED SOLUTION
Use originA as witness. coupling_decreases_with_distance gives locality, CHSH_violation originA rfl gives CHSH > 2.
-/
theorem assumption_D_false :
    ∃ (R : RelationalOrigin (Fin 4)),
      -- coupling is local (decreases with distance)
      (∀ i j k, R.d_R i j ≤ R.d_R i k → R.H_R i k ≤ R.H_R i j) ∧
      -- yet CHSH > 2
      R.CHSH_val > 2 := by
        grind +suggestions

/-! ## Assumption E: "Metric and causal structure alone determine Bell statistics."

Expected: **FALSE**. Two origins with same D and τ but different phaseParam
have different CHSH values. -/

def originA : RelationalOrigin (Fin 4) where
  D := uniD
  D_nonneg := uniD_nonneg
  D_self := uniD_self
  D_symm := uniD_symm
  D_triangle := uniD_triangle
  τ := fun i => (i : ℝ)
  v := 1
  v_pos := one_pos
  phaseParam := π / 4

def originB : RelationalOrigin (Fin 4) where
  D := uniD
  D_nonneg := uniD_nonneg
  D_self := uniD_self
  D_symm := uniD_symm
  D_triangle := uniD_triangle
  τ := fun i => (i : ℝ)
  v := 1
  v_pos := one_pos
  phaseParam := π / 2

/-
PROVIDED SOLUTION
For the first conjunct: originA.D = uniD = originB.D so ∀ i j, originA.D i j = originB.D i j by rfl. For the second: originA.τ = originB.τ by rfl. For CHSH: originA has phaseParam π/4 so CHSH_violation gives > 2. originB has phaseParam π/2 so CHSH = 4·cos(π/2) = 0 ≤ 2 (like assumption_A_false).
-/
theorem assumption_E_false :
    -- Same geometry
    (∀ i j : Fin 4, originA.D i j = originB.D i j) ∧
    -- Same causal time function
    (∀ i : Fin 4, originA.τ i = originB.τ i) ∧
    -- Different Bell statistics
    originA.CHSH_val > 2 ∧ originB.CHSH_val ≤ 2 := by
      unfold originA originB; norm_num;
      constructor <;> norm_num [ CHSH_eq_four_cos, CHSH_violation, assumption_A_false ];
      nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

end