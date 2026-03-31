import RequestProject.Defs

/-!
# Part IV–V: Bell Structure and No-Signaling from Common Origin

We prove that suitable common-origin data yields CHSH > 2,
and that the probability model satisfies no-signaling.
-/

open Real

noncomputable section

variable {S : Type*} (R : RelationalOrigin S)

/-! ## Theorem 5: CHSH violation from common-origin correlator -/

/-
PROBLEM
The CHSH value equals 4 cos(phaseParam)

PROVIDED SOLUTION
Unfold CHSH_val and E_R. E_R(0,0) = cos θ, E_R(0,1) = cos θ, E_R(1,0) = cos θ, E_R(1,1) = -cos θ. So CHSH = cos θ + cos θ + cos θ - (-cos θ) = 4 cos θ. Use simp with the definition, noting that (0:Fin 2) ≠ 1 and (1:Fin 2) = 1.
-/
theorem CHSH_eq_four_cos : R.CHSH_val = 4 * cos R.phaseParam := by
  unfold RelationalOrigin.CHSH_val RelationalOrigin.E_R; ring;
  simp +decide ; ring

/-
PROBLEM
For phaseParam = π/4, the CHSH value is 2√2

PROVIDED SOLUTION
By CHSH_eq_four_cos, CHSH = 4·cos(π/4). cos(π/4) = √2/2. So CHSH = 4·(√2/2) = 2√2. Use Real.cos_pi_div_four.
-/
theorem CHSH_at_pi_over_4 (h : R.phaseParam = π / 4) :
    R.CHSH_val = 2 * √2 := by
      convert CHSH_eq_four_cos R using 1 ; norm_num [ h ] ; ring

/-
PROBLEM
CHSH violation: for phaseParam = π/4, CHSH > 2

PROVIDED SOLUTION
By CHSH_at_pi_over_4, CHSH = 2√2. We need 2√2 > 2, i.e., √2 > 1. Use one_lt_sqrt (or Real.lt_sqrt) with 2 > 1.
-/
theorem CHSH_violation (h : R.phaseParam = π / 4) : R.CHSH_val > 2 := by
  rw [ CHSH_eq_four_cos, h ] ; norm_num ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;

/-
PROBLEM
More generally, CHSH > 2 whenever cos(phaseParam) > 1/2

PROVIDED SOLUTION
By CHSH_eq_four_cos, CHSH = 4·cos(θ). If cos(θ) > 1/2 then CHSH = 4·cos(θ) > 4·(1/2) = 2.
-/
theorem CHSH_violation_general (h : cos R.phaseParam > 1/2) :
    R.CHSH_val > 2 := by
      rw [ CHSH_eq_four_cos ] ; linarith;

/-! ## Theorem 6: No-signaling in the common-origin Bell model -/

/-
PROBLEM
Alice's marginal is always 1/2, independent of Bob's setting

PROVIDED SOLUTION
Unfold P_Alice and P_joint. Cases on x: if x = true, P_Alice = P_joint(true,true) + P_joint(true,false) = (1+E)/4 + (1-E)/4 = 2/4 = 1/2. If x = false, P_Alice = P_joint(false,true) + P_joint(false,false) = (1-E)/4 + (1+E)/4 = 1/2.
-/
theorem alice_marginal (a b : Fin 2) (x : Bool) :
    R.P_Alice a b x = 1 / 2 := by
      unfold RelationalOrigin.P_Alice RelationalOrigin.P_joint; fin_cases x <;> norm_num;
      · ring;
      · ring

/-
PROBLEM
Bob's marginal is always 1/2, independent of Alice's setting

PROVIDED SOLUTION
Unfold P_Bob and P_joint. Cases on y: if y = true, P_Bob = P_joint(true,true) + P_joint(false,true) = (1+E)/4 + (1-E)/4 = 1/2. Similarly for y = false.
-/
theorem bob_marginal (a b : Fin 2) (y : Bool) :
    R.P_Bob a b y = 1 / 2 := by
      unfold RelationalOrigin.P_Bob RelationalOrigin.P_joint;
      cases y <;> norm_num <;> ring

/-
PROBLEM
No-signaling: Alice's marginal is independent of Bob's setting choice

PROVIDED SOLUTION
Both sides equal 1/2 by alice_marginal.
-/
theorem no_signaling_alice (a b b' : Fin 2) (x : Bool) :
    R.P_Alice a b x = R.P_Alice a b' x := by
      rw [ alice_marginal, alice_marginal ]

/-
PROBLEM
No-signaling: Bob's marginal is independent of Alice's setting choice

PROVIDED SOLUTION
Both sides equal 1/2 by bob_marginal.
-/
theorem no_signaling_bob (a a' b : Fin 2) (y : Bool) :
    R.P_Bob a b y = R.P_Bob a' b y := by
      rw [ bob_marginal, bob_marginal ]

/-
PROBLEM
Joint probabilities are nonneg when |E_R| ≤ 1

PROVIDED SOLUTION
Unfold P_joint. In both cases (x==y and x≠y), the value is (1 ± E_R(a,b))/4. E_R is either cos(θ) or -cos(θ), so |E_R| = |cos(θ)| ≤ 1 by h. Thus 1 ± E_R ≥ 0 and dividing by 4 gives nonneg. Use cases on the if-condition and bound using |cos θ| ≤ 1.
-/
theorem P_joint_nonneg (h : |cos R.phaseParam| ≤ 1)
    (a b : Fin 2) (x y : Bool) : 0 ≤ R.P_joint a b x y := by
      unfold RelationalOrigin.P_joint;
      unfold RelationalOrigin.E_R; split_ifs <;> linarith [ abs_le.mp h ] ;

/-
PROBLEM
Joint probabilities sum to 1

PROVIDED SOLUTION
Unfold P_joint. The sum is (1+E)/4 + (1-E)/4 + (1-E)/4 + (1+E)/4 = 4/4 = 1. Just unfold and ring.
-/
theorem P_joint_sum_one (a b : Fin 2) :
    R.P_joint a b true true + R.P_joint a b true false +
    R.P_joint a b false true + R.P_joint a b false false = 1 := by
      unfold RelationalOrigin.P_joint; split_ifs <;> ring;
      all_goals norm_num at *;

end