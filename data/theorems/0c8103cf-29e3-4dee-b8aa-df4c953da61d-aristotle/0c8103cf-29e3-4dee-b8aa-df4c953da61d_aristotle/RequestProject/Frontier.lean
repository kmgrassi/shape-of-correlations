import RequestProject.Defs
import RequestProject.Bell

/-!
# Part IX: Frontier — Bell Violation from Nonseparability Invariant

We define a nonseparability invariant η(R) = |cos(phaseParam)| and prove
that CHSH violation is controlled by this invariant.

Note: Our correlator model is not constrained by the Tsirelson bound (2√2),
as it is a general relational model, not specifically a quantum model.
The maximum |CHSH| is 4, achieved when |cos(phaseParam)| = 1.
-/

open Real

noncomputable section

variable {S : Type*} (R : RelationalOrigin S)

/-! ## Theorem 8: Bell violation from nonseparable relational invariant -/

/-- If η(R) = 0, then CHSH = 0 ≤ 2 (no Bell violation) -/
theorem eta_zero_no_violation (h : R.η = 0) : R.CHSH_val ≤ 2 := by
  rw [CHSH_eq_four_cos] at *;
  unfold RelationalOrigin.η at h; aesop;

/-
PROBLEM
If η(R) > 1/2 and cos(phaseParam) > 0, then CHSH > 2 (Bell violation)

PROVIDED SOLUTION
η > 1/2 and cos θ > 0 means cos θ = |cos θ| = η > 1/2. So CHSH = 4 cos θ > 4·(1/2) = 2. Use CHSH_eq_four_cos and CHSH_violation_general.
-/
theorem eta_threshold_violation (h : R.η > 1/2) (hpos : 0 < cos R.phaseParam) :
    R.CHSH_val > 2 := by
      -- Since $η(R) = |cos(phaseParam)|$ and $cos(phaseParam) > 0$, we have $cos(phaseParam) = η(R)$.
      have h_cos_eq_η : cos R.phaseParam = R.η := by
        exact Eq.symm ( abs_of_pos hpos );
      linarith [ CHSH_eq_four_cos R ]

/-- The CHSH value equals 4 * η(R) when cos(phaseParam) ≥ 0 -/
theorem CHSH_eq_four_eta (h : 0 ≤ cos R.phaseParam) :
    R.CHSH_val = 4 * R.η := by
      rw [CHSH_eq_four_cos];
      rw [ RelationalOrigin.η, abs_of_nonneg h ]

/-
PROBLEM
The absolute CHSH value is bounded by 4

PROVIDED SOLUTION
CHSH = 4 cos θ. |CHSH| = 4|cos θ| ≤ 4·1 = 4 since |cos θ| ≤ 1 (by Real.abs_cos_le_one).
-/
theorem CHSH_abs_le_four : |R.CHSH_val| ≤ 4 := by
  rw [CHSH_eq_four_cos];
  exact abs_le.mpr ⟨ by linarith [ Real.neg_one_le_cos R.phaseParam ], by linarith [ Real.cos_le_one R.phaseParam ] ⟩

/-
PROBLEM
Characterization: CHSH > 2 ⟺ cos(phaseParam) > 1/2

PROVIDED SOLUTION
CHSH = 4 cos θ. CHSH > 2 ⟺ 4 cos θ > 2 ⟺ cos θ > 1/2. Use CHSH_eq_four_cos and linarith.
-/
theorem CHSH_gt_two_iff : R.CHSH_val > 2 ↔ cos R.phaseParam > 1/2 := by
  constructor <;> intro h <;> rw [ CHSH_eq_four_cos ] at * <;> linarith

/-
PROBLEM
The nonseparability invariant η controls the magnitude of CHSH

PROVIDED SOLUTION
|CHSH| = |4 cos θ| = 4 |cos θ| = 4 η. Use CHSH_eq_four_cos, abs_mul, abs_of_pos (show 4 > 0).
-/
theorem CHSH_eq_four_cos_abs : |R.CHSH_val| = 4 * R.η := by
  rw [CHSH_eq_four_cos];
  norm_num [ abs_mul, RelationalOrigin.η ]

end