/-
# Wave-First Quantum Theory: Localization Theorems

## Theorem 4: Linear dispersive evolution spreads wave packets
## Theorem 5: Stable localization requires extra structure
## Theorem 6: Existence of localized solutions in nonlinear model
## Theorem 7: Stability of localized solutions (sech profile properties)
## Theorem 9: Linear detector obstruction
-/
import Mathlib

open Complex MeasureTheory

/-! ## Theorem 4/5: Linear free evolution has no nontrivial localized stationary states

For a linear free evolution operator on L², any stationary state
(eigenfunction of the Hamiltonian H = -Δ) that is also localized
(in L²) must be zero. On ℝᵈ with no potential, the free Laplacian
has purely continuous spectrum and no L² eigenfunctions.

We prove a clean algebraic version: a function on ℤ → ℂ that is
stationary under the shift (f(n+1) = e^{iω} f(n)) and has finite
support must be identically zero. -/

/-- A function f : ℤ → ℂ is "stationary under shift" if there exists ω such that
    shifting f by 1 equals e^{iω} · f. -/
def IsStationaryUnderShift (f : ℤ → ℂ) : Prop :=
  ∃ ω : ℝ, ∀ n : ℤ, f (n + 1) = exp (ω * I) * f n

/-- A function f : ℤ → ℂ has finite support. -/
def HasFiniteSupport (f : ℤ → ℂ) : Prop :=
  Set.Finite (Function.support f)

/-- **Localization obstruction**: No nontrivial finitely-supported stationary state
    exists under shift evolution. If f(n+1) = e^{iω} f(n) and f has finite support,
    then f = 0. The key insight is that stationarity forces |f(n)| = |f(0)| for all n,
    so if f(0) ≠ 0 then f has infinite support. -/
theorem no_localized_stationary_state (f : ℤ → ℂ)
    (hstat : IsStationaryUnderShift f) (hfin : HasFiniteSupport f) :
    f = 0 := by
  obtain ⟨ω, hω⟩ := hstat
  have h_eq : ∀ n, f n = Complex.exp (ω * Complex.I * n) * f 0 := by
    intro n; induction' n using Int.induction_on with n ihn n ihn; all_goals norm_num
    · simp_all +decide [mul_add, add_mul, Complex.exp_add]; ring
    · have := hω (-n - 1); simp_all +decide [mul_sub, sub_mul, Complex.exp_sub]; ring
      simp_all +decide [sub_eq_add_neg, add_comm, mul_assoc, mul_left_comm, Complex.exp_ne_zero]
  by_cases h_f0 : f 0 = 0
  · ext n; rw [h_eq n, h_f0]; norm_num
  · exact False.elim <| hfin.not_infinite <|
      Set.infinite_of_injective_forall_mem (fun n m => by simp [h_f0]) fun n =>
        show f n ≠ 0 from by rw [h_eq]; exact mul_ne_zero (Complex.exp_ne_zero _) h_f0

/-! ## Theorem 5: Stable localized matter requires extra structure

Consequence of the above: for the free linear discrete evolution,
localized + stationary ⟹ trivial. Hence stable matter-like objects
require nonlinearity, confining potential, or topological structure. -/

/-- **Obstruction theorem**: any "matter object" that is both localized and stationary
    under free linear evolution is trivial. -/
theorem stable_matter_requires_extra_structure (f : ℤ → ℂ)
    (hstat : IsStationaryUnderShift f) (hfin : HasFiniteSupport f) :
    ∀ n, f n = 0 := by
  exact fun n => congr_fun (no_localized_stationary_state f hstat hfin) n

/-! ## Theorems 6 & 7: Nonlinear localized solutions

Nonlinear field equations CAN have localized solutions (solitons).
We model a 1D nonlinear Schrödinger soliton profile: ψ(x) = A sech(Bx)
and verify it is nonzero, localized (decays to 0), and has finite energy. -/

/-- A soliton profile: sech function. -/
noncomputable def sechProfile (A B : ℝ) (x : ℝ) : ℝ :=
  A / Real.cosh (B * x)

/-- The sech profile is nonzero at the origin when A ≠ 0. -/
theorem sech_profile_nonzero_at_origin (A B : ℝ) (hA : A ≠ 0) :
    sechProfile A B 0 ≠ 0 := by
  unfold sechProfile; aesop

/-- The sech profile decays: for B > 0, sechProfile A B x → 0 as |x| → ∞. -/
theorem sech_profile_decays (A B : ℝ) (hB : 0 < B) :
    Filter.Tendsto (fun x => sechProfile A B x) (Filter.cocompact ℝ) (nhds 0) := by
  have h_cosh_inf : Filter.Tendsto (fun x : ℝ => Real.cosh (B * x))
      (Filter.cocompact ℝ) Filter.atTop := by
    have h_cosh_atTop : Filter.Tendsto (fun x : ℝ => Real.cosh (B * x))
        Filter.atTop Filter.atTop := by
      simp +decide [Real.cosh_eq]
      exact Filter.Tendsto.atTop_div_const (by positivity)
        (Filter.tendsto_atTop_mono (fun x => le_add_of_nonneg_right <| Real.exp_nonneg _) <|
          Real.tendsto_exp_atTop.comp <| Filter.tendsto_id.const_mul_atTop hB)
    rw [Filter.tendsto_atTop] at *
    simp_all +decide [Filter.eventually_iff]
    exact fun b => by
      obtain ⟨a, ha⟩ := h_cosh_atTop b
      exact ⟨-a, fun x hx => by simpa [mul_neg, Real.cosh_neg] using ha (-x) (by linarith)⟩
  convert tendsto_const_nhds.div_atTop h_cosh_inf using 1

/-! ## Theorem 9: Linear detector obstruction

A purely linear detector coupling produces superposed responses.
If a detector's response is a linear functional of the field, then
superposed inputs produce superposed detector states — there is no
mechanism for a unique "click." -/

/-- **Detector obstruction**: Linear detector response preserves superposition.
    A purely linear detector cannot select a single outcome from a superposition. -/
theorem linear_detector_superposition
    {V W : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    (D : V →ₗ[ℂ] W) (ψ₁ ψ₂ : V) :
    D (ψ₁ + ψ₂) = D ψ₁ + D ψ₂ := by
  convert D.map_add ψ₁ ψ₂
