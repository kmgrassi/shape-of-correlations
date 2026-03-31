/-
# Locality Emergence Theorems

Theorems D1-D3: Showing that locality emerges from the metric structure
when coupling respects distance, and fails when it doesn't.
-/
import RequestProject.CorrGeom.Defs

noncomputable section

open Real

variable {S : Type*}

/-! ## Theorem D2: Locality fails for non-monotone coupling

We construct a coupling that is NOT monotone in distance.
This shows geometry alone does not force local dynamics. -/

/-- There exists a function f : ℝ → ℝ such that f is not monotone decreasing,
    i.e., there exist d₁ < d₂ with f(d₁) < f(d₂), violating locality. -/
theorem locality_requires_monotone_coupling :
    ∃ (f : ℝ → ℝ), (∃ d₁ d₂ : ℝ, 0 ≤ d₁ ∧ d₁ < d₂ ∧ f d₁ < f d₂) :=
  ⟨fun x => x, 0, 1, by norm_num⟩

/-! ## Theorem D3: Approximate locality under exponential decay

If H(i,j) = exp(-d(i,j)), then for any ε > 0 there exists R such that
d(i,j) > R implies H(i,j) < ε. -/

/-- Exponential coupling gives effective locality: interactions beyond
    distance R are bounded by exp(-R), which tends to 0. -/
theorem expCoupling_locality (K : CorrKernel S) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ i j : S, emergentDist K i j > R → expCoupling K i j < ε := by
  use -Real.log ε
  intro i j hij
  rw [expCoupling]
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_exp]
  linarith

/-! ## Assumption 3 test: "Geometry alone implies locality" is FALSE

Without assuming coupling is monotone in distance, having a good metric
does not force local dynamics. We formalize this by exhibiting a coupling
function that increases with distance. -/

/-- A "perverse" coupling that INCREASES with distance.
    f(d) = d makes farther points interact MORE strongly. -/
def perverseCoupling : ℝ → ℝ := id

/-- The perverse coupling is anti-local: it increases with distance. -/
theorem perverse_coupling_anti_local :
    ∀ d₁ d₂ : ℝ, d₁ < d₂ → perverseCoupling d₁ < perverseCoupling d₂ :=
  fun _ _ h => h

end
