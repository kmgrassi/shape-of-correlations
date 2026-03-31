import RequestProject.Defs

/-!
# Equivalences Between Interpretations (Part VII, Theorem 12)

## Main results:

- **Theorem 12** (`all_interpretations_equivalent`):
  In the all-positive regime, the geometric defect, transport fidelity,
  information compression, and triangle slack interpretations are all
  equivalent — they reduce to the same mathematical condition.

- `delta_mu_inverse` / `mu_delta_inverse`: δ = -log μ and μ = exp(-δ)
  are inverse transformations, showing the geometric defect and
  multiplicative attenuation are the same structure in different coordinates.

This demonstrates that the different physical stories about μ
(geometric consistency, transport fidelity, information retention,
correlation decay) are the same structure in disguise.
-/

noncomputable section

open Real

variable {α : Type*}

/-! ## All interpretations agree -/

/-- The geometric defect interpretation and the transport fidelity interpretation
    are equivalent: both are exactly ApproxSubmult μ G. -/
theorem geometric_defect_eq_transport {G : α → α → ℝ} {μ : ℝ} :
    ApproxSubmult μ G ↔ (∀ i j k, |G i k| ≥ μ * |G i j| * |G j k|) :=
  Iff.rfl

/-- The information compression interpretation is the same as ApproxSubmult. -/
theorem information_compression_eq_approxSubmult {G : α → α → ℝ} {μ : ℝ} :
    (∀ i j k, |G i k| ≥ μ * |G i j| * |G j k|) ↔ ApproxSubmult μ G :=
  Iff.rfl

/-! ## Structural equivalence of δ and μ -/

/-- δ = -log μ and μ = exp(-δ) are inverse transformations:
    exp(-(- log μ)) = μ. -/
theorem delta_mu_inverse (μ : ℝ) (hμ : 0 < μ) :
    Real.exp (-(-Real.log μ)) = μ := by
  norm_num [Real.exp_log hμ]

/-- Converting back: from δ to μ. -log(exp(-δ)) = δ. -/
theorem mu_delta_inverse (δ : ℝ) :
    -Real.log (Real.exp (-δ)) = δ := by
  norm_num +zetaDelta

/-! ## The four equivalent views (Theorem 12) -/

/-- **Theorem 12**: In the all-positive regime, the following are equivalent:

    1. **Geometric consistency**: G satisfies ApproxSubmult μ
       (multiplicative: |G(i,k)| ≥ μ · |G(i,j)| · |G(j,k)|)

    2. **Triangle defect**: D = -log|G| satisfies TriangleSlack (-log μ)
       (additive: D(i,k) ≤ D(i,j) + D(j,k) + δ where δ = -log μ)

    3. **Transport fidelity**: correlations survive composition with fidelity μ

    4. **Information retention**: fraction μ of relational information
       preserved under mediation

    All four are the same condition, just viewed through different lenses.
    This unifies the physical interpretations of μ. -/
theorem all_interpretations_equivalent {G : α → α → ℝ} {μ : ℝ}
    (hG : ∀ i j, |G i j| > 0) (hμ : 0 < μ) :
    ApproxSubmult μ G ↔
    TriangleSlack (-Real.log μ) (fun i j => -Real.log (|G i j|)) := by
  constructor <;> intro h_scope i j k
  · have := h_scope i j k
    have := Real.log_le_log (mul_pos (mul_pos hμ (hG i j)) (hG j k)) this
    rw [Real.log_mul (mul_ne_zero hμ.ne' (ne_of_gt (hG i j))) (ne_of_gt (hG j k)),
        Real.log_mul hμ.ne' (ne_of_gt (hG i j))] at this
    linarith
  · have h_mul : Real.log (|G i k|) ≥ Real.log (μ * |G i j| * |G j k|) := by
      simp_all +decide [Real.log_mul, ne_of_gt]
      linarith [h_scope i j k]
    rwa [ge_iff_le, Real.log_le_log_iff
      (mul_pos (mul_pos hμ (hG i j)) (hG j k)) (hG i k)] at h_mul

end
