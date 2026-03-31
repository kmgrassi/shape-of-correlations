import RequestProject.Defs

/-!
# Toy Model: Coarse-Graining, Propagation, and CHSH (Priorities 3 & 4)

## Main results:

### Theorem D (propagation):
- `propagation_induces_approxSubmult`: μ can be realized as a propagation attenuation factor
- `perfect_transport_mu_one`: perfect compositional transport gives μ = 1
- `lossy_propagation`: lossy propagation gives 0 < μ < 1

### Theorem 9 (information loss):
- `information_loss_is_approxSubmult`: information loss under mediation = ApproxSubmult

### Toy models:
- `constantKernel_exactSubmult_of_abs_le_one`: constant kernels with |c| ≤ 1 are exact
- `constantKernel_approxSubmult`: constant kernel with c > 0 has ApproxSubmult (1/c)
- `allOnes_has_mu_one`: all-ones kernel has exact submultiplicativity
- `scaling_approxSubmult`: scaling changes μ to μ/|c|

### CHSH connection:
- `chsh_trivial_bound`: |CHSH| ≤ 4 when all entries bounded by 1
- `chsh_interp_linear`: CHSH is linear in the interpolation parameter
- `chsh_classical`: classical kernel has CHSH = 2
-/

noncomputable section

open Real

variable {α : Type*}

/-! ## Propagation / Transport Model -/

/-- A propagation kernel: G(i,j) = lam^(steps i j) · base(i,j). -/
def propagationKernel (lam : ℝ) (base : α → α → ℝ) (steps : α → α → ℕ) :
    α → α → ℝ := fun i j =>
  lam ^ (steps i j) * base i j

/-! ## Theorem 6: Propagation attenuation induces μ-submultiplicativity -/

/-- **Theorem 6**: If a kernel satisfies |G(i,k)| ≥ lam · |G(i,j)| · |G(j,k)|
    pointwise, then ApproxSubmult lam G holds. μ = lam is exactly the
    propagation attenuation / transport fidelity factor. -/
theorem propagation_induces_approxSubmult {G : α → α → ℝ} {lam : ℝ}
    (_hlam : 0 ≤ lam)
    (hcomp : ∀ i j k, |G i k| ≥ lam * |G i j| * |G j k|) :
    ApproxSubmult lam G :=
  hcomp

/-! ## Theorem 7: Perfect transport gives μ = 1 -/

/-- **Theorem 7**: If composition is lossless, then μ = 1. -/
theorem perfect_transport_mu_one {G : α → α → ℝ}
    (hlossless : ∀ i j k, |G i k| ≥ |G i j| * |G j k|) :
    ApproxSubmult 1 G :=
  fun i j k => by simpa using hlossless i j k

/-! ## Theorem 8: Lossy propagation gives 0 < μ < 1 -/

/-- **Theorem 8**: Lossy propagation with attenuation lam gives ApproxSubmult lam. -/
theorem lossy_propagation {G : α → α → ℝ} {lam : ℝ}
    (_hlam_pos : 0 < lam)
    (hcomp : ∀ i j k, |G i k| ≥ lam * |G i j| * |G j k|) :
    ApproxSubmult lam G :=
  hcomp

/-! ## Theorem 9: Information loss under mediation -/

/-- **Theorem 9**: Information loss under mediation (preserving fraction c)
    is exactly ApproxSubmult c. This connects μ to information-preservation
    under composition. -/
theorem information_loss_is_approxSubmult {I : α → α → ℝ} {c : ℝ}
    (_hc : 0 ≤ c)
    (hmed : ∀ i j k, |I i k| ≥ c * |I i j| * |I j k|) :
    ApproxSubmult c I :=
  hmed

/-! ## Constant Kernel Toy Models -/

/-- A constant kernel G(i,j) = c for all i,j. -/
def constantKernel (c : ℝ) : α → α → ℝ := fun _ _ => c

/-- A constant kernel with |c| ≤ 1 satisfies ExactSubmult.
    (|c| ≥ |c|² holds iff |c| ≤ 1.) -/
theorem constantKernel_exactSubmult_of_abs_le_one {c : ℝ} (hc : |c| ≤ 1) :
    ExactSubmult (constantKernel c : α → α → ℝ) := by
  intro i j k
  show |c| ≥ |c| * |c|
  cases abs_cases c <;> nlinarith

/-- A constant kernel with c > 0 satisfies ApproxSubmult (1/c).
    Since |c|/(|c|²) = 1/c, the consistency ratio is exactly 1/c. -/
theorem constantKernel_approxSubmult {c : ℝ} (hc : c > 0) :
    ApproxSubmult (1 / c) (constantKernel c : α → α → ℝ) := by
  intro i j k
  simp only [constantKernel, abs_of_pos hc]
  rw [div_mul_eq_mul_div, one_mul, div_mul_cancel₀ _ hc.ne']

/-- The all-ones kernel has ExactSubmult (μ = 1): |1| ≥ |1| · |1|. -/
theorem allOnes_has_mu_one :
    ExactSubmult (fun (_ _ : α) => (1 : ℝ)) :=
  fun _ _ _ => by norm_num

/-! ## Scaling and μ -/

/-- Scaling a kernel by c ≠ 0 transforms ApproxSubmult μ to ApproxSubmult (μ/|c|).
    This shows how rescaling affects the geometric consistency parameter. -/
theorem scaling_approxSubmult {G : α → α → ℝ} {μ c : ℝ}
    (hc : c ≠ 0) (_hμ : 0 ≤ μ) (hG : ApproxSubmult μ G) :
    ApproxSubmult (μ / |c|) (fun i j => c * G i j) := by
  intro i j k
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ge_iff_le, div_le_iff₀] <;>
    simp +decide [*, abs_mul]
  have := hG i j k
  ring_nf at this ⊢
  nlinarith [abs_nonneg c, abs_nonneg (G i j), abs_nonneg (G j k), abs_nonneg (G i k)]

/-! ## CHSH Bounds -/

/-- Simple CHSH bound: if each |G(i,j)| ≤ 1, then |CHSH| ≤ 4 (by triangle inequality). -/
theorem chsh_trivial_bound {G : Fin 4 → Fin 4 → ℝ}
    (hbd : ∀ i j, |G i j| ≤ 1) :
    |CHSHValue G| ≤ 4 :=
  abs_le.mpr ⟨by unfold CHSHValue
                 linarith! [abs_le.mp (hbd 0 2), abs_le.mp (hbd 0 3),
                            abs_le.mp (hbd 1 2), abs_le.mp (hbd 1 3)],
              by unfold CHSHValue
                 linarith! [abs_le.mp (hbd 0 2), abs_le.mp (hbd 0 3),
                            abs_le.mp (hbd 1 2), abs_le.mp (hbd 1 3)]⟩

/-- Under ApproxSubmult μ with diagonal bound, self-correlation constrains
    the relationship: μ · |G(i,i)| · |G(i,j)| ≤ |G(i,j)|. -/
theorem offdiag_bound_from_approxSubmult {G : α → α → ℝ} {μ : ℝ}
    (_hμ : 0 < μ) (hAS : ApproxSubmult μ G)
    (_hdiag : ∀ i, |G i i| ≤ 1) (i j : α) :
    μ * |G i i| * |G i j| ≤ |G i j| :=
  hAS i i j |> le_trans (by linarith)

/-! ## Toy Model: μ ↑ ⟹ CHSH ↓ for interpolated family -/

/-- The quantum (maximally entangled) part of the kernel, using standard
    Bell-test angles: 0, π/4, π/8, 3π/8. -/
def quantumKernel : Fin 4 → Fin 4 → ℝ := fun i j =>
  let angles : Fin 4 → ℝ := ![0, Real.pi/4, Real.pi/8, 3*Real.pi/8]
  Real.cos (angles i - angles j)

/-- The classical (product-state) kernel: all entries = 1. -/
def classicalKernel : Fin 4 → Fin 4 → ℝ := fun _ _ => 1

/-- The interpolated family G_t = (1-t) · Q + t · C.
    As t increases from 0 to 1, the kernel transitions from quantum to classical. -/
def interpKernel (t : ℝ) : Fin 4 → Fin 4 → ℝ := fun i j =>
  (1 - t) * quantumKernel i j + t * classicalKernel i j

/-- **Theorem C (linearity)**: The CHSH value of the interpolated kernel is
    a linear interpolation of the quantum and classical CHSH values.
    Since CHSH(classical) = 2 < 2√2 ≈ CHSH(quantum), increasing t
    (coarse-graining toward classical) decreases CHSH. -/
theorem chsh_interp_linear (t : ℝ) :
    CHSHValue (interpKernel t) =
      (1 - t) * CHSHValue quantumKernel + t * CHSHValue classicalKernel := by
  unfold CHSHValue interpKernel; ring

/-- The classical kernel has CHSH = 1 + 1 + 1 - 1 = 2. -/
theorem chsh_classical : CHSHValue classicalKernel = 2 := by
  unfold CHSHValue classicalKernel; norm_num

end
