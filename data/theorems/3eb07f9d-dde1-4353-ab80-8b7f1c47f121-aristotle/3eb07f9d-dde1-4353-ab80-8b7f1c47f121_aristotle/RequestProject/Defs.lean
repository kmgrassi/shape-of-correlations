/-
# Quantitative CHSH Bounds Under Geometric Constraints

Core definitions for studying whether global geometric consistency of a normalized PSD kernel
restricts the size of Bell/CHSH violation.
-/
import Mathlib

noncomputable section

open Real

/-! ## Core Definitions -/

/-- The CHSH functional for a kernel G with four distinguished indices -/
def CHSH_val {S : Type*} (G : S → S → ℝ) (A₀ A₁ B₀ B₁ : S) : ℝ :=
  G A₀ B₀ + G A₀ B₁ + G A₁ B₀ - G A₁ B₁

/-- The CHSH violation parameter η(G) = |CHSH(G)| / 4 -/
def CHSH_eta {S : Type*} (G : S → S → ℝ) (A₀ A₁ B₀ B₁ : S) : ℝ :=
  |CHSH_val G A₀ A₁ B₀ B₁| / 4

/-- A kernel is symmetric -/
def IsSymmetricKernel {S : Type*} (G : S → S → ℝ) : Prop :=
  ∀ i j, G i j = G j i

/-- A kernel is normalized (diagonal entries equal 1) -/
def IsNormalizedKernel {S : Type*} (G : S → S → ℝ) : Prop :=
  ∀ i, G i i = 1

/-- A kernel is positive semidefinite -/
def IsPSDKernel {S : Type*} [Fintype S] (G : S → S → ℝ) : Prop :=
  ∀ c : S → ℝ, ∑ i, ∑ j, c i * c j * G i j ≥ 0

/-- The geometry kernel: I_G(i,j) = |G(i,j)| -/
def geometryKernel {S : Type*} (G : S → S → ℝ) (i j : S) : ℝ :=
  |G i j|

/-- The geometric distance: d_G(i,j) = -log|G(i,j)| -/
def geomDist {S : Type*} (G : S → S → ℝ) (i j : S) : ℝ :=
  -Real.log (|G i j|)

/-- Bell-sector submultiplicativity: the submultiplicativity constraint restricted to
    the four Bell indices {A₀, A₁, B₀, B₁} -/
def BellSubmult {S : Type*} (G : S → S → ℝ) (A₀ A₁ B₀ B₁ : S) : Prop :=
  ∀ i ∈ ({A₀, A₁, B₀, B₁} : Set S),
  ∀ j ∈ ({A₀, A₁, B₀, B₁} : Set S),
  ∀ k ∈ ({A₀, A₁, B₀, B₁} : Set S),
    |G i k| ≥ |G i j| * |G j k|

/-- Global submultiplicativity: |G(i,k)| ≥ |G(i,j)| · |G(j,k)| for all i,j,k -/
def GlobalSubmult {S : Type*} (G : S → S → ℝ) : Prop :=
  ∀ i j k, |G i k| ≥ |G i j| * |G j k|

/-- A Bell scenario packages the kernel with its four distinguished indices -/
structure BellScenario (S : Type*) [Fintype S] where
  G : S → S → ℝ
  A₀ : S
  A₁ : S
  B₀ : S
  B₁ : S
  sym : IsSymmetricKernel G
  normalized : IsNormalizedKernel G
  psd : IsPSDKernel G

/-- The CHSH value of a Bell scenario -/
def BellScenario.chsh {S : Type*} [Fintype S] (B : BellScenario S) : ℝ :=
  CHSH_val B.G B.A₀ B.A₁ B.B₀ B.B₁

/-- The correlator E_G(a,b) = G(A_a, B_b) -/
def correlator {S : Type*} (G : S → S → ℝ) (A₀ A₁ B₀ B₁ : S) (a b : Fin 2) : ℝ :=
  G (if a = 0 then A₀ else A₁) (if b = 0 then B₀ else B₁)

/-! ## Basic Properties -/

/-- CHSH expressed in terms of correlators -/
theorem chsh_eq_correlators {S : Type*} (G : S → S → ℝ) (A₀ A₁ B₀ B₁ : S) :
    CHSH_val G A₀ A₁ B₀ B₁ =
    correlator G A₀ A₁ B₀ B₁ 0 0 + correlator G A₀ A₁ B₀ B₁ 0 1 +
    correlator G A₀ A₁ B₀ B₁ 1 0 - correlator G A₀ A₁ B₀ B₁ 1 1 := by
  simp [CHSH_val, correlator]

/-- Global submultiplicativity implies Bell-sector submultiplicativity -/
theorem GlobalSubmult.toBellSubmult {S : Type*} (G : S → S → ℝ) (A₀ A₁ B₀ B₁ : S)
    (hG : GlobalSubmult G) : BellSubmult G A₀ A₁ B₀ B₁ := by
  intro i _ j _ k _
  exact hG i j k

/-
PROBLEM
Helper: PSD quadratic form for two-element coefficient vectors.
    If G is PSD, symmetric, and normalized, then for any i, j and t:
    1 + 2*t*G(i,j) + t² ≥ 0

PROVIDED SOLUTION
Specialize the PSD condition with the coefficient vector c defined by c(i)=1, c(j)=t, c(k)=0 for k ∉ {i,j}. The sum ∑ₐ ∑_b c(a)*c(b)*G(a,b) becomes c(i)*c(i)*G(i,i) + c(i)*c(j)*G(i,j) + c(j)*c(i)*G(j,i) + c(j)*c(j)*G(j,j) = 1*1*1 + 1*t*G(i,j) + t*1*G(j,i) + t*t*1 = 1 + 2t*G(i,j) + t² (using symmetry G(i,j)=G(j,i) and normalization G(i,i)=G(j,j)=1).

Specifically: define c(k) = if k = i then 1 else if k = j then t else 0. Then ∑ₐ ∑_b c(a)*c(b)*G(a,b) = 1 + 2t*G(i,j) + t² ≥ 0 by PSD. The key is that all cross terms with k ∉ {i,j} vanish since c(k) = 0.
-/
theorem psd_two_point_quadratic {S : Type*} [Fintype S] [DecidableEq S] (G : S → S → ℝ)
    (hpsd : IsPSDKernel G) (hnorm : IsNormalizedKernel G) (hsym : IsSymmetricKernel G)
    (i j : S) (hij : i ≠ j) (t : ℝ) :
    1 + 2 * t * G i j + t ^ 2 ≥ 0 := by
  convert hpsd ( fun x => if x = i then 1 else if x = j then t else 0 ) using 1 ; simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ] ; ring!;
  rw [ Finset.sum_add_distrib ] ; simp +decide [ *, Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ] ; ring;
  rw [ if_neg hij.symm, if_neg hij.symm, if_neg hij.symm ] ; rw [ hnorm i, hnorm j ] ; rw [ hsym i j ] ; ring;

/-
PROBLEM
PSD + normalized implies G(i,j) ≤ 1

PROVIDED SOLUTION
If i = j, then G(i,j) = G(i,i) = 1 by normalization. If i ≠ j, use psd_two_point_quadratic with t = -1: 1 + 2*(-1)*G(i,j) + (-1)² ≥ 0, i.e., 2 - 2*G(i,j) ≥ 0, so G(i,j) ≤ 1.
-/
theorem psd_normalized_le_one {S : Type*} [Fintype S] [DecidableEq S] (G : S → S → ℝ)
    (hpsd : IsPSDKernel G) (hnorm : IsNormalizedKernel G) (hsym : IsSymmetricKernel G)
    (i j : S) : G i j ≤ 1 := by
  by_cases hij : i = j <;> [ simp +decide [ * ] ; linarith [ psd_two_point_quadratic G hpsd hnorm hsym i j hij ( -1 ) ] ];
  rw [ hnorm ]

/-
PROBLEM
PSD + normalized implies -1 ≤ G(i,j)

PROVIDED SOLUTION
If i = j, then G(i,j) = G(i,i) = 1 ≥ -1 by hnorm. If i ≠ j, use psd_two_point_quadratic with t = 1: 1 + 2*1*G(i,j) + 1² ≥ 0, i.e., 2 + 2*G(i,j) ≥ 0, so G(i,j) ≥ -1. Use linarith.
-/
theorem psd_normalized_ge_neg_one {S : Type*} [Fintype S] [DecidableEq S] (G : S → S → ℝ)
    (hpsd : IsPSDKernel G) (hnorm : IsNormalizedKernel G) (hsym : IsSymmetricKernel G)
    (i j : S) : -1 ≤ G i j := by
  by_cases hij : i = j <;> simp_all +decide [ IsSymmetricKernel, IsNormalizedKernel ];
  linarith [ psd_two_point_quadratic G hpsd hnorm hsym i j hij 1 ]

/-- PSD + normalized implies |G(i,j)| ≤ 1 -/
theorem psd_normalized_bound {S : Type*} [Fintype S] [DecidableEq S] (G : S → S → ℝ)
    (hpsd : IsPSDKernel G) (hnorm : IsNormalizedKernel G) (hsym : IsSymmetricKernel G)
    (i j : S) : |G i j| ≤ 1 := by
  rw [abs_le]
  exact ⟨psd_normalized_ge_neg_one G hpsd hnorm hsym i j,
         psd_normalized_le_one G hpsd hnorm hsym i j⟩

/-
PROBLEM
Trivial upper bound: |CHSH| ≤ 4 for normalized PSD kernels

PROVIDED SOLUTION
Use |CHSH| = |G(A₀,B₀) + G(A₀,B₁) + G(A₁,B₀) - G(A₁,B₁)| ≤ |G(A₀,B₀)| + |G(A₀,B₁)| + |G(A₁,B₀)| + |G(A₁,B₁)| ≤ 1 + 1 + 1 + 1 = 4, using psd_normalized_bound for each term and the triangle inequality.
-/
theorem chsh_trivial_bound {S : Type*} [Fintype S] [DecidableEq S] (G : S → S → ℝ)
    (hpsd : IsPSDKernel G) (hnorm : IsNormalizedKernel G) (hsym : IsSymmetricKernel G)
    (A₀ A₁ B₀ B₁ : S) : |CHSH_val G A₀ A₁ B₀ B₁| ≤ 4 := by
  exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₀ B₀ ), abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₀ B₁ ), abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₁ B₀ ), abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₁ B₁ ), show CHSH_val G A₀ A₁ B₀ B₁ = G A₀ B₀ + G A₀ B₁ + G A₁ B₀ - G A₁ B₁ from rfl ], by linarith [ abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₀ B₀ ), abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₀ B₁ ), abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₁ B₀ ), abs_le.mp ( psd_normalized_bound G hpsd hnorm hsym A₁ B₁ ), show CHSH_val G A₀ A₁ B₀ B₁ = G A₀ B₀ + G A₀ B₁ + G A₁ B₀ - G A₁ B₁ from rfl ] ⟩

end