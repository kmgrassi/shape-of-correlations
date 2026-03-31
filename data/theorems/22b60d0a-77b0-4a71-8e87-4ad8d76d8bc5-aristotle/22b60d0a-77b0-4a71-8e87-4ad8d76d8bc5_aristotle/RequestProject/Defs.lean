/-
# Common-Origin Kernel Classification

Core definitions for the classification of normalized PSD relational kernels
supporting both geometry (via submultiplicativity) and Bell violation (via CHSH).
-/
import Mathlib

namespace CommonOrigin

open Finset BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

-- ============================================================
-- Part I: Core kernel properties
-- ============================================================

/-- A kernel G : S → S → ℝ is symmetric. -/
def IsSymmetric (G : S → S → ℝ) : Prop :=
  ∀ i j, G i j = G j i

/-- A kernel is normalized: G(i,i) = 1 for all i. -/
def IsNormalized (G : S → S → ℝ) : Prop :=
  ∀ i, G i i = 1

/-- A kernel is positive semidefinite:
  for all weight vectors c, ∑ᵢ ∑ⱼ cᵢ G(i,j) cⱼ ≥ 0. -/
def IsPSD (G : S → S → ℝ) : Prop :=
  ∀ c : S → ℝ, 0 ≤ ∑ i : S, ∑ j : S, c i * G i j * c j

/-- A common-origin kernel: symmetric, normalized, and PSD. -/
structure IsCommonOriginKernel (G : S → S → ℝ) : Prop where
  symmetric : IsSymmetric G
  normalized : IsNormalized G
  psd : IsPSD G

-- ============================================================
-- Part II: Geometry predicates
-- ============================================================

/-- All absolute values of kernel entries are strictly positive. -/
def AllPositive (G : S → S → ℝ) : Prop :=
  ∀ i j, 0 < |G i j|

/-- Global submultiplicativity: |G(i,k)| ≥ |G(i,j)| · |G(j,k)| for all i,j,k.
  This is equivalent to the triangle inequality for d_G(i,j) = -log|G(i,j)|. -/
def GlobalSubmult (G : S → S → ℝ) : Prop :=
  ∀ i j k, |G i k| ≥ |G i j| * |G j k|

/-- Global geometry: all entries positive and globally submultiplicative.
  Then d_G(i,j) = -log|G(i,j)| is a pseudometric. -/
def GlobalGeometry (G : S → S → ℝ) : Prop :=
  AllPositive G ∧ GlobalSubmult G

/-- Sector positivity: |G(i,j)| > 0 for all i,j in subset T. -/
def SectorPositive (G : S → S → ℝ) (T : Finset S) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, 0 < |G i j|

/-- Sector submultiplicativity on subset T. -/
def SectorSubmult (G : S → S → ℝ) (T : Finset S) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, |G i k| ≥ |G i j| * |G j k|

/-- Sector geometry on subset T: positivity + submultiplicativity restricted to T. -/
def SectorGeometry (G : S → S → ℝ) (T : Finset S) : Prop :=
  SectorPositive G T ∧ SectorSubmult G T

-- ============================================================
-- Part III: Bell scenario
-- ============================================================

/-- Bell scenario: four distinguished indices A₀, A₁, B₀, B₁. -/
structure BellIndices (S : Type*) where
  A0 : S
  A1 : S
  B0 : S
  B1 : S

/-- CHSH value: E(0,0) + E(0,1) + E(1,0) - E(1,1) where E(a,b) = G(Aₐ, Bᵦ). -/
def CHSH_value (G : S → S → ℝ) (B : BellIndices S) : ℝ :=
  G B.A0 B.B0 + G B.A0 B.B1 + G B.A1 B.B0 - G B.A1 B.B1

/-- Bell-violating: there exist indices with |CHSH| > 2. -/
def BellViolating (G : S → S → ℝ) : Prop :=
  ∃ B : BellIndices S, |CHSH_value G B| > 2

/-- Bell-trivial: for all choices of indices, |CHSH| ≤ 2. -/
def TrivialBell (G : S → S → ℝ) : Prop :=
  ∀ B : BellIndices S, |CHSH_value G B| ≤ 2

/-- Nonseparability invariant η(G) = |CHSH(G)| / 4. -/
noncomputable def eta (G : S → S → ℝ) (B : BellIndices S) : ℝ :=
  |CHSH_value G B| / 4

/-- The geometry distance kernel: d_G(i,j) = -log|G(i,j)|. -/
noncomputable def distKernel (G : S → S → ℝ) (i j : S) : ℝ :=
  -Real.log (|G i j|)

-- ============================================================
-- Part IV: Concrete kernel families
-- ============================================================

/-- Constant kernel: G(i,j) = 1 for all i,j. -/
def constKernel (S : Type*) : S → S → ℝ := fun _ _ => 1

/-- Rank-1 kernel from a vector v: G(i,j) = v(i) · v(j). -/
def rank1Kernel (v : S → ℝ) : S → S → ℝ := fun i j => v i * v j

/-- Standard Bell indices for Fin 4: A₀=0, A₁=1, B₀=2, B₁=3. -/
def stdBellIndices : BellIndices (Fin 4) where
  A0 := 0
  A1 := 1
  B0 := 2
  B1 := 3

/-- Auxiliary: √2/2 -/
noncomputable abbrev sqrt2half : ℝ := Real.sqrt 2 / 2

/-- The CHSH-optimal kernel on Fin 4.
  This is the Gram matrix of the unit vectors:
    A₀ = (1, 0), A₁ = (0, 1),
    B₀ = (√2/2, √2/2), B₁ = (√2/2, -√2/2).
  It achieves CHSH = 2√2 (Tsirelson bound). -/
noncomputable def chshKernel : Fin 4 → Fin 4 → ℝ :=
  ![![1, 0, sqrt2half, sqrt2half],
    ![0, 1, sqrt2half, -sqrt2half],
    ![sqrt2half, sqrt2half, 1, 0],
    ![sqrt2half, -sqrt2half, 0, 1]]

-- ============================================================
-- Part V: Rank and structural predicates
-- ============================================================

/-- A kernel is rank-1 if it factors as v(i) · v(j) for some vector v. -/
def IsRank1 (G : S → S → ℝ) : Prop :=
  ∃ v : S → ℝ, ∀ i j, G i j = v i * v j

/-- Predicate: G is simultaneously globally geometric and Bell-violating. -/
def GlobalCoexistence (G : S → S → ℝ) : Prop :=
  GlobalGeometry G ∧ BellViolating G

/-- Predicate: G has sectoral coexistence — geometry on some sector and Bell violation. -/
def SectoralCoexistence (G : S → S → ℝ) : Prop :=
  (∃ T : Finset S, SectorGeometry G T) ∧ BellViolating G

end CommonOrigin
