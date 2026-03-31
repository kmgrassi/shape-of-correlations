/-
# Correlation → Geometry → Locality: Core Definitions

This file formalizes the abstract setup for emergent geometry from correlation kernels.
Given a finite set S with no background space, and a symmetric correlation kernel
I : S → S → ℝ with 0 < I(i,j) ≤ 1 and I(i,i) = 1, we define the emergent distance
d(i,j) = -log(I(i,j)) and study when this yields a metric space.
-/
import Mathlib

noncomputable section

open Real

/-! ## Correlation Kernel -/

/-- A correlation kernel on a type S: a function I : S → S → ℝ satisfying
    symmetry, strict positivity, normalization, and boundedness. -/
structure CorrKernel (S : Type*) where
  I : S → S → ℝ
  symm : ∀ i j, I i j = I j i
  pos : ∀ i j, 0 < I i j
  norm : ∀ i, I i i = 1
  bound : ∀ i j, I i j ≤ 1

/-- A correlation kernel satisfying the multiplicative triangle inequality:
    I(i,k) ≥ I(i,j) * I(j,k) for all i, j, k. -/
structure CorrKernelTriangle (S : Type*) extends CorrKernel S where
  mult_triangle : ∀ i j k, I i k ≥ I i j * I j k

/-- A separating correlation kernel: I(i,j) = 1 ↔ i = j. -/
structure CorrKernelSep (S : Type*) extends CorrKernelTriangle S where
  sep : ∀ i j, I i j = 1 ↔ i = j

/-! ## Emergent Distance -/

/-- The emergent distance induced by a correlation kernel:
    d(i,j) = -log(I(i,j)). -/
def emergentDist {S : Type*} (K : CorrKernel S) (i j : S) : ℝ :=
  -Real.log (K.I i j)

/-! ## Coupling / Locality Kernels -/

/-- General coupling kernel: H(i,j) = f(d(i,j)). -/
def couplingKernel {S : Type*} (K : CorrKernel S) (f : ℝ → ℝ) (i j : S) : ℝ :=
  f (emergentDist K i j)

/-- Exponential coupling: H(i,j) = exp(-d(i,j)). -/
def expCoupling {S : Type*} (K : CorrKernel S) (i j : S) : ℝ :=
  Real.exp (-(emergentDist K i j))

/-- Rational coupling: H(i,j) = 1/(1 + d(i,j)). -/
def ratCoupling {S : Type*} (K : CorrKernel S) (i j : S) : ℝ :=
  1 / (1 + emergentDist K i j)

/-! ## Metric Ball -/

/-- The closed ball of radius r around point i in the emergent metric. -/
def emergentBall {S : Type*} (K : CorrKernel S) (i : S) (r : ℝ) : Set S :=
  {j : S | emergentDist K i j ≤ r}

/-- The cardinality of a metric ball (for Fintype S). -/
def emergentBallCard {S : Type*} [Fintype S] [DecidableEq S] (K : CorrKernel S)
    (i : S) (r : ℝ) : ℕ :=
  Finset.card (Finset.filter (fun j => decide (emergentDist K i j ≤ r) = true) Finset.univ)

end

