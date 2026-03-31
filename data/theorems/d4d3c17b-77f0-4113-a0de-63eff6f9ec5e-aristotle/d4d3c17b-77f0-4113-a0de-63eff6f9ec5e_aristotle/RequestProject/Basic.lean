/-
# Deriving Causal Order from Propagation Kernels

## Basic Definitions

This file contains the core definitions:
- Symmetric correlation kernel and its emergent metric
- Time-indexed propagation kernel
- Derived causal order from propagation support
-/
import Mathlib

open Finset BigOperators Real Classical

noncomputable section

/-! ## Symmetric Correlation Kernel -/

/-- A symmetric correlation kernel on a finite type `S`.
    Satisfies positivity, normalization, symmetry, and supermultiplicativity. -/
structure CorrelationKernel (S : Type*) [Fintype S] [DecidableEq S] where
  I : S → S → ℝ
  pos : ∀ i j, 0 < I i j
  le_one : ∀ i j, I i j ≤ 1
  diag : ∀ i, I i i = 1
  symm : ∀ i j, I i j = I j i
  supermul : ∀ i j k, I i k ≥ I i j * I j k

/-- The emergent metric derived from a correlation kernel: d(i,j) = -log I(i,j) -/
def CorrelationKernel.d {S : Type*} [Fintype S] [DecidableEq S]
    (C : CorrelationKernel S) (i j : S) : ℝ :=
  -Real.log (C.I i j)

/-! ## Properties of the emergent metric -/

namespace CorrelationKernel

variable {S : Type*} [Fintype S] [DecidableEq S] (C : CorrelationKernel S)

/-
PROVIDED SOLUTION
d(i,j) = -log I(i,j). Since 0 < I(i,j) ≤ 1, we have log I(i,j) ≤ 0, so -log I(i,j) ≥ 0.
-/
lemma d_nonneg (i j : S) : 0 ≤ C.d i j := by
  exact neg_nonneg_of_nonpos ( Real.log_nonpos ( le_of_lt ( C.pos i j ) ) ( C.le_one i j ) )

/-
PROVIDED SOLUTION
d(i,i) = -log I(i,i) = -log 1 = 0. Use C.diag.
-/
lemma d_self (i : S) : C.d i i = 0 := by
  simp +decide [ CorrelationKernel.d, C.diag ]

/-
PROVIDED SOLUTION
d(i,j) = -log I(i,j) = -log I(j,i) = d(j,i). Use C.symm.
-/
lemma d_symm (i j : S) : C.d i j = C.d j i := by
  unfold CorrelationKernel.d; rw [ C.symm ] ;

/-
PROVIDED SOLUTION
We need d(i,k) ≤ d(i,j) + d(j,k), i.e. -log I(i,k) ≤ -log I(i,j) + (-log I(j,k)) = -log(I(i,j) * I(j,k)). Since log is monotone and I(i,k) ≥ I(i,j)*I(j,k) (supermultiplicativity), we have log I(i,k) ≥ log(I(i,j)*I(j,k)), so -log I(i,k) ≤ -log(I(i,j)*I(j,k)) = -log I(i,j) - log I(j,k). Use Real.log_mul_le for the product, or Real.log_le_log for monotonicity of log, plus C.supermul and C.pos.
-/
lemma d_triangle (i j k : S) : C.d i k ≤ C.d i j + C.d j k := by
  -- By the properties of logarithms, we have:
  -- $- \log I(i,k) \leq - (\log I(i,j) + \log I(j,k)) = - \log I(i,j) - \log I(j,k)$
  have h_log : Real.log (C.I i k) ≥ Real.log (C.I i j) + Real.log (C.I j k) := by
    rw [ ← Real.log_mul ( ne_of_gt ( C.pos i j ) ) ( ne_of_gt ( C.pos j k ) ) ] ; exact Real.log_le_log ( mul_pos ( C.pos i j ) ( C.pos j k ) ) ( by nlinarith [ C.pos i j, C.pos j k, C.pos i k, C.le_one i j, C.le_one j k, C.le_one i k, C.supermul i j k ] ) ;
  unfold CorrelationKernel.d; linarith;

end CorrelationKernel

/-! ## Time-indexed Propagation Kernel -/

/-- A time-indexed propagation kernel on a finite type `S` with discrete time `ℕ`.
    Satisfies nonnegativity, identity at zero, and semigroup composition. -/
structure PropagationKernel (S : Type*) [Fintype S] [DecidableEq S] where
  K : ℕ → S → S → ℝ
  nonneg : ∀ t i j, 0 ≤ K t i j
  identity : ∀ i j, K 0 i j = if i = j then 1 else 0
  semigroup : ∀ t s i j, K (t + s) i j = ∑ k : S, K t i k * K s k j

/-! ## Derived Causal Order -/

/-- The causal relation derived from a propagation kernel:
    i ≺_K j iff there exists t > 0 such that K_t(i,j) > 0 -/
def PropagationKernel.causal {S : Type*} [Fintype S] [DecidableEq S]
    (P : PropagationKernel S) (i j : S) : Prop :=
  ∃ t : ℕ, 0 < t ∧ 0 < P.K t i j

/-- Acyclicity condition: no positive-time self-propagation -/
def PropagationKernel.Acyclic {S : Type*} [Fintype S] [DecidableEq S]
    (P : PropagationKernel S) : Prop :=
  ∀ i : S, ∀ t : ℕ, 0 < t → P.K t i i = 0

/-! ## Causal Diamonds -/

/-- The causal diamond between two points a and b -/
def PropagationKernel.diamond {S : Type*} [Fintype S] [DecidableEq S]
    (P : PropagationKernel S) (a b : S) : Set S :=
  {x : S | P.causal a x ∧ P.causal x b}

/-! ## Compatibility Conditions -/

/-- Finite-speed propagation: K_t(i,j) > 0 implies d(i,j) ≤ v * t -/
def FiniteSpeedPropagation {S : Type*} [Fintype S] [DecidableEq S]
    (C : CorrelationKernel S) (P : PropagationKernel S) (v : ℝ) : Prop :=
  0 < v ∧ ∀ t : ℕ, ∀ i j : S, 0 < P.K t i j → C.d i j ≤ v * t

/-- Metric boundedness of causal diamonds -/
def MetricBoundedDiamonds {S : Type*} [Fintype S] [DecidableEq S]
    (C : CorrelationKernel S) (P : PropagationKernel S) : Prop :=
  ∀ a b : S, ∀ x ∈ P.diamond a b,
    C.d a x ≤ C.d a b ∧ C.d x b ≤ C.d a b

/-- Monotonicity along causal chains -/
def CausalMonotonicity {S : Type*} [Fintype S] [DecidableEq S]
    (C : CorrelationKernel S) (P : PropagationKernel S) : Prop :=
  ∀ a b c : S, P.causal a b → P.causal b c →
    C.d a c ≥ max (C.d a b) (C.d b c)

/-! ## Earliest arrival time -/

/-- The earliest arrival time from i to j, defined as the minimum t > 0
    such that K_t(i,j) > 0, or 0 if no such t exists.
    Note: This uses Classical.choice since causal is not decidable in general. -/
def PropagationKernel.earliestArrival {S : Type*} [Fintype S] [DecidableEq S]
    (P : PropagationKernel S) (i j : S) : ℕ :=
  if h : P.causal i j then h.choose else 0

end