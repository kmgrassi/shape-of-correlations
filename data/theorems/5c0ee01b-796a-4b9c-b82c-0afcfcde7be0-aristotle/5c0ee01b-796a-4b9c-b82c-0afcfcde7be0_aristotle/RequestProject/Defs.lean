/-
  Causal Order as Extra Relational Data on Emergent Metric Geometry
  Part I: Core Definitions
-/
import Mathlib

noncomputable section

open Real

/-! ## 1. Symmetric Kernel and Emergent Metric -/

/-- A symmetric correlation kernel on a finite type `S`. -/
structure SymmetricKernel (S : Type*) where
  I : S → S → ℝ
  symm : ∀ i j, I i j = I j i
  pos : ∀ i j, 0 < I i j
  le_one : ∀ i j, I i j ≤ 1
  refl : ∀ i, I i i = 1
  supermul : ∀ i j k, I i k ≥ I i j * I j k

/-- The emergent distance function induced by a symmetric kernel. -/
def emergentDist {S : Type*} (K : SymmetricKernel S) (i j : S) : ℝ :=
  -Real.log (K.I i j)

/-! ## 2. Causal Layer -/

/-- A causal relation on `S`: a strict partial order. -/
structure CausalRelation (S : Type*) where
  rel : S → S → Prop
  irrefl : ∀ i, ¬ rel i i
  trans : ∀ i j k, rel i j → rel j k → rel i k

/-- Asymmetry follows from irreflexivity and transitivity. -/
theorem CausalRelation.asymm {S : Type*} (C : CausalRelation S)
    (i j : S) (h1 : C.rel i j) (h2 : C.rel j i) : False :=
  C.irrefl i (C.trans i j i h1 h2)

/-! ## 3. Causal-Metric Compatibility -/

/-- The causal diamond: the set of points causally between `a` and `b`. -/
def causalDiamond {S : Type*} (C : CausalRelation S) (a b : S) : Set S :=
  {x | C.rel a x ∧ C.rel x b}

/-- A CausalMetric structure combining metric and causal data. -/
structure CausalMetric (S : Type*) where
  d : S → S → ℝ
  d_nonneg : ∀ i j, 0 ≤ d i j
  d_self : ∀ i, d i i = 0
  d_symm : ∀ i j, d i j = d j i
  d_triangle : ∀ i j k, d i k ≤ d i j + d j k
  causal : CausalRelation S

/-- Diamond boundedness compatibility: points in a causal diamond are metrically bounded. -/
def DiamondBounded {S : Type*} (CM : CausalMetric S) : Prop :=
  ∀ a b : S, ∀ x : S, x ∈ causalDiamond CM.causal a b →
    CM.d a x ≤ CM.d a b ∧ CM.d x b ≤ CM.d a b

/-- Geodesic compatibility: causal chains are metrically monotone. -/
def GeodesicCompatible {S : Type*} (CM : CausalMetric S) : Prop :=
  ∀ a b c : S, CM.causal.rel a b → CM.causal.rel b c →
    CM.d a c ≥ max (CM.d a b) (CM.d b c)

/-! ## 4. Antisymmetric Kernel -/

/-- An antisymmetric kernel on `S`. -/
structure AntisymmetricKernel (S : Type*) where
  A : S → S → ℝ
  antisymm : ∀ i j, A i j = -A j i

/-- The causal relation induced by an antisymmetric kernel: i ≺ j ⟺ A(i,j) > 0. -/
def AntisymmetricKernel.inducedRel {S : Type*} (K : AntisymmetricKernel S) :
    S → S → Prop :=
  fun i j => K.A i j > 0

/-! ## 5. Time-Separation Function -/

/-- A time-separation function compatible with a causal relation. -/
structure TimeSeparation (S : Type*) where
  causal : CausalRelation S
  tau : S → S → ℝ
  tau_nonneg : ∀ i j, 0 ≤ tau i j
  tau_pos_imp_causal : ∀ i j, tau i j > 0 → causal.rel i j
  reverse_triangle : ∀ i j k, causal.rel i j → causal.rel j k →
    tau i k ≥ tau i j + tau j k

/-! ## 6. Directed Propagation Kernel -/

/-- A time-indexed directed propagation kernel. -/
structure PropagationKernel (S : Type*) where
  K : ℕ → S → S → ℝ
  K_nonneg : ∀ t i j, 0 ≤ K t i j

/-- The causal relation induced by a propagation kernel. -/
def PropagationKernel.inducedRel {S : Type*} (P : PropagationKernel S) :
    S → S → Prop :=
  fun i j => ∃ t : ℕ, t > 0 ∧ P.K t i j > 0 ∧ P.K t j i = 0

end
