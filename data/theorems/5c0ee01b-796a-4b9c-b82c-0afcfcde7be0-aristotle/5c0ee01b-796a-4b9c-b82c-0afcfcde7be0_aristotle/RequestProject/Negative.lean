/-
  Causal Order as Extra Relational Data on Emergent Metric Geometry
  Part II & V: Negative Theorems and Toy Models

  Proves that metric structure alone does not determine causal order.
-/
import Mathlib
import RequestProject.Defs

noncomputable section

open Real

/-! ## Toy Model A: Two-Point Space -/

/-- Two-point metric space with constant distance. -/
def twoPointDist : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else 1

theorem twoPointDist_nonneg (i j : Fin 2) : 0 ≤ twoPointDist i j := by
  simp [twoPointDist]; split <;> norm_num

theorem twoPointDist_self (i : Fin 2) : twoPointDist i i = 0 := by
  simp [twoPointDist]

theorem twoPointDist_symm (i j : Fin 2) : twoPointDist i j = twoPointDist j i := by
  simp [twoPointDist]; split <;> split <;> simp_all

/-
PROVIDED SOLUTION
Case analysis on Fin 2 values. All cases are trivially 0 ≤ 0+0, 1 ≤ 0+1, 1 ≤ 1+0, or 0 ≤ 1+1. Use interval_cases or fin_cases.
-/
theorem twoPointDist_triangle (i j k : Fin 2) :
    twoPointDist i k ≤ twoPointDist i j + twoPointDist j k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [ twoPointDist ]

/-- Causal order 1 on Fin 2: 0 ≺ 1. -/
def causalOrder1 : CausalRelation (Fin 2) where
  rel := fun i j => i = 0 ∧ j = 1
  irrefl := by intro i ⟨h1, h2⟩; omega
  trans := by intro i j k ⟨h1, h2⟩ ⟨h3, h4⟩; omega

/-- Causal order 2 on Fin 2: 1 ≺ 0. -/
def causalOrder2 : CausalRelation (Fin 2) where
  rel := fun i j => i = 1 ∧ j = 0
  irrefl := by intro i ⟨h1, h2⟩; omega
  trans := by intro i j k ⟨h1, h2⟩ ⟨h3, h4⟩; omega

/-
PROBLEM
The two causal orders are distinct.

PROVIDED SOLUTION
causalOrder1.rel 0 1 is true (0=0 ∧ 1=1), but causalOrder2.rel 0 1 requires 0=1 which is false. So they differ at (0,1). Use funext and show they differ at specific points.
-/
theorem causal_orders_distinct : causalOrder1.rel ≠ causalOrder2.rel := by
  exact fun h => by have := congr_fun ( congr_fun h 0 ) 1; simp +decide [ causalOrder1, causalOrder2 ] at this;

/-! ## Theorem 1: Metric alone does not determine causal order.
    Same metric admits two distinct strict orders. -/

/-- **Theorem 1**: The same metric on a two-point space is compatible with two
    distinct causal orders, proving that metric alone does not determine causality. -/
theorem metric_does_not_determine_causality :
    ∃ (C₁ C₂ : CausalRelation (Fin 2)),
      C₁.rel ≠ C₂.rel ∧
      (∀ i j, twoPointDist i j = twoPointDist i j) := by
  exact ⟨causalOrder1, causalOrder2, causal_orders_distinct, fun _ _ => rfl⟩

/-! ## Theorem 2: Isometries obstruct canonical causal order -/

/-- The swap isometry on Fin 2. -/
def swapFin2 : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

/-
PROBLEM
swapFin2 is an isometry of twoPointDist.

PROVIDED SOLUTION
Case analysis on i, j in Fin 2. swapFin2 swaps 0↔1, and twoPointDist only depends on whether i=j. If i=j then swapFin2 i = swapFin2 j, so both sides are 0. If i≠j then swapFin2 i ≠ swapFin2 j, so both sides are 1. Use fin_cases.
-/
theorem swapFin2_isometry (i j : Fin 2) :
    twoPointDist (swapFin2 i) (swapFin2 j) = twoPointDist i j := by
      fin_cases i <;> fin_cases j <;> rfl

/-
PROBLEM
swapFin2 is not the identity.

PROVIDED SOLUTION
swapFin2 0 = 1 ≠ 0 = id 0. Use funext_iff and show they differ at 0.
-/
theorem swapFin2_ne_id : swapFin2 ≠ id := by
  exact fun h => by have := congr_fun h 0; simp +decide at this;

/-
PROBLEM
**Theorem 2**: No strict total order on Fin 2 is invariant under the swap isometry.
    Any strict total order, when both elements are mapped by the swap, violates asymmetry.

PROVIDED SOLUTION
Suppose r exists satisfying irrefl, asymmetry, totality, and swap-invariance. By totality applied to 0 and 1 (which are distinct in Fin 2), either r 0 1 or r 1 0. Case 1: r 0 1. By swap-invariance, r (swapFin2 0) (swapFin2 1) = r 1 0. So r 1 0 holds. But by asymmetry, r 0 1 → ¬ r 1 0, contradiction. Case 2: r 1 0. By swap-invariance, r (swapFin2 1) (swapFin2 0) = r 0 1. So r 0 1 holds. But by asymmetry, r 1 0 → ¬ r 0 1, contradiction. Use fin_cases or decide for the Fin 2 computations.
-/
theorem isometry_obstructs_canonical_order :
    ¬ ∃ (r : Fin 2 → Fin 2 → Prop),
      (∀ i, ¬ r i i) ∧                           -- irreflexive
      (∀ i j, r i j → ¬ r j i) ∧                 -- asymmetric
      (∀ i j, r i j ∨ r j i ∨ i = j) ∧           -- total
      (∀ i j, r i j → r (swapFin2 i) (swapFin2 j)) := by
        unfold swapFin2; aesop;

/-! ## Theorem 3: Symmetric kernels cannot encode causal orientation -/

/-- A "causal configuration" bundles a symmetric kernel with a causal relation. -/
structure CausalConfig (S : Type*) where
  kernel : SymmetricKernel S
  causal : CausalRelation S

/-- Reversing a causal relation. -/
def CausalRelation.reverse {S : Type*} (C : CausalRelation S) : CausalRelation S where
  rel := fun i j => C.rel j i
  irrefl := C.irrefl
  trans := fun i j k hij hjk => C.trans k j i hjk hij

/-- **Theorem 3**: A symmetric kernel is invariant under reversal of the causal order.
    This means the kernel alone cannot distinguish a causal configuration from its reversal. -/
theorem symmetric_kernel_invariant_under_reversal {S : Type*} (cfg : CausalConfig S) :
    cfg.kernel.I = (CausalConfig.mk cfg.kernel cfg.causal.reverse).kernel.I := by
  rfl

/-
PROBLEM
**Theorem 3 (strengthened)**: For any symmetric kernel I and causal relation C,
    the reversal of C yields a different causal relation (when C is nontrivial)
    but the same kernel values. Thus I cannot distinguish the two.

PROVIDED SOLUTION
Construct a specific SymmetricKernel on Fin 2: I(0,0)=I(1,1)=1, I(0,1)=I(1,0)=1/2. Use causalOrder1 (0≺1). Its reverse is 1≺0 (causalOrder2). Show C.rel ≠ C.reverse.rel by the same argument as causal_orders_distinct: C.rel 0 1 is true but C.reverse.rel 0 1 = C.rel 1 0 is false. The kernel values are trivially the same (rfl).
-/
theorem symmetric_kernel_cannot_encode_orientation :
    ∃ (K : SymmetricKernel (Fin 2)) (C : CausalRelation (Fin 2)),
      C.rel ≠ C.reverse.rel ∧
      (∀ i j, K.I i j = K.I i j) := by
        fconstructor;
        refine' ⟨ fun _ _ ↦ 1, _, _, _, _, _ ⟩ <;> norm_num;
        use causalOrder1;
        simp +decide [ funext_iff, CausalRelation.reverse ];
        simp +decide [ causalOrder1 ]

/-! ## Toy Model B: Three-Point Line -/

/-- Three-point line metric: d(i,j) = |i - j|. -/
def threePointDist : Fin 3 → Fin 3 → ℝ :=
  fun i j => |(i : ℤ) - (j : ℤ)|

/-- Forward causal order on three points: 0 ≺ 1 ≺ 2. -/
def threePointForward : CausalRelation (Fin 3) where
  rel := fun i j => (i : ℕ) < (j : ℕ)
  irrefl := by intro i h; exact Nat.lt_irrefl _ h
  trans := by intro i j k h1 h2; exact Nat.lt_trans h1 h2

/-- Backward causal order on three points: 2 ≺ 1 ≺ 0. -/
def threePointBackward : CausalRelation (Fin 3) where
  rel := fun i j => (j : ℕ) < (i : ℕ)
  irrefl := by intro i h; exact Nat.lt_irrefl _ h
  trans := by intro i j k h1 h2; exact Nat.lt_trans h2 h1

/-
PROBLEM
The forward and backward orders on three points are distinct.

PROVIDED SOLUTION
threePointForward.rel 0 1 is (0:ℕ) < (1:ℕ) = True, but threePointBackward.rel 0 1 is (1:ℕ) < (0:ℕ) = False. So they differ at (0,1). Use funext and decide, or show the specific point.
-/
theorem threePoint_orders_distinct :
    threePointForward.rel ≠ threePointBackward.rel := by
      simp +decide [ funext_iff, threePointForward, threePointBackward ]

/-- Reversing the order on a three-point line still gives a valid causal structure
    on the same metric, demonstrating underdetermination. -/
theorem threePoint_same_metric_different_orders :
    ∃ (C₁ C₂ : CausalRelation (Fin 3)),
      C₁.rel ≠ C₂.rel ∧
      (∀ i j : Fin 3, threePointDist i j = threePointDist i j) :=
  ⟨threePointForward, threePointBackward, threePoint_orders_distinct, fun _ _ => rfl⟩

/-! ## Toy Model C: Four-Point Cycle -/

/-- Four-point cycle metric: d(i,j) = min(|i-j|, 4-|i-j|) on Fin 4. -/
def cyclePointDist : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    let diff := ((i : ℤ) - (j : ℤ)).natAbs
    (min diff (4 - diff) : ℝ)

/-- First causal order on four-point cycle: 0 ≺ 1 ≺ 2 ≺ 3. -/
def cycleOrder1 : CausalRelation (Fin 4) where
  rel := fun i j => (i : ℕ) < (j : ℕ)
  irrefl := by intro i h; exact Nat.lt_irrefl _ h
  trans := by intro i j k h1 h2; exact Nat.lt_trans h1 h2

/-- Second causal order on four-point cycle: 0 ≺ 3 ≺ 2 ≺ 1. -/
def cycleOrder2 : CausalRelation (Fin 4) where
  rel := fun i j => (j : ℕ) < (i : ℕ)
  irrefl := by intro i h; exact Nat.lt_irrefl _ h
  trans := by intro i j k h1 h2; exact Nat.lt_trans h2 h1

/-
PROBLEM
The cycle metric admits multiple distinct causal orders.

PROVIDED SOLUTION
Use cycleOrder1 and cycleOrder2. They differ because cycleOrder1.rel 0 1 is (0:ℕ) < (1:ℕ) = true, while cycleOrder2.rel 0 1 is (1:ℕ) < (0:ℕ) = false. Same argument as threePoint_orders_distinct.
-/
theorem cycle_multiple_orders :
    ∃ (C₁ C₂ : CausalRelation (Fin 4)),
      C₁.rel ≠ C₂.rel := by
        fconstructor;
        use fun i j => ( j : ℕ ) < ( i : ℕ );
        all_goals norm_cast;
        exact ⟨ ⟨ fun i j => False, by tauto, by tauto ⟩, fun h => by have := congr_fun ( congr_fun h 1 ) 0; norm_num at this ⟩

end