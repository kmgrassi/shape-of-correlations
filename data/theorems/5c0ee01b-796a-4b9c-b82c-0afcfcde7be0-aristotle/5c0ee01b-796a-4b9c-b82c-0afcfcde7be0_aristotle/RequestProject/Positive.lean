/-
  Causal Order as Extra Relational Data on Emergent Metric Geometry
  Part III & IV: Positive Theorems and Compatibility

  Proves that antisymmetric data suffices for causal order,
  and investigates compatibility conditions.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.Negative

noncomputable section

open Real

/-! ## Theorem 4: Antisymmetric kernel induces strict order -/

/-
PROBLEM
An antisymmetric kernel has A(i,i) = 0.

PROVIDED SOLUTION
From A(i,i) = -A(i,i), we get 2*A(i,i) = 0, so A(i,i) = 0. Use K.antisymm i i and linarith.
-/
theorem AntisymmetricKernel.diag_zero {S : Type*} (K : AntisymmetricKernel S) (i : S) :
    K.A i i = 0 := by
      linarith [ K.antisymm i i ]

/-
PROBLEM
The induced relation from an antisymmetric kernel is irreflexive.

PROVIDED SOLUTION
inducedRel i i means A(i,i) > 0. But diag_zero shows A(i,i) = 0. So 0 > 0 is false. Use diag_zero and linarith/lt_irrefl.
-/
theorem AntisymmetricKernel.inducedRel_irrefl {S : Type*} (K : AntisymmetricKernel S) (i : S) :
    ¬ K.inducedRel i i := by
      -- By definition of inducedRel, we have K.inducedRel i i if and only if K.A i i > 0.
      simp [AntisymmetricKernel.inducedRel];
      linarith [ AntisymmetricKernel.diag_zero K i ]

/-
PROBLEM
The induced relation from an antisymmetric kernel is asymmetric.

PROVIDED SOLUTION
If A(i,j) > 0, then A(j,i) = -A(i,j) < 0. So ¬(A(j,i) > 0). Use K.antisymm and linarith.
-/
theorem AntisymmetricKernel.inducedRel_asymm {S : Type*} (K : AntisymmetricKernel S)
    (i j : S) : K.inducedRel i j → ¬ K.inducedRel j i := by
      exact fun h1 h2 => by linarith [ K.antisymm i j, show K.A i j > 0 from h1, show K.A j i > 0 from h2 ] ;

/-
PROBLEM
Additional hypothesis: the induced relation is transitive.
    Under this assumption, the induced relation is a strict partial order.

PROVIDED SOLUTION
Construct a CausalRelation with rel = K.inducedRel. Irreflexivity is inducedRel_irrefl. Transitivity is htrans. Then ⟨this, rfl⟩.
-/
theorem antisymmetric_kernel_induces_strict_order {S : Type*} (K : AntisymmetricKernel S)
    (htrans : ∀ i j k : S, K.inducedRel i j → K.inducedRel j k → K.inducedRel i k) :
    ∃ C : CausalRelation S, C.rel = K.inducedRel := by
      exact ⟨ ⟨ _, AntisymmetricKernel.inducedRel_irrefl K, htrans ⟩, rfl ⟩

/-! ## Theorem 5: CausalMetric consistency -/

/-
PROBLEM
**Theorem 5**: Given a pseudometric and a strict partial order, we can form
    a well-defined CausalMetric structure.

PROVIDED SOLUTION
Just package the data: ⟨⟨d, hnn, hs, hsymm, htri, C⟩, rfl, rfl⟩.
-/
theorem causal_metric_consistency {S : Type*}
    (d : S → S → ℝ) (hnn : ∀ i j, 0 ≤ d i j) (hs : ∀ i, d i i = 0)
    (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (C : CausalRelation S) :
    ∃ CM : CausalMetric S, CM.d = d ∧ CM.causal = C := by
      -- We can construct the CausalMetric structure by providing the distance function d and the causal relation C.
      use ⟨d, hnn, hs, hsymm, htri, C⟩

/-! ## Theorem 6: Not every order is compatible with diamond boundedness -/

/-- A metric on Fin 3 where d(0,2) < d(0,1). -/
def incompatibleDist : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then 0
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1
    else 3

/-- An order where 0 ≺ 1 ≺ 2 on Fin 3. -/
def linearOrder3 : CausalRelation (Fin 3) where
  rel := fun i j => (i : ℕ) < (j : ℕ)
  irrefl := by intro i h; exact Nat.lt_irrefl _ h
  trans := by intro i j k h1 h2; exact Nat.lt_trans h1 h2

/-
PROBLEM
**Theorem 6**: Diamond boundedness can fail. Here 1 is in the causal diamond
    of (0,2) but d(0,1) = 3 > d(0,2) = 1, violating diamond boundedness.

PROVIDED SOLUTION
Use incompatibleDist and linearOrder3. Take a=0, b=2, x=1. Then linearOrder3.rel 0 1 (since 0<1) and linearOrder3.rel 1 2 (since 1<2), so 1 is in the diamond. But incompatibleDist 0 1 = 3 and incompatibleDist 0 2 = 1, so d(0,1) = 3 > 1 = d(0,2), violating diamond boundedness. Provide ⟨incompatibleDist, linearOrder3, 0, 2, 1, ...⟩.
-/
theorem diamond_boundedness_can_fail :
    ∃ (d : Fin 3 → Fin 3 → ℝ) (C : CausalRelation (Fin 3)),
      ∃ (a b x : Fin 3), C.rel a x ∧ C.rel x b ∧ ¬(d a x ≤ d a b) := by
        -- Choose $d$ and $C$ as defined in the provided solution.
        use incompatibleDist, linearOrder3
        use 0, 2, 1;
        simp +decide [ linearOrder3, incompatibleDist ]

/-! ## Theorem 7: Trivial order gives trivial causal structure -/

/-- The empty causal relation. -/
def emptyCausal (S : Type*) : CausalRelation S where
  rel := fun _ _ => False
  irrefl := fun _ h => h
  trans := fun _ _ _ h _ => h.elim

/-
PROBLEM
**Theorem 7**: With the empty causal relation, all causal diamonds are empty.

PROVIDED SOLUTION
Unfold causalDiamond and emptyCausal. The set becomes {x | False ∧ False} = ∅. Use ext, simp.
-/
theorem trivial_order_trivial_diamonds (S : Type*) (a b : S) :
    causalDiamond (emptyCausal S) a b = ∅ := by
      ext x
      simp [causalDiamond, emptyCausal]

/-! ## Theorem 8: Total order is generically too strong -/

/-
PROBLEM
**Theorem 8**: For the 4-point cycle metric, no strict total order satisfies
    geodesic compatibility (d(a,c) ≥ max(d(a,b), d(b,c)) for a ≺ b ≺ c),
    since the cycle metric has d(0,2) = d(2,0) = 2 but intermediate distances are 1.

PROVIDED SOLUTION
Suppose r is a strict total order on Fin 4 satisfying geodesic compatibility. The cycle metric has d(i,j) = min(|i-j|, 4-|i-j|). Distances: d(0,1)=d(1,2)=d(2,3)=d(0,3)=1, d(0,2)=d(1,3)=2. Consider the 4 elements. By totality, r gives a linear ordering σ(0) ≺ σ(1) ≺ σ(2) ≺ σ(3). Consider the three consecutive pairs in this order: σ(0)≺σ(1)≺σ(2). Geodesic compatibility requires d(σ(0),σ(2)) ≥ max(d(σ(0),σ(1)), d(σ(1),σ(2))). Similarly for σ(1)≺σ(2)≺σ(3). And σ(0)≺σ(1)≺σ(3) gives d(σ(0),σ(3)) ≥ max(d(σ(0),σ(1)), d(σ(1),σ(3))). By case analysis on the 24 total orderings of Fin 4, one can check that each fails. For example, if the order is 0≺1≺2≺3: d(0,3)=1 but d(1,3)=2, so d(0,3) < d(1,3) = max(d(0,1), d(1,3)), violating the condition for 0≺1≺3. Use intro, obtain the hypotheses, and derive contradiction by considering the chain that includes antipodal elements. Specifically: in any total order on 4 elements, there must be a≺b≺c where d(a,c) < d(a,b) or d(a,c) < d(b,c), since the cycle metric doesn't satisfy the monotonicity required. The key insight: take the first and third elements in the total order. Their cycle distance might be smaller than the distance to the middle element. Use a case-analysis approach with fin_cases or omega.
-/
theorem total_order_too_strong_for_cycle :
    ¬ ∃ (r : Fin 4 → Fin 4 → Prop),
      (∀ i, ¬ r i i) ∧                             -- irreflexive
      (∀ i j k, r i j → r j k → r i k) ∧          -- transitive
      (∀ i j, r i j ∨ r j i ∨ i = j) ∧             -- total
      (∀ a b c, r a b → r b c →                    -- geodesic compatible
        cyclePointDist a c ≥ max (cyclePointDist a b) (cyclePointDist b c)) := by
          rintro ⟨ r, hr₁, hr₂, hr₃, hr₄ ⟩;
          simp_all +decide [ Fin.forall_fin_succ ];
          unfold cyclePointDist at hr₄ ; norm_num at hr₄;
          grind +ring

end