/-
# Causal Compatibility and Counterexamples

## Main results:

1. **Counterexample**: A metric space admits many distinct partial orders,
   none determined by the metric alone. This shows that metric emergence
   (spatial/kinematic structure) does NOT imply causal order.

2. **Metric + order → Lorentzian-style structure**: Given a metric d and
   a partial order ≺, we define a "Lorentzian-like" interval structure
   and state conditions under which this yields causal diamonds.

3. **Necessary condition**: For metric + causal order to be "Lorentzian-like",
   the order must be compatible with the metric in specific ways.

These results clarify that the correlation-kernel framework gives
spatial/kinematic geometry, and causal structure requires additional
data (an antisymmetric relation or causal matrix).
-/
import Mathlib

open Finset

noncomputable section

/-! ## 1. Metric does not determine causal order -/

/-
PROBLEM
On any type with more than one element, both the discrete order
    (only x ≤ x) and a nontrivial linear order are consistent with
    the same metric. This shows the metric alone cannot determine
    causal structure.

    Concretely: Fin 2 with the discrete metric d(0,1) = d(1,0) = 1
    admits both orderings 0 < 1 and 1 < 0 as total orders, and also
    the trivial partial order. The metric is invariant under swapping
    0 and 1, so no ordering is "canonical".

PROVIDED SOLUTION
Use d(i,j) = if i = j then 0 else 1 (discrete metric on Fin 2). Metric axioms are straightforward. For the two orders, use r₁ = (fun i j => i = 0 ∧ j = 1) and r₂ = (fun i j => i = 1 ∧ j = 0). They are distinct (r₁ 0 1 is true, r₂ 0 1 is false). Verify the required properties by case analysis on Fin 2.
-/
theorem metric_does_not_determine_order :
    ∃ (d : Fin 2 → Fin 2 → ℝ),
      -- d is a metric
      (∀ i, d i i = 0) ∧
      (∀ i j, d i j = d j i) ∧
      (∀ i j, 0 ≤ d i j) ∧
      (∀ i j, d i j = 0 → i = j) ∧
      (∀ i j k, d i k ≤ d i j + d j k) ∧
      -- There exist two distinct total orders both compatible
      -- (i.e., the metric is the same regardless of which order we pick)
      (∃ (r₁ r₂ : Fin 2 → Fin 2 → Prop),
        -- r₁ and r₂ are distinct relations
        r₁ ≠ r₂ ∧
        -- r₁ is a strict total order (0 < 1)
        r₁ 0 1 ∧ ¬r₁ 1 0 ∧
        -- r₂ is a strict total order (1 < 0)
        r₂ 1 0 ∧ ¬r₂ 0 1) := by
          fconstructor;
          exact fun i j => if i = j then 0 else 1;
          simp +decide;
          exists fun i j => i = 0 ∧ j = 1, fun i j => i = 1 ∧ j = 0;
          simp +decide [ funext_iff ]

/-
PROBLEM
A metric space with a nontrivial isometry group cannot have
    a canonical partial order: any isometry-compatible order must
    identify isometric points.

PROVIDED SOLUTION
Proof by contradiction. Assume h_total: ∀ i j, i ≠ j → r i j ∨ r j i.

Since σ ≠ id, there exists v with σ v ≠ v (use Function.ne_iff.mp hσ_ne).

By h_total, since v ≠ σ v, either r v (σ v) or r (σ v) v. WLOG r v (σ v) (the other case: r (σ v) v, apply hr_compat to get r (σ (σ v)) (σ v), and iterate to get the same structure).

From r v (σ v), by hr_compat: r (σ v) (σ (σ v)) = r (σ v) (σ^[2] v).
By hr_trans: r v (σ^[2] v).
Continuing: r v (σ^[k] v) for all k ≥ 1 (by induction using hr_compat and hr_trans).

Since V is finite and σ is bijective, there exists n > 0 such that σ^[n] v = v (use Function.IsFixedPt.perm_pow or the fact that the orbit is finite).

Then r v (σ^[n] v) = r v v, contradicting hr_irrefl v.

Key lemma for iteration: prove by induction on k that r v (σ^[k+1] v), using hr_compat to get r (σ^[k] v) (σ^[k+1] v) and hr_trans to chain.

For the periodicity: σ viewed as Equiv.ofBijective gives a permutation, and (Equiv.ofBijective σ hσ_bij)^(Fintype.card V)! = 1, so σ^[n] = id for n = (Fintype.card V)!, giving σ^[n] v = v. Use Function.Bijective.iterate_eq_id or just that the order of any element divides the group order.
-/
theorem isometry_prevents_canonical_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ)
    (hd_metric : ∀ i, d i i = 0)
    (hd_symm : ∀ i j, d i j = d j i)
    -- σ is a nontrivial isometry
    (σ : V → V)
    (hσ_bij : Function.Bijective σ)
    (hσ_isom : ∀ i j, d (σ i) (σ j) = d i j)
    (hσ_ne : σ ≠ id)
    -- r is an "isometry-compatible" strict order
    (r : V → V → Prop)
    (hr_compat : ∀ i j, r i j → r (σ i) (σ j))
    (hr_irrefl : ∀ i, ¬r i i)
    (hr_asym : ∀ i j, r i j → ¬r j i)
    (hr_trans : ∀ i j k, r i j → r j k → r i k) :
    -- Then r cannot be a total order on V
    ¬(∀ i j, i ≠ j → r i j ∨ r j i) := by
      -- By contradiction, assume there exists a linear order compatible with the metric.
      by_contra h_linear_order
      -- Since σ is not the identity, there exists some v such that σ(v) ≠ v. Let's call this v.
      obtain ⟨v, hv⟩ : ∃ v, σ v ≠ v := by
        exact Function.ne_iff.mp hσ_ne
      -- By the assumption, since v ≠ σ(v), we have either r v (σ v) or r (σ v) v.
      have hvr : r v (σ v) ∨ r (σ v) v := by
        exact h_linear_order _ _ hv.symm
      -- Let's consider both cases.
      by_cases hv_case : r v (σ v);
      · -- By induction, we can show that $r v (\sigma^k v)$ holds for all $k \geq 1$.
        have h_ind : ∀ k : ℕ, 0 < k → r v (σ^[k] v) := by
          intro k hk; induction hk <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
          exact hr_trans _ _ _ ‹_› ( by rename_i k hk ih; exact Nat.recOn k ( by simpa ) fun n ihn => by simpa only [ Function.iterate_succ_apply' ] using hr_compat _ _ ihn ) ;
        -- Since σ is bijective, there exists some k such that σ^k v = v.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < k ∧ σ^[k] v = v := by
          -- Since σ is bijective, the sequence σ^k v must eventually repeat.
          have h_seq_repeat : ∃ k l : ℕ, k < l ∧ σ^[k] v = σ^[l] v := by
            by_contra h_no_repeat;
            exact absurd ( Set.infinite_range_of_injective ( fun k l hkl => le_antisymm ( not_lt.1 fun hlt => h_no_repeat ⟨ l, k, hlt, hkl.symm ⟩ ) ( not_lt.1 fun hlt => h_no_repeat ⟨ k, l, hlt, hkl ⟩ ) ) ) ( Set.not_infinite.mpr <| Set.toFinite _ );
          obtain ⟨ k, l, hkl, h ⟩ := h_seq_repeat;
          refine' ⟨ l - k, tsub_pos_of_lt hkl, _ ⟩;
          rw [ ← Nat.add_sub_of_le hkl.le, Function.iterate_add_apply ] at h;
          exact hσ_bij.injective.iterate _ h.symm;
        exact hr_irrefl v ( by simpa [ hk.2 ] using h_ind k hk.1 );
      · -- By induction, we can show that $r (σ^k v) v$ for all $k \geq 1$.
        have h_ind : ∀ k : ℕ, 1 ≤ k → r (σ^[k] v) v := by
          intro k hk; induction hk <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
          have := hr_compat _ _ ‹_›; aesop;
        -- Since $V$ is finite, there exists some $n > 0$ such that $\sigma^n(v) = v$.
        obtain ⟨n, hn_pos, hn_eq⟩ : ∃ n : ℕ, 0 < n ∧ σ^[n] v = v := by
          -- Since $σ$ is a bijection on a finite set, it must have finite order.
          have h_finite_order : ∃ n : ℕ, 0 < n ∧ σ^[n] = id := by
            have h_finite_order : ∃ n : ℕ, 0 < n ∧ (Equiv.ofBijective σ hσ_bij)^[n] = Equiv.refl V := by
              exact ⟨ orderOf ( Equiv.ofBijective σ hσ_bij ), orderOf_pos _, by simp +decide [ pow_orderOf_eq_one ] ⟩;
            aesop;
          exact ⟨ h_finite_order.choose, h_finite_order.choose_spec.1, congr_fun h_finite_order.choose_spec.2 v ⟩;
        grind +ring

/-! ## 2. Metric + order → Lorentzian-style structure -/

/-- A causal metric structure: a pseudometric plus a partial order
    that is "compatible" in the sense that causal curves have
    non-negative "proper time" (d along causal direction). -/
structure CausalMetric (V : Type*) extends PartialOrder V where
  d : V → V → ℝ
  d_self : ∀ i, d i i = 0
  d_symm : ∀ i j, d i j = d j i
  d_nonneg : ∀ i j, 0 ≤ d i j
  d_triangle : ∀ i j k, d i k ≤ d i j + d j k

/-- The causal diamond between two causally related points. -/
def CausalMetric.diamond {V : Type*} (C : CausalMetric V) (p q : V) : Set V :=
  {x | C.le p x ∧ C.le x q}

/-
PROBLEM
A causal diamond is contained in a metric ball, under causal monotonicity:
    if the order respects the metric in the sense that p ≤ x ≤ q implies
    d(p,x) + d(x,q) ≤ some bound, then points in the diamond are close to p.
    The natural hypothesis is d(p,x) + d(x,q) = d(p,q) ("geodesic order"),
    from which d(p,x) ≤ d(p,q) follows by nonnegativity of d(x,q).

PROVIDED SOLUTION
From hx: p ≤ x and x ≤ q. By h_geodesic p x q: d(p,x) + d(x,q) = d(p,q). Since d(x,q) ≥ 0 by C.d_nonneg, d(p,x) ≤ d(p,x) + d(x,q) = d(p,q). Use linarith.
-/
theorem diamond_in_ball {V : Type*} [Fintype V] (C : CausalMetric V) (p q : V)
    (hpq : C.le p q) (x : V) (hx : x ∈ C.diamond p q)
    (h_geodesic : ∀ a b c, C.le a b → C.le b c → C.d a b + C.d b c = C.d a c) :
    C.d p x ≤ C.d p q := by
      linarith [ h_geodesic p x q hx.1 hx.2, C.d_nonneg x q ]

/-! ## 3. Necessary conditions for Lorentzian-like behavior -/

/-
PROBLEM
For a causal metric to behave "Lorentzian-like", the causal order
    must be non-trivial (i.e., there exist distinct causally related points).

PROVIDED SOLUTION
If the order is trivial (x ≤ y → x = y), then the diamond {x | p ≤ x ∧ x ≤ q} only contains p (since p ≤ x → p = x). So diamond p q ⊆ {p}. For any x in the diamond, x ∈ {x | p ≤ x ∧ x ≤ q}, so p ≤ x, which gives x = p by h_trivial.
-/
theorem lorentzian_needs_nontrivial_order
    {V : Type*} [Fintype V] (C : CausalMetric V)
    (h_trivial : ∀ x y, C.le x y → x = y) :
    -- If the order is trivial, all causal diamonds are singletons
    ∀ p q, C.diamond p q ⊆ {p} := by
      grind +locals

end