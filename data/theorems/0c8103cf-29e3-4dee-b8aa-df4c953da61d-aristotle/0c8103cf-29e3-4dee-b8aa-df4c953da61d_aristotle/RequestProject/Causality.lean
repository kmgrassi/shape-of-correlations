import RequestProject.Defs

/-!
# Part III: Causality from Common Origin

We prove that the propagation kernel K_t^R derived from D induces a
causal order ≺_R that is a strict partial order, and that finite-speed
compatibility holds.
-/

open Real

noncomputable section

variable {S : Type*} (R : RelationalOrigin S)

/-! ## Theorem 3: Causal order from propagation -/

/-
PROBLEM
The causal relation is irreflexive

PROVIDED SOLUTION
causal i i requires τ(i) < τ(i) which is false by lt_irrefl.
-/
theorem causal_irrefl (i : S) : ¬R.causal i i := by
  exact fun h => lt_irrefl _ h.1

/-
PROBLEM
The causal relation is transitive

PROVIDED SOLUTION
From hij: τ(i) < τ(j) and D(i,j) ≤ v·(τ(j)-τ(i)). From hjk: τ(j) < τ(k) and D(j,k) ≤ v·(τ(k)-τ(j)). We need τ(i) < τ(k) (by lt_trans) and D(i,k) ≤ v·(τ(k)-τ(i)). By triangle inequality: D(i,k) ≤ D(i,j) + D(j,k) ≤ v·(τ(j)-τ(i)) + v·(τ(k)-τ(j)) = v·(τ(k)-τ(i)). Use mul_sub and ring-like reasoning.
-/
theorem causal_trans (i j k : S) (hij : R.causal i j) (hjk : R.causal j k) :
    R.causal i k := by
      constructor;
      · exact lt_trans hij.1 hjk.1;
      · linarith [ hij.2, hjk.2, R.D_triangle i j k ]

/-
PROBLEM
The causal relation is asymmetric

PROVIDED SOLUTION
causal i j gives τ(i) < τ(j), causal j i gives τ(j) < τ(i), contradiction by lt_asymm.
-/
theorem causal_asymm (i j : S) (h : R.causal i j) : ¬R.causal j i := by
  exact fun h' => lt_asymm h.1 h'.1

/-
PROBLEM
The causal relation is a strict partial order (irreflexive + transitive)

PROVIDED SOLUTION
Direct from causal_irrefl and causal_trans.
-/
theorem causal_strict_partial_order :
    (∀ i, ¬R.causal i i) ∧
    (∀ i j k, R.causal i j → R.causal j k → R.causal i k) := by
      exact ⟨ fun i => by rintro ⟨ h₁, h₂ ⟩ ; linarith, fun i j k hij hjk => by exact? ⟩

/-! ## Theorem 4: Finite-speed compatibility from common origin -/

/-
PROBLEM
If the propagation kernel is positive at time t, then the emergent
    distance is at most v*t. This shows geometry and causality are
    compatible because they derive from the same D.

PROVIDED SOLUTION
K_pos t i j means D(i,j) ≤ v*t. By metric_emergence, d_R(i,j) = D(i,j), so d_R(i,j) ≤ v*t.
-/
theorem finite_speed_compat (i j : S) (t : ℝ) (ht : 0 < t)
    (hprop : R.K_pos t i j) : R.d_R i j ≤ R.v * t := by
      convert hprop using 1;
      unfold RelationalOrigin.d_R RelationalOrigin.K_pos;
      unfold RelationalOrigin.I_R; aesop;

/-
PROBLEM
Causal precedence implies finite emergent distance

PROVIDED SOLUTION
From h.2: D(i,j) ≤ v·(τ(j)-τ(i)). By metric_emergence, d_R(i,j) = D(i,j).
-/
theorem causal_implies_finite_distance (i j : S) (h : R.causal i j) :
    R.d_R i j ≤ R.v * (R.τ j - R.τ i) := by
      convert h.2 using 1;
      -- By definition of $d_R$, we have $d_R(i, j) = -\log(I_R(i, j))$.
      rw [RelationalOrigin.d_R];
      -- By definition of $I_R$, we have $I_R i j = \exp(-R.D i j)$.
      simp [RelationalOrigin.I_R]

end