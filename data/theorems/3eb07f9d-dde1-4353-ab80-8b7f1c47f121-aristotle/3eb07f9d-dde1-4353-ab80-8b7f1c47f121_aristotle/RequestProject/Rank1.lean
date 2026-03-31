/-
# Rank-1 CHSH Bound (Theorem 6 / Assumption E)

Rank-1 normalized PSD kernels G(i,j) = f(i) * f(j) with f : S → {-1, 1}
always satisfy |CHSH(G)| ≤ 2. This shows that "simple kernels are Bell-classical."
-/
import Mathlib
import RequestProject.Defs

/-! ## Rank-1 (deterministic) CHSH bound -/

/-
PROBLEM
For sign functions f : S → {-1, 1}, the induced CHSH value satisfies |CHSH| ≤ 2.
    This is the classical Bell bound.

PROVIDED SOLUTION
Case analysis on the four sign assignments. f(A₀), f(A₁), f(B₀), f(B₁) are each ±1. The expression is f(A₀)(f(B₀)+f(B₁)) + f(A₁)(f(B₀)-f(B₁)). When f(B₀)=f(B₁), the second term vanishes and |CHSH| = |2f(A₀)f(B₀)| = 2. When f(B₀)=-f(B₁), the first term vanishes and |CHSH| = |2f(A₁)f(B₀)| = 2. Either way |CHSH| = 2 ≤ 2.
-/
theorem rank1_chsh_le_two {S : Type*} (f : S → ℝ) (A₀ A₁ B₀ B₁ : S)
    (hf : ∀ s, f s = 1 ∨ f s = -1) :
    |f A₀ * f B₀ + f A₀ * f B₁ + f A₁ * f B₀ - f A₁ * f B₁| ≤ 2 := by
  rcases hf A₀ with ha | ha <;> rcases hf A₁ with hb | hb <;> rcases hf B₀ with hc | hc <;> rcases hf B₁ with hd | hd <;> rw [ ha, hb, hc, hd ] <;> norm_num [ abs_le ]

/-- Equivalent formulation: the CHSH functional applied to the rank-1 kernel G(i,j) = f(i)f(j). -/
theorem rank1_kernel_chsh_le_two {S : Type*} [Fintype S] (f : S → ℝ) (A₀ A₁ B₀ B₁ : S)
    (hf : ∀ s, f s = 1 ∨ f s = -1) :
    |CHSH_val (fun i j => f i * f j) A₀ A₁ B₀ B₁| ≤ 2 := by
  simp only [CHSH_val]
  exact rank1_chsh_le_two f A₀ A₁ B₀ B₁ hf

/-
PROBLEM
The rank-1 CHSH bound is tight: there exist sign assignments achieving |CHSH| = 2.

PROVIDED SOLUTION
Take f = ![1, 1, 1, 1]. Then f 0 * f 2 + f 0 * f 3 + f 1 * f 2 - f 1 * f 3 = 1 + 1 + 1 - 1 = 2.
-/
theorem rank1_chsh_tight :
    ∃ f : Fin 4 → ℝ, (∀ s, f s = 1 ∨ f s = -1) ∧
    |f 0 * f 2 + f 0 * f 3 + f 1 * f 2 - f 1 * f 3| = 2 := by
  exists fun s => if s = 0 then 1 else if s = 1 then -1 else if s = 2 then 1 else 1;
  grind