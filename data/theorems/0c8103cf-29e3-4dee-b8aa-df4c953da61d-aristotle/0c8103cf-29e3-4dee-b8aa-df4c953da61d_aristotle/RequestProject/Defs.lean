import Mathlib

/-!
# Common-Origin Unification: Core Definitions

We define a single `RelationalOrigin` structure from which geometry (metric),
causality (strict partial order), and Bell correlations (CHSH violation + no-signaling)
all emerge.
-/

open Real

noncomputable section

/-- A relational origin structure on a finite type `S`, packaging:
  - A cost/distance function `D : S → S → ℝ` satisfying pseudometric axioms
  - A time function `τ : S → ℝ` providing causal directionality
  - A propagation speed `v > 0`
  - A phase parameter `phaseParam` governing Bell correlations -/
structure RelationalOrigin (S : Type*) where
  /-- Cost / action / distance function -/
  D : S → S → ℝ
  /-- D is nonneg -/
  D_nonneg : ∀ i j, 0 ≤ D i j
  /-- D(i,i) = 0 -/
  D_self : ∀ i, D i i = 0
  /-- D is symmetric -/
  D_symm : ∀ i j, D i j = D j i
  /-- D satisfies the triangle inequality -/
  D_triangle : ∀ i j k, D i k ≤ D i j + D j k
  /-- Time function for causal directionality -/
  τ : S → ℝ
  /-- Propagation speed -/
  v : ℝ
  /-- Speed is positive -/
  v_pos : 0 < v
  /-- Phase parameter for Bell correlations (derived from relational data) -/
  phaseParam : ℝ

variable {S : Type*} (R : RelationalOrigin S)

/-- The symmetric correlation kernel: I_R(i,j) = exp(-D(i,j)) -/
def RelationalOrigin.I_R (i j : S) : ℝ := exp (-R.D i j)

/-- The emergent distance: d_R(i,j) = -log(I_R(i,j)) -/
def RelationalOrigin.d_R (i j : S) : ℝ := -log (R.I_R i j)

/-- The coupling strength kernel: H_R(i,j) = exp(-d_R(i,j)) = I_R(i,j) -/
def RelationalOrigin.H_R (i j : S) : ℝ := exp (-R.d_R i j)

/-- The propagation kernel is positive iff D(i,j) ≤ v * t -/
def RelationalOrigin.K_pos (t : ℝ) (i j : S) : Prop := R.D i j ≤ R.v * t

/-- Causal precedence: i ≺ j iff τ(i) < τ(j) and signal can propagate from i to j -/
def RelationalOrigin.causal (i j : S) : Prop :=
  R.τ i < R.τ j ∧ R.D i j ≤ R.v * (R.τ j - R.τ i)

/-- The CHSH correlator: E_R(a,b) = cos(phaseParam) for (a,b) ≠ (1,1),
    E_R(1,1) = -cos(phaseParam) -/
def RelationalOrigin.E_R (a b : Fin 2) : ℝ :=
  if a = 1 ∧ b = 1 then -cos R.phaseParam else cos R.phaseParam

/-- The CHSH value: S_R = E(0,0) + E(0,1) + E(1,0) - E(1,1) -/
def RelationalOrigin.CHSH_val : ℝ :=
  R.E_R 0 0 + R.E_R 0 1 + R.E_R 1 0 - R.E_R 1 1

/-- Joint probability for outcomes (x,y) ∈ {true,false}² given settings (a,b).
    P(x,y|a,b) = (1 + (-1)^[x≠y] · E(a,b)) / 4
    where true ↔ +1, false ↔ -1 -/
def RelationalOrigin.P_joint (a b : Fin 2) (x y : Bool) : ℝ :=
  if x == y then (1 + R.E_R a b) / 4 else (1 - R.E_R a b) / 4

/-- Alice's marginal probability for outcome x -/
def RelationalOrigin.P_Alice (a b : Fin 2) (x : Bool) : ℝ :=
  R.P_joint a b x true + R.P_joint a b x false

/-- Bob's marginal probability for outcome y -/
def RelationalOrigin.P_Bob (a b : Fin 2) (y : Bool) : ℝ :=
  R.P_joint a b true y + R.P_joint a b false y

/-- A nonseparability invariant measuring how much the phase parameter
    deviates from classically achievable values -/
def RelationalOrigin.η : ℝ := |cos R.phaseParam|

end
