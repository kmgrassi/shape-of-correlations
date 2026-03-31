/-
# Timeless Configuration Ensemble with Observer-Moment Measure

Formal verification of the mathematical framework for a timeless ensemble
of configurations equipped with a measure μ_X, inducing a probability
distribution over observer-moments, and determining conditions under which
low-entropy-history observer-moments dominate over fluctuation-based
(Boltzmann brain) observer-moments.
-/
import Mathlib

open MeasureTheory ENNReal Set

noncomputable section

/-! ## §1. Core Objects -/

/-- A `TimelessEnsemble` bundles the core mathematical objects of the thesis:
  - `X` : the configuration space (measurable space of complete physical states)
  - `D` : the space of possible observational data
  - `Obs` : for each configuration x, the (countable) set of observer-instances in x
  - `μ_X` : a measure on X (e.g. |Ψ(x)|² in quantum instantiations)
  - `obs` : maps each observer-moment to its observational data
-/
structure TimelessEnsemble where
  /-- Configuration space -/
  X : Type*
  /-- Measurable space structure on X -/
  msX : MeasurableSpace X
  /-- Observational data space -/
  D : Type*
  /-- Observer-instance type for each configuration -/
  Obs : X → Type*
  /-- The measure on configuration space (§1.2) -/
  μ_X : Measure X
  /-- Observation function mapping observer-moments to data (§1.5) -/
  obs : (Σ x, Obs x) → D

namespace TimelessEnsemble

variable (E : TimelessEnsemble)

/-- The observer-moment space O = {(x, i) | x ∈ X, i ∈ Obs(x)} (§1.3) -/
def ObserverSpace := Σ x : E.X, E.Obs x

/-- The set of observer-moments consistent with observed data D (§1.5):
    O_D = {o ∈ O | obs(o) = d} -/
def O_D (d : E.D) : Set E.ObserverSpace :=
  {o | E.obs o = d}

end TimelessEnsemble

/-! ## §5–6. Boltzmann Brain Domination

We now state and prove the core mathematical results about BB domination
in terms of abstract measure values, without requiring the full induced
measure construction (which would need additional measurability hypotheses).

The key insight: given measures of the normal and BB observer-moment sets,
the conditional probability formula and domination results follow from
elementary ENNReal arithmetic.
-/

/-- Configuration for the BB domination analysis.
    Given measures of the relevant observer-moment subsets, we can derive
    all the domination results. -/
structure BBAnalysis where
  /-- μ_O(O_D^normal) : measure of normal observer-moments matching data D -/
  μ_normal : ℝ≥0∞
  /-- μ_O(O_D^BB) : measure of Boltzmann brain observer-moments matching data D -/
  μ_BB : ℝ≥0∞

namespace BBAnalysis

variable (B : BBAnalysis)

/-- P(normal | D) as defined in §5:
    μ_O(O_D^normal) / (μ_O(O_D^normal) + μ_O(O_D^BB)) -/
def P_normal : ℝ≥0∞ :=
  B.μ_normal / (B.μ_normal + B.μ_BB)

/-- P(BB | D) := μ_O(O_D^BB) / (μ_O(O_D^normal) + μ_O(O_D^BB)) -/
def P_BB : ℝ≥0∞ :=
  B.μ_BB / (B.μ_normal + B.μ_BB)

/-! ### §6. Typical failure mode: BB domination when μ_BB = ∞ and μ_normal < ∞ -/

/-
PROBLEM
**Theorem (§6 — BB Domination).**
    If the measure of normal observer-moments is finite and the measure of
    BB observer-moments is infinite, then P(normal | D) = 0.
    This is the core pathology of infinite-volume cosmologies.

PROVIDED SOLUTION
Unfold P_normal. We need μ_normal / (μ_normal + μ_BB) = 0. Since μ_BB = ⊤, μ_normal + μ_BB = ⊤. Since μ_normal < ⊤, we have ENNReal.div_top or similar: a finite value divided by ⊤ is 0. Use ENNReal.div_eq_zero_iff or direct calculation.
-/
theorem bb_domination
    (_h_normal_fin : B.μ_normal < ⊤)
    (h_BB_inf : B.μ_BB = ⊤) :
    B.P_normal = 0 := by
  unfold BBAnalysis.P_normal; aesop;

/-
PROBLEM
**Corollary (corrected).** Under BB domination, P(BB | D) is also 0
    in the ENNReal convention (since ⊤/⊤ = 0 in ENNReal). This reflects
    the fact that the conditional probability is ill-defined (non-normalizable)
    when the total measure is infinite — the original thesis statement
    "P(BB|D) = 1" assumed real-valued arithmetic but ENNReal ⊤/⊤ = 0.
    The meaningful content is captured by `bb_domination`: P(normal|D) = 0.

PROVIDED SOLUTION
Unfold P_BB. Since μ_BB = ⊤, μ_normal + μ_BB = ⊤. So P_BB = ⊤ / ⊤ = 0 in ENNReal (by ENNReal.top_div_top or similar). Use simp with ENNReal lemmas.
-/
theorem bb_domination_complement
    (_h_normal_fin : B.μ_normal < ⊤)
    (h_BB_inf : B.μ_BB = ⊤) :
    B.P_BB = 0 := by
  unfold BBAnalysis.P_BB; aesop;

/-! ### §7. Required consistency condition -/

/-
PROBLEM
**Theorem (§7 — Consistency).**
    If μ_normal > 0 and μ_BB = 0, then P(normal | D) = 1.
    This is the ideal case where BB observer-moments have zero measure.

Note: the original statement without `h_normal_fin` is false because
   when μ_normal = ⊤ and μ_BB = 0, P_normal = ⊤/(⊤+0) = ⊤/⊤ = 0 in ENNReal.
   We add the finiteness hypothesis.

PROVIDED SOLUTION
Unfold P_normal. μ_BB = 0 so μ_normal + 0 = μ_normal. Need μ_normal / μ_normal = 1. Since μ_normal > 0 (hence ≠ 0) and μ_normal < ⊤ (hence ≠ ⊤), use ENNReal.div_self.
-/
theorem consistency_ideal
    (h_normal_pos : B.μ_normal > 0)
    (h_normal_fin : B.μ_normal < ⊤)
    (h_BB_zero : B.μ_BB = 0) :
    B.P_normal = 1 := by
  -- Substitute h_BB_zero into the definition of P_normal.
  have h_P_normal : B.P_normal = B.μ_normal / (B.μ_normal + 0) := by
    rw [ BBAnalysis.P_normal, h_BB_zero, add_zero ];
  -- Since μ_normal is positive and finite, dividing it by itself gives 1.
  have h_div : B.μ_normal / B.μ_normal = 1 := by
    rw [ ENNReal.div_self ] <;> aesop;
  aesop

/-
PROBLEM
P(normal | D) + P(BB | D) = 1 when the total measure is positive and finite.

PROVIDED SOLUTION
Unfold P_normal and P_BB. Need μ_normal/(μ_normal+μ_BB) + μ_BB/(μ_normal+μ_BB) = 1. Factor: (μ_normal + μ_BB)/(μ_normal+μ_BB) = 1. Use ENNReal.add_div and ENNReal.div_self. The total is positive and finite by hypothesis.
-/
theorem prob_sum_one
    (h_pos : B.μ_normal + B.μ_BB > 0)
    (h_fin : B.μ_normal + B.μ_BB < ⊤) :
    B.P_normal + B.P_BB = 1 := by
  rw [ BBAnalysis.P_normal, BBAnalysis.P_BB ];
  rw [ ← ENNReal.add_div, ENNReal.div_self ] <;> aesop

/-
PROBLEM
P(normal | D) is monotone decreasing in μ_BB (for fixed μ_normal).
    More BB observer-moments ⟹ lower probability of being normal.

PROVIDED SOLUTION
We need to show that μ_n / (μ_n + μ_bb) is antitone in μ_bb. As μ_bb increases, the denominator increases, so the fraction decreases. Use ENNReal.div_le_div_left and add_le_add_left.
-/
theorem P_normal_antitone_μ_BB (μ_n : ℝ≥0∞) :
    Antitone (fun μ_bb => ({ μ_normal := μ_n, μ_BB := μ_bb } : BBAnalysis).P_normal) := by
  intro μ_bb₁ μ_bb₂ h_le; by_cases hbb₂ : μ_n = 0 <;> by_cases hbb₁ : μ_bb₁ = 0 <;> by_cases hbb₂' : μ_bb₂ = 0 <;> simp_all +decide [ BBAnalysis.P_normal ] ;
  · gcongr ; aesop;
  · gcongr

/-! ### §8. Candidate modifications -/

/-
PROBLEM
**(A) Complexity-weighted measure.**
    If we apply a complexity penalty 2^{-K(x)} that makes μ_BB finite,
    and μ_normal remains positive and finite, then P(normal | D) > 0.

PROVIDED SOLUTION
Unfold P_normal and EmpiricallyViable. Need μ_normal / (μ_normal + μ_BB) > 0. Since μ_normal > 0 and μ_normal + μ_BB < ⊤ (both finite), the division is positive. Use ENNReal.div_pos.
-/
theorem complexity_weighting_restores_consistency
    (h_normal_pos : B.μ_normal > 0)
    (h_normal_fin : B.μ_normal < ⊤)
    (h_BB_fin : B.μ_BB < ⊤) :
    B.P_normal > 0 := by
  unfold BBAnalysis.P_normal;
  contrapose! h_normal_pos; aesop

/-
PROBLEM
**(B) Finite ensemble.**
    If total measure is finite, conditional probability is well-defined (< ⊤).

PROVIDED SOLUTION
Unfold P_normal. Need μ_normal / (μ_normal + μ_BB) ≤ 1. Since μ_normal ≤ μ_normal + μ_BB, use ENNReal.div_le_one_of_le or ENNReal.div_self_le_one, or note numerator ≤ denominator so division ≤ 1.
-/
theorem finite_ensemble_well_defined
    (_h_fin : B.μ_normal + B.μ_BB < ⊤) :
    B.P_normal ≤ 1 := by
  rw [ BBAnalysis.P_normal, ENNReal.div_le_iff_le_mul ] <;> aesop

end BBAnalysis

/-! ## §2. Conditional Probability / Typicality Principle

We formalize the conditional probability over observer-moments using
Mathlib's measure theory. For a measure space (Ω, μ) and a property P,
the conditional probability given data D is:

  P(P | D) = μ({o ∈ O_D : P(o)}) / μ(O_D)
-/

/-- Conditional probability of a property P given data D, expressed as
    the ratio of measures of the intersection to the conditioning set. -/
def condProb {α : Type*} [MeasurableSpace α] (μ : Measure α) (S P : Set α) : ℝ≥0∞ :=
  μ (S ∩ P) / μ S

/-
PROBLEM
Conditional probability is at most 1 when the conditioning set has
    positive finite measure.

PROVIDED SOLUTION
condProb μ S P = μ(S ∩ P) / μ(S). Since S ∩ P ⊆ S, μ(S ∩ P) ≤ μ(S). Since μ(S) > 0 and μ(S) < ⊤, division of a value ≤ μ(S) by μ(S) is ≤ 1. Use ENNReal.div_le_one or measure_mono.
-/
theorem condProb_le_one {α : Type*} [MeasurableSpace α] (μ : Measure α) (S P : Set α)
    (_hS_pos : μ S > 0) (_hS_fin : μ S < ⊤) :
    condProb μ S P ≤ 1 := by
  refine' ENNReal.div_le_of_le_mul _;
  simpa using MeasureTheory.measure_mono ( Set.inter_subset_left )

/-
PROBLEM
Conditional probability of the full conditioning set is 1.

PROVIDED SOLUTION
condProb μ S S = μ(S ∩ S) / μ(S) = μ(S) / μ(S). Since μ(S) > 0 (≠ 0) and μ(S) < ⊤ (≠ ⊤), use ENNReal.div_self.
-/
theorem condProb_self {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (hS_pos : μ S > 0) (hS_fin : μ S < ⊤) :
    condProb μ S S = 1 := by
  -- Since μ(S) is positive and finite, we can apply the lemma ENNReal.div_self.
  have h_div : μ S / μ S = 1 := by
    rw [ ENNReal.div_self hS_pos.ne' hS_fin.ne ];
  unfold condProb; aesop;

/-
PROBLEM
If P ⊆ S, conditional probability of P equals μ(P) / μ(S).

PROVIDED SOLUTION
condProb μ S P = μ(S ∩ P) / μ(S). Since P ⊆ S, S ∩ P = P. So it equals μ(P) / μ(S). Use Set.inter_eq_right.mpr h or inter_comm and inter_eq_left.
-/
theorem condProb_of_subset {α : Type*} [MeasurableSpace α] (μ : Measure α) (S P : Set α) (h : P ⊆ S) :
    condProb μ S P = μ P / μ S := by
  unfold condProb;
  rw [ Set.inter_eq_right.mpr h ]

/-! ## §3. Bell / Quantum Compatibility Constraint

We formalize the statement that the measure does not factorize into
local hidden variable distributions (Bell's theorem). -/

/-- A joint probability distribution P(A, B | a, b, λ) factorizes into
    local hidden variables iff it can be written as P(A|a,λ) · P(B|b,λ). -/
def BellLocalFactorizable
    (A B Setting HiddenVar : Type*) [MeasurableSpace HiddenVar]
    (P_joint : A → B → Setting → Setting → HiddenVar → ℝ≥0∞)
    (P_A : A → Setting → HiddenVar → ℝ≥0∞)
    (P_B : B → Setting → HiddenVar → ℝ≥0∞) : Prop :=
  ∀ a b s_a s_b hv, P_joint a b s_a s_b hv = P_A a s_a hv * P_B b s_b hv

/-- The thesis asserts that quantum configurations are NOT Bell-local factorizable (§3).
    This is stated as the negation of factorizability. -/
def BellNonlocal
    (A B Setting HiddenVar : Type*) [MeasurableSpace HiddenVar]
    (P_joint : A → B → Setting → Setting → HiddenVar → ℝ≥0∞)  : Prop :=
  ¬ ∃ (P_A : A → Setting → HiddenVar → ℝ≥0∞)
      (P_B : B → Setting → HiddenVar → ℝ≥0∞),
    BellLocalFactorizable A B Setting HiddenVar P_joint P_A P_B

/-! ## §9–10. Open Problems and Core Thesis

The core thesis: a timeless ensemble (X, μ_X) induces a measure on
observer-moments (O, μ_O). The model is empirically viable iff typical
observer-moments matching data D arise from coherent low-entropy histories
rather than Boltzmann fluctuations.

We formalize the key condition for empirical viability. -/

/-- A `BBAnalysis` is **empirically viable** if P(normal | D) > 0,
    meaning normal observer-moments have positive conditional probability. -/
def BBAnalysis.EmpiricallyViable (B : BBAnalysis) : Prop :=
  B.P_normal > 0

/-- A `BBAnalysis` is **pathological** (BB-dominated) if P(normal | D) = 0. -/
def BBAnalysis.Pathological (B : BBAnalysis) : Prop :=
  B.P_normal = 0

/-
PROBLEM
Empirical viability and pathology are mutually exclusive.

PROVIDED SOLUTION
EmpiricallyViable is P_normal > 0 and Pathological is P_normal = 0. These are pos_iff_ne_zero in ENNReal.
-/
theorem BBAnalysis.viable_iff_not_pathological (B : BBAnalysis) :
    B.EmpiricallyViable ↔ ¬ B.Pathological := by
  unfold BBAnalysis.EmpiricallyViable BBAnalysis.Pathological;
  exact pos_iff_ne_zero

/-
PROBLEM
**Core Thesis (§10).** The model is empirically viable if and only if
    the measure of normal observer-moments is positive and the ratio
    μ_normal / (μ_normal + μ_BB) is positive.

Note: The original formulation included `B.μ_normal = ⊤` as a disjunct,
   but this is false: when μ_normal = ⊤, P_normal = ⊤/(⊤+μ_BB) = ⊤/⊤ = 0
   in ENNReal (since ⊤ + anything ≥ ⊤ = ⊤). The correct characterization
   requires the total measure to be finite.

PROVIDED SOLUTION
EmpiricallyViable = P_normal > 0 = (μ_normal / (μ_normal + μ_BB)) > 0. In ENNReal, a/b > 0 iff a > 0 and b < ⊤ (since a/b = a * b⁻¹, and b⁻¹ > 0 iff b < ⊤, and a * c > 0 iff a > 0 and c > 0). Also need μ_normal + μ_BB ≠ 0 which follows from μ_normal > 0. Use ENNReal.div_pos_iff or unfold and use mul_pos.
-/
theorem core_thesis (B : BBAnalysis) :
    B.EmpiricallyViable ↔ B.μ_normal > 0 ∧ B.μ_normal + B.μ_BB < ⊤ := by
  -- By definition of P_normal, we have P_normal = μ_normal / (μ_normal + μ_BB).
  have hP_normal : B.P_normal = B.μ_normal / (B.μ_normal + B.μ_BB) := by
    rfl;
  norm_num [ BBAnalysis.EmpiricallyViable, hP_normal ];
  cases B.μ_normal <;> cases B.μ_BB <;> aesop

end