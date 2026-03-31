import Mathlib

noncomputable section

open Finset BigOperators Real

/-! # Common-Origin Relational Kernel Framework

We formalize a framework in which a single relational object (a Gram matrix / correlation
kernel) determines both emergent geometry and Bell correlations. The key result is that
Bell-violating correlations can arise from the same relational structure that generates
emergent geometry, without introducing an independent Bell parameter.

## Main definitions

* `CommonOriginSystem S` - A symmetric, PSD, normalized kernel on a finite type S
* `BellScenario S` - A common-origin system with four distinguished measurement settings
* `BellScenario.CHSH` - The CHSH expression
* `CommonOriginSystem.geomKernel` - The geometry kernel |G(i,j)|
* `CommonOriginSystem.Submultiplicative` - Condition for metric emergence

## Main results

* `correlator_bound` - |G(i,j)| ≤ 1 for any common-origin system
* `chsh_violation` - There exists a common-origin system with CHSH = 2√2 > 2
* `no_signaling_alice` / `no_signaling_bob` - No-signaling holds
* `bell_not_implies_metric` - Bell violation ⇏ metric emergence
* `metric_not_implies_bell` - Metric emergence ⇏ Bell violation
* `both_geometry_and_bell_exist` - Both can coexist from one object
* `nonsep_gt_half_iff_nonlocal` - Nonseparability invariant characterizes Bell violation
-/

-- ============================================================================
-- Part I: Core Definitions
-- ============================================================================

/-- A `CommonOriginSystem` on a finite type `S` is a real symmetric, positive semidefinite,
    normalized kernel `G : S → S → ℝ`. -/
structure CommonOriginSystem (S : Type*) [Fintype S] where
  G : S → S → ℝ
  symm : ∀ i j, G i j = G j i
  normalized : ∀ i, G i i = 1
  psd : ∀ c : S → ℝ, 0 ≤ ∑ i : S, ∑ j : S, c i * c j * G i j

/-- A `BellScenario` extends a `CommonOriginSystem` with four distinguished elements. -/
structure BellScenario (S : Type*) [Fintype S] extends CommonOriginSystem S where
  A₀ : S
  A₁ : S
  B₀ : S
  B₁ : S

variable {S : Type*} [Fintype S]

/-- The geometry kernel I_R(i,j) = |G(i,j)| -/
def CommonOriginSystem.geomKernel (R : CommonOriginSystem S) (i j : S) : ℝ := |R.G i j|

/-- The induced relational distance d_R(i,j) = -log|G(i,j)| -/
def CommonOriginSystem.relDist (R : CommonOriginSystem S) (i j : S) : ℝ :=
  -Real.log (|R.G i j|)

/-- Submultiplicativity: |G(i,k)| ≥ |G(i,j)| · |G(j,k)| for all i,j,k. -/
def CommonOriginSystem.Submultiplicative (R : CommonOriginSystem S) : Prop :=
  ∀ i j k : S, |R.G i k| ≥ |R.G i j| * |R.G j k|

/-- Restricted submultiplicativity on a subset T. -/
def CommonOriginSystem.SubmultiplicativeOn (R : CommonOriginSystem S) (T : Finset S) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, |R.G i k| ≥ |R.G i j| * |R.G j k|

/-- The Bell correlator E(a,b) = G(A_a, B_b) -/
def BellScenario.E (B : BellScenario S) (a b : Fin 2) : ℝ :=
  B.G (if a = 0 then B.A₀ else B.A₁) (if b = 0 then B.B₀ else B.B₁)

/-- The CHSH expression S = E(0,0) + E(0,1) + E(1,0) - E(1,1) -/
def BellScenario.CHSH (B : BellScenario S) : ℝ :=
  B.E 0 0 + B.E 0 1 + B.E 1 0 - B.E 1 1

/-- The nonseparability invariant η(B) = |CHSH(B)| / 4 -/
def BellScenario.nonsepInvariant (B : BellScenario S) : ℝ := |B.CHSH| / 4

/-- Joint probability P(x,y|a,b) = (1 + xy·E(a,b)) / 4 for x,y ∈ {±1} -/
def BellScenario.jointProb (B : BellScenario S) (x y : ℤ) (a b : Fin 2) : ℝ :=
  (1 + ↑x * ↑y * B.E a b) / 4

-- ============================================================================
-- Part II: Gram Matrix from Vectors
-- ============================================================================

/-- The Gram matrix of a family of vectors in ℝⁿ. -/
def gramMatrix {n : ℕ} (v : S → Fin n → ℝ) (i j : S) : ℝ :=
  ∑ k : Fin n, v i k * v j k

theorem gramMatrix_symm {n : ℕ} (v : S → Fin n → ℝ) (i j : S) :
    gramMatrix v i j = gramMatrix v j i := by
  simp only [gramMatrix, mul_comm (v i _) (v j _)]

/-
PROBLEM
The Gram matrix is PSD: ∑ᵢⱼ cᵢcⱼGᵢⱼ = ∑ₖ (∑ᵢ cᵢvᵢₖ)² ≥ 0.

PROVIDED SOLUTION
Rearrange the double sum: ∑ i, ∑ j, c i * c j * (∑ k, v i k * v j k) = ∑ k, (∑ i, c i * v i k)^2 ≥ 0. Use Finset.sum_comm to swap order of summation, then recognize the squared sum pattern.
-/
theorem gramMatrix_psd {n : ℕ} (v : S → Fin n → ℝ) (c : S → ℝ) :
    0 ≤ ∑ i : S, ∑ j : S, c i * c j * gramMatrix v i j := by
      -- By commutativity of the dot product, we can rewrite the sum as:
      have h_comm : ∑ i, ∑ j, c i * c j * (∑ k, v i k * v j k) = ∑ k, ∑ i, ∑ j, c i * c j * (v i k * v j k) := by
        simp +decide only [Finset.mul_sum _ _ _];
        exact?;
      -- Recognize that the inner sum is a square:
      have h_square : ∀ k, ∑ i, ∑ j, c i * c j * (v i k * v j k) = (∑ i, c i * v i k) ^ 2 := by
        simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact h_comm.symm ▸ Finset.sum_nonneg fun k _ => h_square k ▸ sq_nonneg _

/-- Construct a `CommonOriginSystem` from unit vectors. -/
def CommonOriginSystem.fromVectors {n : ℕ} (v : S → Fin n → ℝ)
    (hunit : ∀ s, ∑ k : Fin n, v s k * v s k = 1) : CommonOriginSystem S where
  G := gramMatrix v
  symm := gramMatrix_symm v
  normalized := hunit
  psd := gramMatrix_psd v

/-
PROBLEM
============================================================================
Part III: Theorem 1 — Correlator Bound
============================================================================

Cauchy-Schwarz for PSD kernels: G(i,j)² ≤ G(i,i) · G(j,j).

PROVIDED SOLUTION
Use the PSD condition with c being a function supported only at i and j. Specifically, for any t : ℝ, define c(x) = if x = i then t else if x = j then 1 else 0 (handle the case i = j separately). The PSD condition gives t²G(i,i) + 2t·G(i,j) + G(j,j) ≥ 0 for all t. This means the discriminant of this quadratic is ≤ 0: 4·G(i,j)² - 4·G(i,i)·G(j,j) ≤ 0. If i = j, G(i,j)² = G(i,i)² = G(i,i)·G(j,j) trivially.
-/
theorem CommonOriginSystem.cauchy_schwarz (R : CommonOriginSystem S) (i j : S) :
    R.G i j ^ 2 ≤ R.G i i * R.G j j := by
      -- By the properties of the Gram matrix, we know that for any vectors $u$ and $v$, $(u \cdot v)^2 \leq (u \cdot u)(v \cdot v)$.
      have h_cauchy_schwarz : ∀ (u v : S → ℝ), (∑ i, u i * v i)^2 ≤ (∑ i, u i^2) * (∑ i, v i^2) := by
        exact?;
      -- Since $G$ is positive semidefinite, there exists a matrix $M$ such that $G = M^T M$.
      obtain ⟨M, hM⟩ : ∃ M : S → S → ℝ, ∀ i j, R.G i j = ∑ k, M i k * M j k := by
        have h_pos_semidef : Matrix.PosSemidef (Matrix.of (fun i j => R.G i j)) := by
          constructor;
          · exact Matrix.ext fun i j => by simp +decide [ R.symm ] ;
          · intro x
            have := R.psd (fun i => x i)
            simp_all +decide [ Finsupp.sum_fintype ];
            simpa only [ mul_right_comm ] using this;
        have := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h_pos_semidef;
        obtain ⟨ B, hB ⟩ := this; use fun i j => B j i; intro i j; replace hB := congr_fun ( congr_fun hB i ) j; simp_all +decide [ Matrix.mul_apply, mul_comm ] ;
      simp_all +decide [ sq ]

/-
PROBLEM
**Theorem 1**: |G(i,j)| ≤ 1 for any common-origin system.

PROVIDED SOLUTION
From cauchy_schwarz: G(i,j)^2 ≤ G(i,i)*G(j,j) = 1*1 = 1 (using normalized). So |G(i,j)|^2 ≤ 1, hence |G(i,j)| ≤ 1 (since |G(i,j)| ≥ 0). Use abs_le_one_of_sq_le_one or sq_le_one_iff_abs_le_one.
-/
theorem correlator_bound (R : CommonOriginSystem S) (i j : S) :
    |R.G i j| ≤ 1 := by
      have := R.cauchy_schwarz i j;
      rw [ ← Real.sqrt_sq_eq_abs, Real.sqrt_le_left ] <;> norm_num [ R.normalized ] at * ; nlinarith

/-
PROBLEM
Correlator bound for Bell correlators.

PROVIDED SOLUTION
Unfold E and apply correlator_bound to B.toCommonOriginSystem.
-/
theorem BellScenario.E_bound (B : BellScenario S) (a b : Fin 2) :
    |B.E a b| ≤ 1 := by
      convert correlator_bound B.toCommonOriginSystem _ _ using 2

-- ============================================================================
-- Part IV: Theorem 2 — Bell Violation (CHSH = 2√2)
-- ============================================================================

/-- The CHSH-optimal unit vectors in ℝ²:
    A₀=(1,0), A₁=(0,1), B₀=(1/√2,1/√2), B₁=(1/√2,-1/√2). -/
def chshVec : Fin 4 → Fin 2 → ℝ := fun i =>
  match i with
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![1 / Real.sqrt 2, 1 / Real.sqrt 2]
  | 3 => ![1 / Real.sqrt 2, -(1 / Real.sqrt 2)]

/-
PROVIDED SOLUTION
Case split on all 4 values of Fin 4 using fin_cases. For cases 0 and 1, it's 1*1+0*0=1 and 0*0+1*1=1. For cases 2 and 3, it's (1/√2)*(1/√2) + (1/√2)*(1/√2) = 1/2+1/2=1, using Real.mul_self_sqrt or Real.sq_sqrt for the fact that (1/√2)^2 = 1/2.
-/
theorem chshVec_unit : ∀ s : Fin 4, ∑ k : Fin 2, chshVec s k * chshVec s k = 1 := by
  intro s
  fin_cases s <;> norm_num [ chshVec ] at *;
  · norm_num [ ← sq ];
  · norm_num [ ← sq ]

/-- The CHSH-optimal Bell scenario from Gram vectors. -/
def chshScenario : BellScenario (Fin 4) :=
  { CommonOriginSystem.fromVectors chshVec chshVec_unit with
    A₀ := 0
    A₁ := 1
    B₀ := 2
    B₁ := 3 }

/-
PROVIDED SOLUTION
Unfold chshScenario.E, chshScenario, CommonOriginSystem.fromVectors, gramMatrix. The sum over Fin 2 is chshVec 0 0 * chshVec 2 0 + chshVec 0 1 * chshVec 2 1 = 1*(1/√2) + 0*(1/√2) = 1/√2. Use simp with BellScenario.E, gramMatrix, chshVec, Fin.sum_univ_two, and norm_num.
-/
theorem chsh_E00 : chshScenario.E 0 0 = 1 / Real.sqrt 2 := by
  norm_num [ BellScenario.E, chshScenario ] at *;
  convert congr_arg _ ( chshVec_unit 2 ) using 1 ; norm_num [ Fin.sum_univ_two, gramMatrix ];
  rotate_right;
  exacts [ fun x => ( √2 ) ⁻¹, by unfold CommonOriginSystem.fromVectors; norm_num [ chshVec, gramMatrix ], by norm_num ]

/-
PROVIDED SOLUTION
Similar to chsh_E00. E 0 1 = gramMatrix chshVec 0 3 = chshVec 0 0 * chshVec 3 0 + chshVec 0 1 * chshVec 3 1 = 1*(1/√2) + 0*(-(1/√2)) = 1/√2.
-/
theorem chsh_E01 : chshScenario.E 0 1 = 1 / Real.sqrt 2 := by
  unfold chshScenario; norm_num [ gramMatrix, chshVec ] ;
  unfold BellScenario.E; norm_num [ gramMatrix, chshVec ] ;
  unfold CommonOriginSystem.fromVectors; norm_num [ gramMatrix, chshVec ] ;

/-
PROVIDED SOLUTION
E 1 0 = gramMatrix chshVec 1 2 = chshVec 1 0 * chshVec 2 0 + chshVec 1 1 * chshVec 2 1 = 0*(1/√2) + 1*(1/√2) = 1/√2.
-/
theorem chsh_E10 : chshScenario.E 1 0 = 1 / Real.sqrt 2 := by
  simp [chshScenario, BellScenario.E, CommonOriginSystem.fromVectors, gramMatrix];
  unfold chshVec; norm_num;

/-
PROVIDED SOLUTION
E 1 1 = gramMatrix chshVec 1 3 = chshVec 1 0 * chshVec 3 0 + chshVec 1 1 * chshVec 3 1 = 0*(1/√2) + 1*(-(1/√2)) = -1/√2.
-/
theorem chsh_E11 : chshScenario.E 1 1 = -(1 / Real.sqrt 2) := by
  unfold chshScenario;
  unfold BellScenario.E; norm_num [ Fin.sum_univ_succ, chshVec ] ;
  unfold CommonOriginSystem.fromVectors; norm_num [ Fin.sum_univ_succ, chshVec ] ; ring;
  norm_num [ gramMatrix, chshVec ]

/-
PROBLEM
**Theorem 2**: CHSH = 2√2 for the optimal Gram construction.

PROVIDED SOLUTION
Unfold CHSH. Use chsh_E00, chsh_E01, chsh_E10, chsh_E11 to rewrite. Get 1/√2 + 1/√2 + 1/√2 - (-(1/√2)) = 4/√2 = 2*√2. For 4/√2 = 2*√2, use the fact that √2 * √2 = 2 (Real.mul_self_sqrt).
-/
theorem chsh_value : chshScenario.CHSH = 2 * Real.sqrt 2 := by
  convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) ( chsh_E00 ) ( chsh_E01 ) ) ( chsh_E10 ) ) ( congr_arg Neg.neg ( chsh_E11 ) ) using 1 ; ring_nf;
  grind

/-
PROBLEM
**Theorem 2 (corollary)**: CHSH > 2 (Bell violation).

PROVIDED SOLUTION
Rewrite with chsh_value to get 2*√2 > 2. This follows from √2 > 1, which follows from 2 > 1 and sqrt being monotone, or just from Real.one_lt_sq_iff_one_lt and 2 > 1.
-/
theorem chsh_violation : chshScenario.CHSH > 2 := by
  refine' lt_of_le_of_lt _ ( chsh_value.symm ▸ mul_lt_mul_of_pos_left ( show Real.sqrt 2 > 1 from Real.lt_sqrt_of_sq_lt ( by norm_num ) ) zero_lt_two );
  norm_num +zetaDelta at *

/-
PROBLEM
============================================================================
Part V: Theorem 3 — No-Signaling
============================================================================

Joint probabilities are nonneg for |E| ≤ 1 and x,y ∈ {±1}.

PROVIDED SOLUTION
When x,y ∈ {±1}, xy ∈ {±1}, so xy*E ∈ [-1,1] since |E| ≤ 1 (by E_bound). Thus 1 + xy*E ≥ 0, and dividing by 4 gives nonneg. Case split on hx and hy to get x*y = 1 or x*y = -1.
-/
theorem BellScenario.jointProb_nonneg (B : BellScenario S) (a b : Fin 2)
    (x y : ℤ) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    0 ≤ B.jointProb x y a b := by
      exact div_nonneg ( by cases hx <;> cases hy <;> simp +decide [ * ] <;> linarith [ abs_le.mp ( B.E_bound a b ) ] ) zero_le_four

/-
PROBLEM
Joint probabilities sum to 1.

PROVIDED SOLUTION
Unfold jointProb. Sum = (1+E)/4 + (1-E)/4 + (1-E)/4 + (1+E)/4 = 4/4 = 1. Use ring or field_simp after unfolding.
-/
theorem BellScenario.jointProb_sum (B : BellScenario S) (a b : Fin 2) :
    B.jointProb 1 1 a b + B.jointProb 1 (-1) a b +
    B.jointProb (-1) 1 a b + B.jointProb (-1) (-1) a b = 1 := by
      unfold BellScenario.jointProb; ring;

/-
PROBLEM
**Theorem 3a**: Alice's marginal is 1/2 (no-signaling).

PROVIDED SOLUTION
Unfold jointProb. The sum is (1 + x*1*E)/4 + (1 + x*(-1)*E)/4 = (1 + xE + 1 - xE)/4 = 2/4 = 1/2. Just ring/field_simp after unfolding.
-/
theorem no_signaling_alice (B : BellScenario S) (a b : Fin 2) (x : ℤ) :
    B.jointProb x 1 a b + B.jointProb x (-1) a b = 1 / 2 := by
      unfold BellScenario.jointProb; ring;

/-
PROBLEM
**Theorem 3b**: Bob's marginal is 1/2 (no-signaling).

PROVIDED SOLUTION
Unfold jointProb. The sum is (1 + 1*y*E)/4 + (1 + (-1)*y*E)/4 = (1 + yE + 1 - yE)/4 = 2/4 = 1/2. Just ring/field_simp after unfolding.
-/
theorem no_signaling_bob (B : BellScenario S) (a b : Fin 2) (y : ℤ) :
    B.jointProb 1 y a b + B.jointProb (-1) y a b = 1 / 2 := by
      unfold BellScenario.jointProb; ring;

-- ============================================================================
-- Part VI: Theorem 4 — Common Origin (Definitional)
-- ============================================================================

/-- Geometry kernel is |G(i,j)|, directly from G. -/
theorem common_origin_geometry (B : BellScenario S) (i j : S) :
    B.geomKernel i j = |B.G i j| := rfl

/-- Bell correlators are G(A_a, B_b), directly from G. -/
theorem common_origin_bell (B : BellScenario S) (a b : Fin 2) :
    B.E a b = B.G (if a = 0 then B.A₀ else B.A₁) (if b = 0 then B.B₀ else B.B₁) := rfl

/-
PROBLEM
============================================================================
Part VII: Theorem 5 — Bell Violation ⇏ Metric Emergence
============================================================================

Submultiplicativity fails for the CHSH-optimal construction.

PROVIDED SOLUTION
Show submultiplicativity fails at (i,j,k) = (0,2,1) (or (0,2,1) meaning A₀, B₀, A₁). We need |G(0,1)| ≥ |G(0,2)| * |G(2,1)|. G(0,1) = gramMatrix chshVec 0 1 = 1*0 + 0*1 = 0. G(0,2) = 1/√2. G(2,1) = 1/√2. So 0 ≥ (1/√2)*(1/√2) = 1/2, which is false. Unfold Submultiplicative, introduce the negation, and provide the witness (0,2,1). Use norm_num after unfolding gramMatrix and chshVec.
-/
theorem chsh_submult_fails :
    ¬chshScenario.toCommonOriginSystem.Submultiplicative := by
      unfold CommonOriginSystem.Submultiplicative;
      simp +zetaDelta at *;
      use 0, 2, 1;
      unfold chshScenario; norm_num [ abs_of_pos ] ;
      unfold CommonOriginSystem.fromVectors; norm_num [ Fin.sum_univ_succ, gramMatrix ] ;
      unfold chshVec; norm_num [ abs_of_pos ] ;

/-- **Theorem 5**: Bell violation does not imply metric emergence. -/
theorem bell_not_implies_metric :
    ∃ B : BellScenario (Fin 4), B.CHSH > 2 ∧
    ¬B.toCommonOriginSystem.Submultiplicative :=
  ⟨chshScenario, chsh_violation, chsh_submult_fails⟩

-- ============================================================================
-- Part VIII: Theorem 6 — Metric Emergence ⇏ Bell Violation
-- ============================================================================

/-- The trivial construction: all vectors = (1, 0). -/
def trivialVec : Fin 4 → Fin 2 → ℝ := fun _ => ![1, 0]

/-
PROVIDED SOLUTION
Expand the sum over Fin 2 using Fin.sum_univ_two. trivialVec s = ![1, 0] for all s, so the sum is 1*1 + 0*0 = 1. Use simp with trivialVec and Matrix.cons_val lemmas.
-/
theorem trivialVec_unit :
    ∀ s : Fin 4, ∑ k : Fin 2, trivialVec s k * trivialVec s k = 1 := by
      unfold trivialVec; norm_num;

/-- The trivial Bell scenario (all vectors identical). -/
def trivialScenario : BellScenario (Fin 4) :=
  { CommonOriginSystem.fromVectors trivialVec trivialVec_unit with
    A₀ := 0
    A₁ := 1
    B₀ := 2
    B₁ := 3 }

/-
PROVIDED SOLUTION
For trivialScenario, G(i,j) = gramMatrix trivialVec i j = 1*1 + 0*0 = 1 for all i,j (since trivialVec _ = ![1,0]). So |G(i,j)| = 1 for all i,j. Submultiplicativity: 1 ≥ 1*1 is trivially true. Unfold everything and use norm_num.
-/
theorem trivial_submult : trivialScenario.toCommonOriginSystem.Submultiplicative := by
  -- Since all entries of the Gram matrix are 1, the submultiplicative condition holds trivially.
  intros i j k
  simp [trivialScenario, gramMatrix];
  unfold CommonOriginSystem.fromVectors; norm_num [ trivialVec ] ;
  unfold gramMatrix trivialVec; norm_num [ Fin.sum_univ_succ ] ;

/-
PROVIDED SOLUTION
For trivialScenario, all G(i,j) = 1, so E(a,b) = 1 for all a,b. CHSH = 1+1+1-1 = 2 ≤ 2. Unfold CHSH, E, chshScenario, gramMatrix, trivialVec and use norm_num.
-/
theorem trivial_chsh_le : trivialScenario.CHSH ≤ 2 := by
  unfold BellScenario.CHSH;
  unfold trivialScenario; norm_num;
  unfold BellScenario.E; norm_num [ CommonOriginSystem.fromVectors, gramMatrix, trivialVec ] ;

/-- **Theorem 6**: Metric emergence does not imply Bell violation. -/
theorem metric_not_implies_bell :
    ∃ B : BellScenario (Fin 4), B.toCommonOriginSystem.Submultiplicative ∧ B.CHSH ≤ 2 :=
  ⟨trivialScenario, trivial_submult, trivial_chsh_le⟩

/-
PROBLEM
============================================================================
Part IX: Theorem 7 — Both Geometry and Bell Coexist
============================================================================

Submultiplicativity holds on {0, 3} in the CHSH-optimal construction.

PROVIDED SOLUTION
Check submultiplicativity for all i,j,k ∈ {0,3}. There are 8 triples. For each, |G(i,k)| ≥ |G(i,j)|*|G(j,k)| holds because:
- G(0,0)=1, G(3,3)=1, G(0,3)=G(3,0)=1/√2
- All triples: either sides are equal (like 1≥1*1 or 1/√2 ≥ 1/√2*1) or LHS ≥ product because one factor is ≤1.
Use simp/norm_num with fin_cases after intro and membership checks.
-/
theorem chsh_submult_on_pair :
    chshScenario.toCommonOriginSystem.SubmultiplicativeOn {(0 : Fin 4), 3} := by
      intro i hi j hj k hk;
      simp +zetaDelta at *;
      rcases hi with ( rfl | rfl ) <;> rcases hj with ( rfl | rfl ) <;> rcases hk with ( rfl | rfl ) <;> norm_num [ chshScenario, gramMatrix ];
      all_goals unfold CommonOriginSystem.fromVectors; norm_num [ chshVec ] ;
      all_goals unfold gramMatrix; norm_num [ chshVec ] ;
      · norm_num [ ← sq, abs_of_pos ];
      · ring_nf; norm_num [ abs_le ] ;
      · ring_nf; norm_num [ abs_of_pos ];
      · ring_nf; norm_num [ abs_le ] ;
      · norm_num [ ← sq ]

/-
PROBLEM
**Theorem 7**: Both metric emergence (on a subset) and Bell violation
    can coexist in one common-origin system.

PROVIDED SOLUTION
Use chshScenario with T = {0, 3}. Card ≥ 2 by norm_num. SubmultiplicativeOn by chsh_submult_on_pair. CHSH > 2 by chsh_violation.
-/
theorem both_geometry_and_bell_exist :
    ∃ (B : BellScenario (Fin 4)) (T : Finset (Fin 4)),
      T.card ≥ 2 ∧
      B.toCommonOriginSystem.SubmultiplicativeOn T ∧
      B.CHSH > 2 := by
        -- Let's choose the BellScenario from the CHSH-optimal construction.
        use chshScenario, {0, 3};
        exact ⟨ by decide, chsh_submult_on_pair, chsh_violation ⟩

-- ============================================================================
-- Part X: Theorem 8 — Sector Decomposition
-- ============================================================================

/-- **Theorem 8**: Sector decomposition — one G yields both geometric and Bell sectors. -/
theorem sector_decomposition :
    ∃ B : BellScenario (Fin 4),
      B.toCommonOriginSystem.SubmultiplicativeOn {(0 : Fin 4), 3} ∧
      B.CHSH > 2 ∧
      (∀ i j : Fin 4, B.geomKernel i j = |B.G i j|) :=
  ⟨chshScenario, chsh_submult_on_pair, chsh_violation, common_origin_geometry _⟩

/-
PROBLEM
============================================================================
Part XI: Theorem 9 — Nonseparability Invariant
============================================================================

**Theorem 9a**: η ≤ 1/2 ↔ no Bell violation.

PROVIDED SOLUTION
η = |CHSH|/4. η ≤ 1/2 ↔ |CHSH|/4 ≤ 1/2 ↔ |CHSH| ≤ 2. Use div_le_div_iff or mul/div algebra.
-/
theorem nonsep_le_half_iff_local (B : BellScenario S) :
    B.nonsepInvariant ≤ 1 / 2 ↔ |B.CHSH| ≤ 2 := by
      grind +locals

/-
PROBLEM
**Theorem 9b**: η > 1/2 ↔ Bell violation.

PROVIDED SOLUTION
η = |CHSH|/4. η > 1/2 ↔ |CHSH|/4 > 1/2 ↔ |CHSH| > 2. Use div_lt_div_iff or similar.
-/
theorem nonsep_gt_half_iff_nonlocal (B : BellScenario S) :
    B.nonsepInvariant > 1 / 2 ↔ |B.CHSH| > 2 := by
      unfold BellScenario.nonsepInvariant; norm_num; constructor <;> intro <;> linarith;

/-
PROBLEM
The CHSH-optimal construction has η = √2/2 > 1/2.

PROVIDED SOLUTION
η = |CHSH|/4 = |2√2|/4 = 2√2/4 = √2/2. Use chsh_value, abs_of_pos, and arithmetic.
-/
theorem chsh_nonsep_invariant :
    chshScenario.nonsepInvariant = Real.sqrt 2 / 2 := by
      unfold BellScenario.nonsepInvariant; norm_num [ chshScenario, chsh_value ] ; ring;
      rw [ abs_of_nonneg ] <;> linarith! [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, chsh_value ] ;

-- ============================================================================
-- Part XII: Assumptions A–E
-- ============================================================================

/-- **Assumption A** (TRUE): A common-origin matrix can generate Bell violation. -/
theorem assumption_A : ∃ B : BellScenario (Fin 4), B.CHSH > 2 :=
  ⟨chshScenario, chsh_violation⟩

/-
PROBLEM
**Assumption B** (FALSE): Bell violation does NOT imply geometry automatically.

PROVIDED SOLUTION
Negate and push in. We need to find a BellScenario with CHSH > 2 and not Submultiplicative. Use chshScenario, chsh_violation, chsh_submult_fails.
-/
theorem assumption_B_false :
    ¬(∀ B : BellScenario (Fin 4), B.CHSH > 2 →
      B.toCommonOriginSystem.Submultiplicative) := by
        exact fun h => chsh_submult_fails <| h _ chsh_violation

/-
PROBLEM
**Assumption C** (FALSE): Geometry does NOT imply Bell violation automatically.

PROVIDED SOLUTION
We need a BellScenario with Submultiplicative but not CHSH > 2. Use trivialScenario, trivial_submult, and trivial_chsh_le (which gives CHSH ≤ 2, contradicting CHSH > 2).
-/
theorem assumption_C_false :
    ¬(∀ B : BellScenario (Fin 4), B.toCommonOriginSystem.Submultiplicative →
      B.CHSH > 2) := by
        push_neg;
        convert metric_not_implies_bell using 1

/-- **Assumption D** (TRUE): Both can coexist. -/
theorem assumption_D : ∃ (B : BellScenario (Fin 4)) (T : Finset (Fin 4)),
    T.card ≥ 2 ∧ B.toCommonOriginSystem.SubmultiplicativeOn T ∧ B.CHSH > 2 :=
  both_geometry_and_bell_exist

/-- **Assumption E** (TRUE): Bell violation is intrinsic to η. -/
theorem assumption_E (B : BellScenario S) :
    B.nonsepInvariant > 1 / 2 ↔ |B.CHSH| > 2 :=
  nonsep_gt_half_iff_nonlocal B

end