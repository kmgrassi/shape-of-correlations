import Mathlib
import RequestProject.Interference

/-!
# Seven-Node Toy Model

We build a concrete seven-node toy model with:
- 1 source node
- 2 slit nodes
- 4 screen nodes

We define two route amplitudes (through each slit) and prove that:
1. Screen intensities contain the interference cross term from two routes.
2. Removing one route removes the cross term.
3. All statements are purely relational — no background space is assumed.

## Main results

* `Node.cross_term_screen1_nonzero` — genuine interference at screen1
* `Node.interference_at_screen1` — intensity ≠ sum of individual intensities
* `Node.screen_interference` — the interference formula applied to the model
* `Node.single_route_no_cross` — blocking one slit removes the cross term
* `Node.model_is_relational` — the physics is invariant under relabeling
-/

noncomputable section

open Complex

/-! ## The seven nodes -/

/-- The seven nodes of our toy double-slit model. -/
inductive Node
  | source
  | slitA
  | slitB
  | screen1
  | screen2
  | screen3
  | screen4
  deriving DecidableEq, Fintype

namespace Node

/-- Route amplitude through slit A: assigns a complex amplitude to each screen node
    representing the contribution via slit A. -/
def routeA : WaveAmplitude Node := fun n =>
  match n with
  | screen1 => ⟨1/2, 1/4⟩
  | screen2 => ⟨1/3, 1/2⟩
  | screen3 => ⟨1/4, -1/3⟩
  | screen4 => ⟨1/5, 1/6⟩
  | _ => 0

/-- Route amplitude through slit B: assigns a complex amplitude to each screen node
    representing the contribution via slit B. -/
def routeB : WaveAmplitude Node := fun n =>
  match n with
  | screen1 => ⟨1/3, -1/5⟩
  | screen2 => ⟨1/4, 1/3⟩
  | screen3 => ⟨1/2, 1/4⟩
  | screen4 => ⟨1/6, -1/4⟩
  | _ => 0

/-- Total amplitude with both slits open. -/
def bothSlits : WaveAmplitude Node := routeA + routeB

/-! ## Cross term is present with both slits -/

/-- The cross term at screen1 with both slits is nonzero,
    witnessing genuine interference. -/
theorem cross_term_screen1_nonzero :
    crossTerm routeA routeB screen1 ≠ 0 := by
  unfold crossTerm; norm_num [Complex.ext_iff, routeA, routeB]

/-- With both slits open, the intensity at screen1 differs from
    the sum of individual route intensities. -/
theorem interference_at_screen1 :
    intensity bothSlits screen1 ≠
      intensity routeA screen1 + intensity routeB screen1 := by
  unfold intensity bothSlits routeA routeB
  norm_num [Complex.normSq, Complex.norm_def, div_pow]

/-- The interference formula applied to our specific model. -/
theorem screen_interference (n : Node) :
    intensity bothSlits n =
      intensity routeA n + intensity routeB n +
        crossTerm routeA routeB n :=
  interference_formula routeA routeB n

/-! ## Removing one route removes the cross term -/

/-- With only route A (slit B blocked), the intensity is just
    the single-route intensity — the cross term with the zero
    amplitude vanishes. -/
theorem single_route_no_cross :
    ∀ n, intensity routeA n =
      intensity routeA n + crossTerm routeA (0 : WaveAmplitude Node) n := by
  intro n; unfold crossTerm; simp

/-! ## The model is purely relational -/

/-- All interference physics is stated using only the finite type `Node` and
    functions on it. No ℝⁿ embedding, no manifold, no metric space structure
    on `Node` is assumed. The interference physics emerges from the algebraic
    structure of complex amplitudes on a bare finite set.

    We formalize this by showing the interference formula is invariant under
    arbitrary relabeling of the node set. -/
theorem model_is_relational :
    ∀ (T : Type) [DecidableEq T] [Fintype T] (f : Node ≃ T),
    ∀ n : Node,
      intensity (routeA ∘ f.symm + routeB ∘ f.symm) (f n) =
        intensity (routeA ∘ f.symm) (f n) +
          intensity (routeB ∘ f.symm) (f n) +
          crossTerm (routeA ∘ f.symm) (routeB ∘ f.symm) (f n) :=
  fun _T _ _ f n => interference_formula (routeA ∘ f.symm) (routeB ∘ f.symm) (f n)

end Node
end
