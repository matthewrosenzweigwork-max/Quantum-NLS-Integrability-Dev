import Mathlib
import QuantumNLS.HolomorphicStageD1

/-!
# DEF-017 C2, stage D2: iterated slice derivatives equal diagonal iterated Fréchet derivatives

For `f : E → F` complex-differentiable on an open `U` (E, F complex normed spaces in one universe, F complete),
and `x y : E`, the one-variable slice `g(s) = f (x + s • y)` satisfies, at every `t` with `x + t • y ∈ U`,
  `iteratedDeriv n g t = iteratedFDeriv ℂ n f (x + t • y) (fun _ => y)`.

Proof by induction on `n`. The step uses `iteratedDeriv_succ` (outer derivative), the induction hypothesis
on the open set `{s | x + s • y ∈ U}` (to get an eventual equality, hence equal derivatives), the chain rule
for the complex-differentiable map `iteratedFDeriv ℂ n f` along the line `s ↦ x + s • y`, and the
evaluation-at-a-fixed-vector CLM `ContinuousMultilinearMap.apply`. The last identity is
`iteratedFDeriv_succ_apply_left` (definitional). Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageD2

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem iteratedDeriv_slice {U : Set E} (hU : IsOpen U) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U) (x y : E) (n : ℕ) :
    ∀ t : ℂ, x + t • y ∈ U →
      iteratedDeriv n (fun s : ℂ => f (x + s • y)) t = iteratedFDeriv ℂ n f (x + t • y) (fun _ => y) := by
  have hcont : Continuous (fun s : ℂ => x + s • y) := by fun_prop
  have hO : IsOpen {s : ℂ | x + s • y ∈ U} := hU.preimage hcont
  induction n with
  | zero =>
    intro t _
    simp [iteratedDeriv_zero, iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro t ht
    have hev : (iteratedDeriv n (fun s : ℂ => f (x + s • y))) =ᶠ[𝓝 t]
        (fun s : ℂ => iteratedFDeriv ℂ n f (x + s • y) (fun _ => y)) := by
      filter_upwards [hO.mem_nhds ht] with s hs
      exact ih s hs
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hdA : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) (x + t • y) :=
      ((QuantumNLS.HolomorphicStageD1.differentiableOn_iteratedFDeriv_of_differentiableOn hU hf n)
        (x + t • y) ht).differentiableAt (hU.mem_nhds ht)
    have hline : HasDerivAt (fun s : ℂ => x + s • y) y t := by
      simpa using ((hasDerivAt_id t).smul_const y).const_add x
    have hcomp : HasDerivAt (iteratedFDeriv ℂ n f ∘ fun s : ℂ => x + s • y)
        (fderiv ℂ (iteratedFDeriv ℂ n f) (x + t • y) y) t :=
      hdA.hasFDerivAt.comp_hasDerivAt t hline
    have hev' : HasDerivAt (fun s : ℂ => iteratedFDeriv ℂ n f (x + s • y) (fun _ => y))
        (fderiv ℂ (iteratedFDeriv ℂ n f) (x + t • y) y (fun _ => y)) t :=
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => y)).hasFDerivAt.comp_hasDerivAt
        t hcomp
    rw [hev'.deriv]
    exact (iteratedFDeriv_succ_apply_left (fun _ : Fin (n + 1) => y)).symm

end QuantumNLS.HolomorphicStageD2

#print axioms QuantumNLS.HolomorphicStageD2.iteratedDeriv_slice
