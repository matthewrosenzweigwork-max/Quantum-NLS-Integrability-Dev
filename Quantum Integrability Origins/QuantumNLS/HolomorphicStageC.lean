import Mathlib
import QuantumNLS.HolomorphicStageB2c

/-!
# C2 stage C: complex-differentiable maps on complex Banach spaces are `C^n` for every finite `n`

With `E` and the codomains in one universe `Type u`, induct on `n` with the motive
`∀ F : Type u` complete, `∀ f`, `DifferentiableOn ℂ f U → ContDiffOn ℂ n f U`. The step uses
`contDiffOn_succ_iff_fderiv_of_isOpen` and the key lemma `differentiableOn_fderiv` (stage B2c) at the codomain
`E →L[ℂ] F`, which is again in `Type u` and complete. Consequently `ContDiffOn ℂ ∞ f U` (smooth).

Note: `ContDiffOn ℂ ⊤ f U` in the new `WithTop ℕ∞` convention means ANALYTIC (`ω`), which is stage D, not this file.
Standard axioms only.
-/

universe u

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set
open scoped ContDiff

namespace QuantumNLS.HolomorphicStageC

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem contDiffOn_nat_of_differentiableOn {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F),
      DifferentiableOn ℂ f U → ContDiffOn ℂ n f U := by
  induction n with
  | zero =>
    intro F _ _ _ f hf
    exact contDiffOn_zero.2 hf.continuousOn
  | succ n ih =>
    intro F _ _ _ f hf
    refine (contDiffOn_succ_iff_fderiv_of_isOpen (n := (n : WithTop ℕ∞)) hU).2
      ⟨hf, fun h => absurd h (by simp), ?_⟩
    exact ih (E →L[ℂ] F) (fderiv ℂ f)
      (QuantumNLS.HolomorphicStageB2c.differentiableOn_fderiv hU hf)

/-- Smoothness: `ContDiffOn ℂ ∞` (all finite orders). -/
theorem contDiffOn_infty_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.2 (fun n => contDiffOn_nat_of_differentiableOn hU n F f hf)

end QuantumNLS.HolomorphicStageC

#print axioms QuantumNLS.HolomorphicStageC.contDiffOn_infty_of_differentiableOn
