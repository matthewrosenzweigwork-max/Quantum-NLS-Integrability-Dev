import Mathlib.Topology.UniformSpace.UniformApproximation
import NlsGge.Atomic.G4.G4004
import NlsGge.Atomic.LIB.LIB011
import NlsGge.GK38.Lib.HilbertValuedAnalytic

/-!
# Analyticity of locally uniform limits

This lifts the scalar one-variable locally uniform limit theorem to complex Banach spaces using
the project's weak analyticity criterion. Local uniform convergence is taken in the target's norm
uniformity.
-/

set_option autoImplicit false

open Filter Set

namespace NlsGge.Atomic.G4

/-- A locally uniform limit, in target norm, of analytic maps on an open subset of a complex
normed space into a complete complex normed space is analytic. -/
theorem analyticOnNhd_of_locally_uniform_limit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set E} {f : ℕ → E → F} {g : E → F}
    (hU : IsOpen U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hlim : TendstoLocallyUniformlyOn f g atTop U) :
    AnalyticOnNhd ℂ g U := by
  have hcont : ContinuousOn g U :=
    hlim.continuousOn (Filter.Frequently.of_forall fun n => (hf n).continuousOn)
  have hbd : NlsGge.GK38.Lib.LocBdd U g :=
    NlsGge.GK38.Lib.locBdd_of_continuousOn hU hcont
  apply NlsGge.Atomic.G4.analyticOnNhd_of_weakAnalytic_locallyBounded hU ?_ hbd
  intro x hx h ℓ
  let line : ℂ → E := fun ζ => x + ζ • h
  let D : Set ℂ := line ⁻¹' U
  have hline_cont : Continuous line := by fun_prop
  have hD_open : IsOpen D := hU.preimage hline_cont
  have hzero : (0 : ℂ) ∈ D := by
    change x + (0 : ℂ) • h ∈ U
    simpa using hx
  have hline_analytic (ζ : ℂ) : AnalyticAt ℂ line ζ := by
    dsimp [line]
    fun_prop
  have hline_limit :
      TendstoLocallyUniformlyOn
        (fun n ζ => f n (line ζ)) (fun ζ => g (line ζ)) atTop D := by
    change TendstoLocallyUniformlyOn (fun n => f n ∘ line) (g ∘ line) atTop D
    exact hlim.comp (t := D) line (by intro ζ hζ; exact hζ)
      hline_cont.continuousOn
  have hscalar_limit :
      TendstoLocallyUniformlyOn
        (fun n ζ => ℓ (f n (line ζ))) (fun ζ => ℓ (g (line ζ))) atTop D := by
    change TendstoLocallyUniformlyOn
      (fun n => (fun y : F => ℓ y) ∘ (f n ∘ line))
      ((fun y : F => ℓ y) ∘ (g ∘ line)) atTop D
    exact ℓ.uniformContinuous.comp_tendstoLocallyUniformlyOn hline_limit
  have hscalar_analytic :
      ∀ n, AnalyticOnNhd ℂ (fun ζ : ℂ => ℓ (f n (line ζ))) D := by
    intro n ζ hζ
    have hpoint : AnalyticAt ℂ (f n) (line ζ) := hf n (line ζ) hζ
    have hscalarpoint : AnalyticAt ℂ (fun y : E => ℓ (f n y)) (line ζ) :=
      AnalyticAt.comp (g := fun y : F => ℓ y) (f := f n)
        (ℓ.analyticAt (f n (line ζ))) hpoint
    exact AnalyticAt.comp (g := fun y : E => ℓ (f n y)) (f := line)
      hscalarpoint (hline_analytic ζ)
  exact (NlsGge.Atomic.LIB.analyticOnNhd_of_locallyUniformLimit hD_open
      hscalar_analytic hscalar_limit) 0 hzero

end NlsGge.Atomic.G4
