import NlsGge.Spectral.ActualPhysicalUnitHalfTraceGeneralRescaling35V3
import NlsGge.Spectral.ActualPhysicalDysonUnitAllFrequencyDiagonalTails35V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual normalized half trace differs from its free two-channel expression
by a bound independent of EVERY real frequency. The explicit geometric-smallness
premise is realized eventually at large height by the accepted coefficient limit.
This is not the bounded-height or complete upper-half-plane infinity theorem. -/
theorem actualPhysicalUnitNormalizedHalfTrace_uniformFrequency_bound35
    (u : PhysicalL2) (x Y : ℝ) (hY : 0 < Y)
    (hsmall : ‖u‖*Real.sqrt (‖u‖^2/(4*Y)) < 1) :
    ‖Complex.exp (Complex.I*((x : ℂ)+Complex.I*(Y : ℂ)))*
        actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ)) -
      (1+Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))))/2‖ ≤
      (‖u‖*Real.sqrt (‖u‖^2/(4*Y)))/(1-‖u‖*Real.sqrt (‖u‖^2/(4*Y))) := by
  let z : ℂ := (x : ℂ)+Complex.I*(Y : ℂ)
  let F := actualComplexZsDysonTsum
    (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z
  let a : ℂ := actualZsInteractionState32 z F 1 0 0
  let b : ℂ := actualZsInteractionState32 z F 1 1 1
  let c : ℂ := (Real.exp (-2*Y) : ℂ)
  let p : ℂ := complexRealOscillatoryPhase35 (2*x) 1
  let D : ℝ := (‖u‖*Real.sqrt (‖u‖^2/(4*Y)))/(1-‖u‖*Real.sqrt (‖u‖^2/(4*Y)))
  have ha : ‖a-1‖ ≤ D := actualPhysicalDysonUnit00_allFrequency_tail35 u x Y hY hsmall
  have hb : ‖c*b-c‖ ≤ D := actualPhysicalDysonUnitScaled11_allFrequency_tail35 u x Y hY hsmall
  have hp : ‖p‖=1 := complexRealOscillatoryPhase_norm35 (2*x) 1
  have hform : Complex.exp (Complex.I*z)*actualPhysicalUnitHalfTrace32 u z -
      (1+Complex.exp (2*Complex.I*z))/2 = (a-1+p*(c*b-c))/2 := by
    rw [actualPhysicalUnitHalfTrace_generalRescaling35,
      complexDoubledUpperHalfPlaneExponential_phase35]
    dsimp [a,b,p,c,F,z]
    ring
  change ‖Complex.exp (Complex.I*z)*actualPhysicalUnitHalfTrace32 u z -
      (1+Complex.exp (2*Complex.I*z))/2‖ ≤ D
  rw [hform, norm_div]
  have htwo : ‖(2 : ℂ)‖=(2 : ℝ) := by norm_num
  rw [htwo]
  have hsum : ‖a-1+p*(c*b-c)‖ ≤ D+D := by
    calc
      _ ≤ ‖a-1‖+‖p*(c*b-c)‖ := norm_add_le _ _
      _ = ‖a-1‖+‖c*b-c‖ := by rw [norm_mul,hp,one_mul]
      _ ≤ D+D := add_le_add ha hb
  linarith

end NlsGge.SpectralFoundations
end
