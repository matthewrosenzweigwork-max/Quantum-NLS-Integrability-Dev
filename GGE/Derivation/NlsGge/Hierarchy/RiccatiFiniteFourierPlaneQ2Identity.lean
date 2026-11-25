import NlsGge.Hierarchy.RiccatiQ2PeriodicIntegration
import NlsGge.Sobolev.PeriodicBridge
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

/-! The source Q₂ identity instantiated on the actual period-one finite
Fourier planes. This is a smooth finite-mode theorem, not a generic H¹
identity; the latter is obtained only after the separate density and
continuity arguments. -/

namespace NlsGge.HierarchyRiccati

open NlsGge.Pilot
open MeasureTheory

def finitePlaneSecondConjugateDerivative (N : ℕ) (z : FourierPlane N) : ℝ → ℂ :=
  fun x => star (planeReal N (derivativePlane N (derivativePlane N z)) x)

theorem finitePlane_q2_source_integral_eq_energy
    (N : ℕ) (z : FourierPlane N) :
    (∫ x in (0 : ℝ)..1,
      q2FormalDensityAt (planeReal N z)
        (finitePlaneSecondConjugateDerivative N z) x) =
      ∫ x in (0 : ℝ)..1,
        q2PhysicalEnergyDensity (planeReal N z)
          (planeReal N (derivativePlane N z)) x := by
  let u : ℝ → ℂ := planeReal N z
  let du : ℝ → ℂ := planeReal N (derivativePlane N z)
  let d2ubar : ℝ → ℂ := finitePlaneSecondConjugateDerivative N z
  have huPer : Function.Periodic u 1 := by
    intro x
    exact planeReal_periodic N z x
  have hstarDuPer : Function.Periodic (fun x => star (du x)) 1 := by
    intro x
    exact congrArg star (planeReal_periodic N (derivativePlane N z) x)
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (du x) x := by
    intro x hx
    exact hasDerivAt_planeReal N z x
  have hstarDu : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => star (du y)) (d2ubar x) x := by
    intro x hx
    exact (hasDerivAt_planeReal N (derivativePlane N z) x).star
  have hduCont : Continuous du := by
    dsimp [du]
    exact (contDiff_planeReal N (derivativePlane N z)).continuous
  have hd2Cont : Continuous d2ubar := by
    change Continuous (fun x => star
      (planeReal N (derivativePlane N (derivativePlane N z)) x))
    exact (contDiff_planeReal N (derivativePlane N (derivativePlane N z))).continuous.star
  have huCont : Continuous u := by
    dsimp [u]
    exact (contDiff_planeReal N z).continuous
  have hduInt : IntervalIntegrable du MeasureTheory.volume 0 1 :=
    hduCont.continuousOn.intervalIntegrable
  have hd2ubarInt : IntervalIntegrable d2ubar MeasureTheory.volume 0 1 :=
    hd2Cont.continuousOn.intervalIntegrable
  have hleftQuad : IntervalIntegrable (fun x => -(u x * d2ubar x))
      MeasureTheory.volume 0 1 := by
    exact (huCont.mul hd2Cont).neg.continuousOn.intervalIntegrable
  have hleftQuartic : IntervalIntegrable (fun x => (star (u x) * u x) ^ 2)
      MeasureTheory.volume 0 1 := by
    exact ((huCont.star.mul huCont).pow 2).continuousOn.intervalIntegrable
  have hrightQuad : IntervalIntegrable (fun x => du x * star (du x))
      MeasureTheory.volume 0 1 := by
    exact (hduCont.mul hduCont.star).continuousOn.intervalIntegrable
  have hrightQuartic : IntervalIntegrable (fun x => (star (u x) * u x) ^ 2)
      MeasureTheory.volume 0 1 := hleftQuartic
  have hid := unitPeriod_q2_integral_identity huPer hstarDuPer hu hstarDu
    hduInt hd2ubarInt hleftQuad hleftQuartic hrightQuad hrightQuartic
  simpa only [u, du, d2ubar, finitePlaneSecondConjugateDerivative,
    q2FormalDensityAt_eq_physical] using hid

end NlsGge.HierarchyRiccati
