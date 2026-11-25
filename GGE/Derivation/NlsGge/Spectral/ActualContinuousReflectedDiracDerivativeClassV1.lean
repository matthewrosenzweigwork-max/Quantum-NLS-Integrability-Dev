import NlsGge.Schur.SourceIntervalLInfFromActualContinuousOnV2
import NlsGge.Spectral.ActualNegativePhysicalL2SourcePotentialV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- Actual L2 derivative classes for the reflected system: a rough physical
potential multiplies a realized L-infinity state, not an assumed H1 state. -/
def actualContinuousReflectedDiracDerivativeClass
    (u : PhysicalL2) (z : ℂ) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (b : Bool) : SourceIntervalL2 :=
  if b then
    Complex.I • (z • sourceIntervalL2OfContinuousOn f hf -
      actualSourceL2PotentialTimesLInf u (sourceIntervalLInfOfContinuousOn g hg))
  else
    Complex.I • (actualSourceL2PotentialTimesLInf (star u)
      (sourceIntervalLInfOfContinuousOn f hf) - z • sourceIntervalL2OfContinuousOn g hg)

def actualContinuousReflectedDiracDerivativeRepresentative
    (u : PhysicalL2) (z : ℂ) (f g : ℝ → ℂ) (b : Bool) (t : ℝ) : ℂ :=
  if b then
    Complex.I * (z * f t - actualPhysicalL2SourcePotential u t * g t)
  else
    Complex.I * (actualPhysicalL2SourcePotential (star u) t * f t - z * g t)

/-- The constructed derivative classes have the genuine L2 products as
representatives on the source interval, with the physical conjugate field. -/
theorem actualContinuousReflectedDiracDerivativeClass_ae
    (u : PhysicalL2) (z : ℂ) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (b : Bool) :
    (actualContinuousReflectedDiracDerivativeClass u z f g hf hg b : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      actualContinuousReflectedDiracDerivativeRepresentative u z f g b := by
  let F := sourceIntervalL2OfContinuousOn f hf
  let G := sourceIntervalL2OfContinuousOn g hg
  let Fbound := sourceIntervalLInfOfContinuousOn f hf
  let Gbound := sourceIntervalLInfOfContinuousOn g hg
  cases b
  · let P := actualSourceL2PotentialTimesLInf (star u) Fbound
    filter_upwards [Lp.coeFn_smul Complex.I (P - z • G),
      Lp.coeFn_sub P (z • G), Lp.coeFn_smul z G,
      actualSourceL2PotentialTimesLInf_ae (star u) Fbound,
      sourceIntervalLInfOfContinuousOn_ae f hf,
      sourceIntervalL2OfContinuousOn_ae g hg] with t hi hs hz hp hF hG
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi hs hz
    change (Complex.I • (P - z • G) : SourceIntervalL2) t =
      Complex.I * (actualPhysicalL2SourcePotential (star u) t * f t - z * g t)
    rw [hi, hs, hp, hF, hz, hG]
  · let P := actualSourceL2PotentialTimesLInf u Gbound
    filter_upwards [Lp.coeFn_smul Complex.I (z • F - P),
      Lp.coeFn_sub (z • F) P, Lp.coeFn_smul z F,
      actualSourceL2PotentialTimesLInf_ae u Gbound,
      sourceIntervalL2OfContinuousOn_ae f hf,
      sourceIntervalLInfOfContinuousOn_ae g hg] with t hi hs hz hp hF hG
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi hs hz
    change (Complex.I • (z • F - P) : SourceIntervalL2) t =
      Complex.I * (z * f t - actualPhysicalL2SourcePotential u t * g t)
    rw [hi, hs, hz, hF, hp, hG]

/-- True integrability is realized before using weak-test/IBP identities. -/
theorem actualContinuousReflectedDiracDerivativeRepresentative_intervalIntegrable
    (u : PhysicalL2) (z : ℂ) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (b : Bool) :
    IntervalIntegrable
      (actualContinuousReflectedDiracDerivativeRepresentative u z f g b) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact ((Lp.memLp (actualContinuousReflectedDiracDerivativeClass u z f g hf hg b)).integrable
    (by norm_num)).congr (actualContinuousReflectedDiracDerivativeClass_ae u z f g hf hg b)

end NlsGge.Schur
end
