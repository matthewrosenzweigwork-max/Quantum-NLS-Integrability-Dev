import NlsGge.GK38.NeumannLabels
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Joint analyticity of the actual critical characteristic, with the scalar
spectral derivative identified before the totalized fderiv is used. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

theorem jointDiscrim_derivative38 (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ, z)) (0, 1) = deriv (discrim φ) z := by
  have hf := (analyticOnNhd_discrim (φ, z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hi : HasDerivAt (fun w : ℂ => (φ, w)) (0, 1) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  exact (hf.comp_hasDerivAt z hi).deriv.symm

theorem analyticOnNhd_discrimDeriv_joint38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => deriv (discrim p.1) p.2) univ := by
  let e : (PotPair × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0, 1)
  have h := (e.analyticOnNhd univ).comp analyticOnNhd_discrim.fderiv (mapsTo_univ _ _)
  have he : (fun p : PotPair × ℂ => e (fderiv ℂ (fun q : PotPair × ℂ => discrim q.1 q.2) p)) =
      (fun p : PotPair × ℂ => deriv (discrim p.1) p.2) := by
    funext p
    exact jointDiscrim_derivative38 p.1 p.2
  simpa only [Function.comp_def, he] using h

end
end NlsGge.GK38
