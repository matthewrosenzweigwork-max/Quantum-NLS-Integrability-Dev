import NlsGge.GK38.IsolatingCriticalAnalytic

/-! Scalar spectral derivatives are identified with joint Fréchet derivatives before use. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

theorem analyticOnNhd_joint_spectral_deriv38 (F : PotPair × ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F univ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => deriv (fun z => F (p.1, z)) p.2) univ := by
  let e : (PotPair × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0, 1)
  have h := (e.analyticOnNhd univ).comp hF.fderiv (mapsTo_univ _ _)
  have he : (fun p : PotPair × ℂ => e (fderiv ℂ F p)) =
      (fun p : PotPair × ℂ => deriv (fun z => F (p.1, z)) p.2) := by
    funext p
    have hf := (hF p (mem_univ _)).differentiableAt.hasFDerivAt
    have hi : HasDerivAt (fun z : ℂ => (p.1, z)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hf.comp_hasDerivAt p.2 hi).deriv.symm
  simpa only [Function.comp_def, he] using h

theorem analyticOnNhd_perChar_joint38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) univ :=
  (analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const

theorem analyticOnNhd_perCharDeriv_joint38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => deriv (perChar p.1) p.2) univ :=
  analyticOnNhd_joint_spectral_deriv38 _ analyticOnNhd_perChar_joint38

theorem analyticOnNhd_discrimSecondDeriv_joint38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => deriv (deriv (discrim p.1)) p.2) univ :=
  analyticOnNhd_joint_spectral_deriv38 _ analyticOnNhd_discrimDeriv_joint38

end
end NlsGge.GK38
