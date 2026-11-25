import NlsGge.GK38.PoissonMixedRealKappaDerivative

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem analyticOnNhd_signedNorming38 (n : ℤ) :
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => signedNorming38 u n) univ := by
  intro u _
  have hA : AnalyticAt ℝ (fun v : PhysicalL2 => (realSlice v,(gkMu v n : ℂ))) u :=
    (realSlice.analyticAt u).prod
      (AnalyticAt.comp (g := fun x : ℝ => (x : ℂ)) (f := fun v : PhysicalL2 => gkMu v n)
        (Complex.ofRealCLM.analyticAt (gkMu u n)) (analyticAt_gkMu38 u n))
  have hU := AnalyticAt.comp
    (g := fun p : PotPair × ℂ => normingFactor p.1 p.2)
    (f := fun v : PhysicalL2 => (realSlice v,(gkMu v n : ℂ)))
    ((analyticOnNhd_normingFactor38 (realSlice u,(gkMu u n : ℂ))
      (mem_univ _)).restrictScalars (𝕜 := ℝ)) hA
  have hp : AnalyticAt ℝ
      (fun v : PhysicalL2 => parity n * normingFactor (realSlice v) (gkMu v n : ℂ)) u :=
    analyticAt_const.mul hU
  exact AnalyticAt.comp (g := fun z : ℂ => z.re)
    (f := fun v : PhysicalL2 => parity n * normingFactor (realSlice v) (gkMu v n : ℂ))
    (Complex.reCLM.analyticAt _) hp

theorem analyticOnNhd_realKappa38 (n : ℤ) :
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => realKappa38 u n) univ := by
  intro u _
  have hlog := (analyticAt_log (signedNorming_positive38 u n)).comp
    (f := fun v : PhysicalL2 => signedNorming38 v n) (x := u)
    (analyticOnNhd_signedNorming38 n u (mem_univ _))
  exact analyticAt_const.mul hlog

theorem realCanonicalNormingTarget : RealCanonicalNormingTarget := by
  refine ⟨analyticOnNhd_realKappa38,?_⟩
  intro u n
  have hp := signedNorming_positive38 u n
  refine ⟨hp,normingFactor_real_im38 u (gkMu u n),
    normingFactor_ne_zero_at_dirichlet_root38 _ _ (gkMu_root38 u n),?_,
    hasFDerivAt_realKappa38 u n,
    kernelHamField_realSlice38 _ (kappaKernel_realSymmetric38 u n)⟩
  change Real.exp ((2*Real.log (signedNorming38 u n))/2)=signedNorming38 u n
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),Real.exp_log hp]

end
end NlsGge.GK38.PoissonMixed38
