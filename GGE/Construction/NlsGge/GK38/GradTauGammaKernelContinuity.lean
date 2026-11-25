import NlsGge.GK38.GradTauGammaKernelMap
import NlsGge.GK38.GradTauGammaDefs
import NlsGge.GK38.GradTauGammaTauDerivative

/-! Actual discriminant contour kernels are integrable in the Banach space of
continuous closed-unit time kernels. Bounded kernel pairing/evaluation commutes
with their circle integral only after that integrability is earned. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem k4aGradDiscrim_time_spectral_continuous38 (φ : PotPair) :
    Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => gradDiscrim38 φ p.1 p.2) := by
  have hJ : Continuous (fun p : PotPair × ℂ => fundContP p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_fundContP.continuousOn
  have hA : Continuous (fun z : ℂ => (φ, z)) := continuous_const.prodMk continuous_id
  have hcomp := hJ.comp hA
  have hF : Continuous (fun z : ℂ => fundContP φ z) := by
    simpa only [Function.comp_def] using hcomp
  have hE : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => fundContP φ p.1 p.2) :=
    continuous_eval.comp ((hF.comp continuous_fst).prodMk continuous_snd)
  have hc (i j : Fin 2) : Continuous
      (fun p : ℂ × Icc (0 : ℝ) 1 => fundColumn38 φ p.1 p.2 j i) := by
    have he : (fun p : ℂ × Icc (0 : ℝ) 1 => fundColumn38 φ p.1 p.2 j i) =
        (fun p : ℂ × Icc (0 : ℝ) 1 => fundContP φ p.1 p.2 i j) := by
      funext p
      change ext38 (fundContP φ p.1) p.2 i j = fundContP φ p.1 p.2 i j
      rw [ext38_of_mem _ p.2.2]
    rw [he]
    simpa only [Function.comp_def] using
      (continuous_apply j).comp ((continuous_apply i).comp hE)
  have hm (i j : Fin 2) : Continuous
      (fun p : ℂ × Icc (0 : ℝ) 1 => monodromyPair φ p.1 i j) := by
    have hJm : Continuous (fun p : PotPair × ℂ => monodromyPair p.1 p.2 i j) :=
      continuousOn_univ.mp (analyticOnNhd_monodromyPair i j).continuousOn
    have hAm : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => (φ, p.1)) :=
      continuous_const.prodMk continuous_fst
    simpa only [Function.comp_def] using hJm.comp hAm
  have hc00 := hc 0 0
  have hc01 := hc 0 1
  have hc10 := hc 1 0
  have hc11 := hc 1 1
  have hm00 := hm 0 0
  have hm01 := hm 0 1
  have hm10 := hm 1 0
  have hm11 := hm 1 1
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [gradDiscrim38, starProd38, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop

theorem k4aGradDiscrimCont_continuous38 (φ : PotPair) :
    Continuous (fun z : ℂ => gradDiscrimCont38 φ z) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (k4aGradDiscrim_time_spectral_continuous38 φ)

def k4aQuotientKernelCont38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  (discrim φ z / perChar φ z) • gradDiscrimCont38 φ z

theorem k4aQuotientKernelCont_circleIntegrable38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (k4aQuotientKernelCont38 φ) (C n) (R n) := by
  have hD := (analyticOnNhd_discrim_z φ).continuousOn.mono (subset_univ (sphere (C n) (R n)))
  have hP := (analyticOnNhd_perChar_z φ).continuousOn.mono (subset_univ (sphere (C n) (R n)))
  have hQ := hD.div hP (isolating_periodic_boundary38 hf n)
  exact (hQ.smul (k4aGradDiscrimCont_continuous38 φ).continuousOn).circleIntegrable
    (isolating_radius_pos38 hf n).le

theorem k4aQuotientKernelCont_pairing38 (φ : PotPair) (z : ℂ) :
    integralPairCLM38 (k4aQuotientKernelCont38 φ z) ⟨1, zero_le_one, le_rfl⟩ =
      k4aQuotientCLM38 φ z :=
  k4aIntegralPair_kernel_smul38 (gradDiscrimCont38 φ z) (discrim φ z / perChar φ z)

def gradTauCont38 (φ : PotPair) (n : ℤ) : PairKernelCont38 :=
  -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (k4aQuotientKernelCont38 φ) (discC φ n) (discR φ n)

theorem gradTauCont38_apply (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (t : Icc (0 : ℝ) 1) : gradTauCont38 φ n t = gradTau38 φ n t := by
  have hi := k4aQuotientKernelCont_circleIntegrable38 φ _ _ (isolating_family38 φ hφ) n
  change -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (k4aQuotientKernelCont38 φ) (discC φ n) (discR φ n) t = _
  rw [k4aKernelEvaluation_circleIntegral38 _ _ _ hi t]
  rfl

theorem k4aTauCont_pairing38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    integralPairCLM38 (gradTauCont38 φ n) ⟨1, zero_le_one, le_rfl⟩ =
      k4aTauCLMOnCircle38 φ (discC φ) (discR φ) n := by
  have hi := k4aQuotientKernelCont_circleIntegrable38 φ _ _ (isolating_family38 φ hφ) n
  rw [gradTauCont38, k4aIntegralPair_kernel_smul38,
    k4aKernelPairing_circleIntegral38 _ _ _ hi]
  simp only [k4aQuotientKernelCont_pairing38]
  rfl

theorem hasFDerivAt_gradTauCont38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    HasFDerivAt (fun ψ => tauN ψ n)
      (integralPairCLM38 (gradTauCont38 φ n) ⟨1, zero_le_one, le_rfl⟩) φ := by
  rw [k4aTauCont_pairing38 φ hφ n]
  exact k4aTau_hasFDerivOnAnyCircle38 φ hφ _ _ (isolating_family38 φ hφ) n

end
end NlsGge.GK38
