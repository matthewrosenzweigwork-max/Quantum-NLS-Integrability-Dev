import NlsGge.ThirdConsultation.R.RamerSetting06

                                                                                                          
                                                                                                                         
                                                                                                     
                                                                                                            
                                                                                               
                                                                                                                        
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.R
noncomputable section

namespace R031Aux

/-- The finite standard Gaussian restricted to a measurable set, as a density integral (no measurability of the integrand). -/
theorem gaussian_lintegral_on
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (S : Set V) (hS : MeasurableSet S) (F : V → ℝ≥0∞) :
    ∫⁻ x in S, F x ∂(NlsGge.Ramer.finiteStdGaussian V) =
      ∫⁻ x in S, ENNReal.ofReal (NlsGge.Ramer.finiteGaussianDensity V x) * F x := by
  have hρ : Measurable (fun x : V => ENNReal.ofReal (NlsGge.Ramer.finiteGaussianDensity V x)) :=
    (NlsGge.Ramer.continuous_finiteGaussianDensity (V := V)).measurable.ennreal_ofReal
  have hfin : ∀ᵐ x ∂(volume.restrict S),
      ENNReal.ofReal (NlsGge.Ramer.finiteGaussianDensity V x) < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  rw [NlsGge.Ramer.finiteStdGaussian, restrict_withDensity hS]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρ hfin F

end R031Aux

/-- R-031: finite Gaussian change of variables on both open sets. -/
theorem finiteGaussian_changeOfVariables_on
    (d : ℕ) (T : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (U W : Set (GaussianFiniteCarrier d))
    (hT : C1DiffeomorphOn T U W)
    (f : GaussianFiniteCarrier d → ℝ)
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    gaussianIntegral d W f =
      gaussianIntegral d U
        (fun x => f (T x) * NlsGge.Ramer.finiteRamerDensity T x) := by
  obtain ⟨hU, hW, hBij, hC1, _⟩ := hT
  have hdiff : ∀ x ∈ U, HasFDerivWithinAt T (fderiv ℝ T x) U x := fun x hx =>
    ((hC1.differentiableOn (by norm_num) x hx).differentiableAt
      (hU.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (GaussianFiniteCarrier d))
    hU.measurableSet hdiff hBij.injOn
    (fun y => ENNReal.ofReal (NlsGge.Ramer.finiteGaussianDensity (GaussianFiniteCarrier d) y) *
      ENNReal.ofReal (f y))
  rw [hBij.image_eq] at key
  beta_reduce at key
  unfold gaussianIntegral
  rw [R031Aux.gaussian_lintegral_on (GaussianFiniteCarrier d) W hW.measurableSet,
    R031Aux.gaussian_lintegral_on (GaussianFiniteCarrier d) U hU.measurableSet, key]
  refine setLIntegral_congr_fun hU.measurableSet (fun x hx => ?_)
  beta_reduce
  have hD : 0 ≤ |(fderiv ℝ T x).det| := abs_nonneg _
  have hρx : 0 ≤ NlsGge.Ramer.finiteGaussianDensity (GaussianFiniteCarrier d) x :=
    (NlsGge.Ramer.finiteGaussianDensity_pos x).le
  have hρT0 : 0 ≤ NlsGge.Ramer.finiteGaussianDensity (GaussianFiniteCarrier d) (T x) :=
    (NlsGge.Ramer.finiteGaussianDensity_pos (T x)).le
  have hρT : NlsGge.Ramer.finiteGaussianDensity (GaussianFiniteCarrier d) (T x) =
      NlsGge.Ramer.finiteGaussianDensity (GaussianFiniteCarrier d) x *
        Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2) := by
    unfold NlsGge.Ramer.finiteGaussianDensity
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← ENNReal.ofReal_mul hρT0, ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hρx]
  congr 1
  unfold NlsGge.Ramer.finiteRamerDensity
  rw [hρT]
  ring

end
end NlsGge.ThirdConsultation.R
