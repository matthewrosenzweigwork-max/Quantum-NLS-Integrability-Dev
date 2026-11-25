import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support5
import NlsGge.ThirdConsultation.KSPS.KSPS007Support6

/- KSPS-007 SUPPORT07 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Support7.lean.
   Continuity ("Good") of the first Volterra term, of the integrated quadratic and of the inverse fundamental matrix
   on [0,1]; the entrywise bound of the integrated quadratic by sobolevNorm^2. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS007Support5 NlsGge.ThirdConsultation.KSPS007Support6
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support7

theorem cont_prim (ν : ℂ) (u : PhysicalL2) :
    ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * coverRep38 u s)
      (Set.Icc (0 : ℝ) 1) := by
  have hii : IntervalIntegrable (fun s : ℝ => Complex.exp (ν * (s : ℂ)) * coverRep38 u s) volume 0 1 :=
    (intervalIntegrable_coverRep38_one u).continuousOn_mul
      (by fun_prop : Continuous fun s : ℝ => Complex.exp (ν * (s : ℂ))).continuousOn
  have hfU : IntegrableOn (fun s : ℝ => Complex.exp (ν * (s : ℂ)) * coverRep38 u s)
      (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hii
  simpa [Set.uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval hfU

theorem Good_M1 (φ : SobolevC 1) (lam : ℂ) : Good (fun t => volterraTerm 1 t lam φ) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, NlsGge.ThirdConsultation.KSPS002Support.term1_00]
    exact continuousOn_const
  · simp only [Fin.zero_eta, Fin.mk_one, NlsGge.ThirdConsultation.KSPS002Support.term1_01]
    exact (by fun_prop : Continuous fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * lam * (t : ℂ)))).continuousOn.mul
      (cont_prim _ _)
  · simp only [Fin.mk_one, Fin.zero_eta, NlsGge.ThirdConsultation.KSPS002Support.term1_10]
    exact (by fun_prop : Continuous fun t : ℝ => -Complex.I * Complex.exp (Complex.I * lam * (t : ℂ))).continuousOn.mul
      (cont_prim _ _)
  · simp only [Fin.mk_one, NlsGge.ThirdConsultation.KSPS002Support.term1_11]
    exact continuousOn_const

theorem prod_ii (φ : SobolevC 1) :
    IntervalIntegrable (fun t => coverRep38 (physicalSobolevEmbed 1 φ.1) t *
      coverRep38 (physicalSobolevEmbed 1 φ.2) t) volume 0 1 := by
  have h := (intervalIntegrable_coverRep38_sq_one (physicalSobolevEmbed 1 φ.1)).add
    (intervalIntegrable_coverRep38_sq_one (physicalSobolevEmbed 1 φ.2))
  refine h.mono_fun' ?_ ?_
  · exact (((stronglyMeasurable_coverRep38 _).mul (stronglyMeasurable_coverRep38 _)).aestronglyMeasurable).restrict
  · refine Filter.Eventually.of_forall (fun t => ?_)
    show ‖coverRep38 (physicalSobolevEmbed 1 φ.1) t * coverRep38 (physicalSobolevEmbed 1 φ.2) t‖ ≤
      ‖coverRep38 (physicalSobolevEmbed 1 φ.1) t‖ ^ 2 + ‖coverRep38 (physicalSobolevEmbed 1 φ.2) t‖ ^ 2
    rw [norm_mul]
    nlinarith [norm_nonneg (coverRep38 (physicalSobolevEmbed 1 φ.1) t),
      norm_nonneg (coverRep38 (physicalSobolevEmbed 1 φ.2) t),
      sq_nonneg (‖coverRep38 (physicalSobolevEmbed 1 φ.1) t‖ - ‖coverRep38 (physicalSobolevEmbed 1 φ.2) t‖)]

theorem Good_Q (φ : SobolevC 1) : Good (fun t => KSPSVolterra.integratedQuadratic φ t) := by
  have hq : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, coverRep38 (physicalSobolevEmbed 1 φ.1) s *
      coverRep38 (physicalSobolevEmbed 1 φ.2) s) (Set.Icc (0 : ℝ) 1) := by
    have hfU : IntegrableOn (fun s : ℝ => coverRep38 (physicalSobolevEmbed 1 φ.1) s *
        coverRep38 (physicalSobolevEmbed 1 φ.2) s) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le zero_le_one] using
        (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (prod_ii φ)
    simpa [Set.uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval hfU
  intro i j
  have e : ∀ t, KSPSVolterra.integratedQuadratic φ t i j =
      (∫ s in (0 : ℝ)..t, coverRep38 (physicalSobolevEmbed 1 φ.1) s *
        coverRep38 (physicalSobolevEmbed 1 φ.2) s) * (1 : Mt) i j := by
    intro t
    rw [NlsGge.ThirdConsultation.KSPS003Support2.integratedQuadratic_eq]
    simp [Matrix.smul_apply]
  simp only [e]
  exact hq.mul continuousOn_const

theorem Q_EB (φ : SobolevC 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    EB (KSPSVolterra.integratedQuadratic φ t) (sobolevNorm 1 φ ^ 2) := by
  set e1 := physicalSobolevEmbed 1 φ.1 with he1
  set e2 := physicalSobolevEmbed 1 φ.2 with he2
  have hs : sobolevNorm 1 φ ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    unfold sobolevNorm
    exact Real.sq_sqrt (by positivity)
  have hsq1 := intervalIntegrable_coverRep38_sq_one e1
  have hsq2 := intervalIntegrable_coverRep38_sq_one e2
  have hq : ‖∫ s in (0 : ℝ)..t, coverRep38 e1 s * coverRep38 e2 s‖ ≤ sobolevNorm 1 φ ^ 2 := by
    have hii : IntervalIntegrable (fun s => ‖coverRep38 e1 s‖ ^ 2 + ‖coverRep38 e2 s‖ ^ 2) volume 0 1 :=
      hsq1.add hsq2
    have hit : IntervalIntegrable (fun s => ‖coverRep38 e1 s‖ ^ 2 + ‖coverRep38 e2 s‖ ^ 2) volume 0 t :=
      hii.mono_set (by
        rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl ht.2)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le ht.1
      (f := fun s => coverRep38 e1 s * coverRep38 e2 s)
      (g := fun s => ‖coverRep38 e1 s‖ ^ 2 + ‖coverRep38 e2 s‖ ^ 2)
      (Filter.Eventually.of_forall (fun s _ => by
        rw [norm_mul]
        nlinarith [norm_nonneg (coverRep38 e1 s), norm_nonneg (coverRep38 e2 s),
          sq_nonneg (‖coverRep38 e1 s‖ - ‖coverRep38 e2 s‖)])) hit
    have h2 : ∫ s in (0 : ℝ)..t, (‖coverRep38 e1 s‖ ^ 2 + ‖coverRep38 e2 s‖ ^ 2) ≤
        ∫ s in (0 : ℝ)..1, (‖coverRep38 e1 s‖ ^ 2 + ‖coverRep38 e2 s‖ ^ 2) :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun s => by positivity) hii
    rw [intervalIntegral.integral_add hsq1 hsq2, integral_sq_coverRep38_one,
      integral_sq_coverRep38_one] at h2
    have h3 := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 φ.1
    have h4 := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 φ.2
    rw [hs]
    have := norm_nonneg e1
    have := norm_nonneg e2
    nlinarith
  intro i j
  have e : KSPSVolterra.integratedQuadratic φ t i j =
      (∫ s in (0 : ℝ)..t, coverRep38 e1 s * coverRep38 e2 s) * (1 : Mt) i j := by
    rw [NlsGge.ThirdConsultation.KSPS003Support2.integratedQuadratic_eq, Matrix.smul_apply, smul_eq_mul]
  rw [e, norm_mul]
  have h1 : ‖(1 : Mt) i j‖ ≤ 1 := by fin_cases i <;> fin_cases j <;> simp
  calc _ ≤ ‖∫ s in (0 : ℝ)..t, coverRep38 e1 s * coverRep38 e2 s‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hq

theorem Good_N (φ : SobolevC 1) (lam : ℂ) :
    Good (fun t => KSPSVolterra.inverseFundamental φ t lam) := by
  have hF : ∀ k l : Fin 2, ContinuousOn (fun t => KSPSVolterra.fundamental φ t lam k l)
      (Set.Icc (0 : ℝ) 1) := by
    intro k l
    refine (NlsGge.Atomic.G1022S3.Mf_continuousOn (KSPSVolterra.toPair φ) lam zero_le_one k l).congr
      (fun t ht => ?_)
    rw [NlsGge.ThirdConsultation.KSPS007Support.fundamental_eq_Mf φ lam ht.1]
  intro i j
  fin_cases i <;> fin_cases j
  · exact hF 1 1
  · exact (hF 0 1).neg
  · exact (hF 1 0).neg
  · exact hF 0 0

end NlsGge.ThirdConsultation.KSPS007Support7
