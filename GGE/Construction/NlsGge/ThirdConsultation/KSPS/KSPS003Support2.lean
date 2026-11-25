import Mathlib
import NlsGge.ThirdConsultation.KSPS.IBP002Support
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Support1
import NlsGge.ThirdConsultation.G6.Energy031D

                                                                                                             
                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS003Support2

theorem pv_prim (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    NlsGge.ThirdConsultation.KSPS003Support.PrimOn (fun x : ℝ => sobolevPointValue 1 u x)
      (coverRep38 (physicalSobolevDerivative38 1 u)) := by
  refine ⟨intervalIntegrable_coverRep38_one _, fun t ht => ?_⟩
  have h := NlsGge.ThirdConsultation.KSPS002Support.ibp_scalar u ht 0
  simp only [zero_mul, Complex.exp_zero, one_mul] at h
  beta_reduce
  linear_combination -h

theorem pv_sup (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (x : ℝ) :
    ‖sobolevPointValue 1 u x‖ ≤ ‖iotaCLM‖ * ‖u‖ := by
  have h : sobolevPointValue 1 u x = iotaCLM u (x : PhysicalCircle) := by
    simp only [sobolevPointValue, le_refl, dite_true]
    rw [iotaCLM_apply]
  rw [h]
  exact (ContinuousMap.norm_coe_le_norm (iotaCLM u) _).trans (iotaCLM.le_opNorm u)

theorem deriv_L1 (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    ∫ t in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) t‖ ≤ ‖derivCLM‖ * ‖u‖ := by
  refine (integral_coverRep38_le_one _).trans ?_
  rw [← derivCLM_apply]
  exact derivCLM.le_opNorm u

theorem scalar_entry_bound (u v : PhysicalSobolev38 ((1 : ℕ) : ℝ)) {lam : ℂ} (hlam : lam ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp (-(Complex.I * lam * (x : ℂ))) *
      ((∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 u) t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 v) s) +
        (2 * Complex.I * lam)⁻¹ * ∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 u) t *
          coverRep38 (physicalSobolevEmbed 1 v) t)‖ ≤
      2 * Real.exp (|lam.im| * x) *
        (((‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) * ((‖iotaCLM‖ + ‖derivCLM‖) * ‖v‖)) /
          ‖2 * Complex.I * lam‖ ^ 2 := by
  have hb := NlsGge.ThirdConsultation.KSPS003Support.remainder_bound
    (pv_prim u) (pv_prim v)
    (Mp := ‖iotaCLM‖ * ‖u‖) (Vp := ‖derivCLM‖ * ‖u‖)
    (Mq := ‖iotaCLM‖ * ‖v‖) (Vq := ‖derivCLM‖ * ‖v‖)
    (fun t _ => pv_sup u t) (deriv_L1 u) (fun t _ => pv_sup v t) (deriv_L1 v) hlam hx
  have hu := sobolevPointValue_ae 1 u
  have hv := sobolevPointValue_ae 1 v
  have hinner : ∀ t : ℝ, (∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
        sobolevPointValue 1 v s) =
      ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 v) s := by
    intro t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hv] with s hs _
    rw [hs]
  have h1 : (∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
          sobolevPointValue 1 u t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
            sobolevPointValue 1 v s) =
      ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 u) t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 v) s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hu] with t ht _
    rw [ht, hinner t]
  have h2 : (∫ t in (0 : ℝ)..x, sobolevPointValue 1 u t * sobolevPointValue 1 v t) =
      ∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 u) t *
        coverRep38 (physicalSobolevEmbed 1 v) t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hu, hv] with t ht1 ht2 _
    rw [ht1, ht2]
  try beta_reduce at hb
  rw [h1, h2] at hb
  refine hb.trans (le_of_eq ?_)
  ring

theorem integrand_00 (lam : ℂ) (x t : ℝ) (p : PotPair) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * T) 0 0 =
      Complex.exp (-(Complex.I * lam * ((x - t : ℝ) : ℂ))) * Complex.I * potRepFst38 p t *
        T 1 0 := by
  simp [KSPSVolterra.E, KSPSVolterra.R, KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two]

theorem integrand_01 (lam : ℂ) (x t : ℝ) (p : PotPair) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * T) 0 1 =
      Complex.exp (-(Complex.I * lam * ((x - t : ℝ) : ℂ))) * Complex.I * potRepFst38 p t *
        T 1 1 := by
  simp [KSPSVolterra.E, KSPSVolterra.R, KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two]

theorem integrand_10 (lam : ℂ) (x t : ℝ) (p : PotPair) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * T) 1 0 =
      Complex.exp (Complex.I * lam * ((x - t : ℝ) : ℂ)) * (-Complex.I) * potRepSnd38 p t *
        T 0 0 := by
  simp [KSPSVolterra.E, KSPSVolterra.R, KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two]

theorem integrand_11 (lam : ℂ) (x t : ℝ) (p : PotPair) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (KSPSVolterra.E lam (x - t) * KSPSVolterra.R * KSPSVolterra.phi p t * T) 1 1 =
      Complex.exp (Complex.I * lam * ((x - t : ℝ) : ℂ)) * (-Complex.I) * potRepSnd38 p t *
        T 0 1 := by
  simp [KSPSVolterra.E, KSPSVolterra.R, KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two]

theorem alg00 (E1 E2 E0 E3 cp G : ℂ) (he : E1 * E2 = E0 * E3) :
    E1 * Complex.I * cp * (-Complex.I * E2 * G) = E0 * (E3 * cp * G) := by
  linear_combination (-(cp * G * E1 * E2)) * Complex.I_mul_I + (cp * G) * he

theorem alg11 (E1 E2 E0 E3 cq H : ℂ) (he : E1 * E2 = E0 * E3) :
    E1 * (-Complex.I) * cq * (Complex.I * E2 * H) = E0 * (E3 * cq * H) := by
  linear_combination (-(cq * H * E1 * E2)) * Complex.I_mul_I + (cq * H) * he

theorem term2_unfold (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 2 x lam φ =
      KSPSVolterra.integrateMatrix 0 x (fun t => KSPSVolterra.E lam (x - t) * KSPSVolterra.R *
        KSPSVolterra.phi (toPotPair φ) t * volterraTerm 1 t lam φ) := rfl

theorem volterra2_00 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 2 x lam φ 0 0 =
      Complex.exp (-(Complex.I * lam * (x : ℂ))) *
        ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 φ.1) t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.2) s := by
  rw [term2_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [integrand_00, NlsGge.ThirdConsultation.KSPS002Support.term1_10 φ t lam]
  have hp : potRepFst38 (toPotPair φ) t = coverRep38 (physicalSobolevEmbed 1 φ.1) t := rfl
  rw [hp]
  exact alg00 _ _ _ _ _ _ (by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring)

theorem volterra2_11 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 2 x lam φ 1 1 =
      Complex.exp (Complex.I * lam * (x : ℂ)) *
        ∫ t in (0 : ℝ)..x, Complex.exp (-(2 * Complex.I * lam) * (t : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 φ.2) t *
          ∫ s in (0 : ℝ)..t, Complex.exp ((2 * Complex.I * lam) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.1) s := by
  rw [term2_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [integrand_11, NlsGge.ThirdConsultation.KSPS002Support.term1_01 φ t lam]
  have hp : potRepSnd38 (toPotPair φ) t = coverRep38 (physicalSobolevEmbed 1 φ.2) t := rfl
  rw [hp]
  exact alg11 _ _ _ _ _ _ (by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring)

theorem volterra2_01 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : volterraTerm 2 x lam φ 0 1 = 0 := by
  rw [term2_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t _ => ?_)).trans (by simp)
  rw [integrand_01, NlsGge.ThirdConsultation.KSPS002Support.term1_11]
  simp

theorem volterra2_10 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : volterraTerm 2 x lam φ 1 0 = 0 := by
  rw [term2_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t _ => ?_)).trans (by simp)
  rw [integrand_10, NlsGge.ThirdConsultation.KSPS002Support.term1_00]
  simp

theorem integratedQuadratic_eq (φ : SobolevC 1) (x : ℝ) :
    KSPSVolterra.integratedQuadratic φ x =
      (∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.1) t *
        coverRep38 (physicalSobolevEmbed 1 φ.2) t) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem mt_00 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    (freePropagator x lam * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) 0 0 =
      Complex.exp (-(Complex.I * lam * (x : ℂ))) * Complex.I *
        ∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.1) t *
          coverRep38 (physicalSobolevEmbed 1 φ.2) t := by
  rw [integratedQuadratic_eq]
  simp [freePropagator, KSPSVolterra.R, Matrix.mul_apply, Fin.sum_univ_two]

theorem mt_11 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    (freePropagator x lam * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) 1 1 =
      Complex.exp (Complex.I * lam * (x : ℂ)) * (-Complex.I) *
        ∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.1) t *
          coverRep38 (physicalSobolevEmbed 1 φ.2) t := by
  rw [integratedQuadratic_eq]
  simp [freePropagator, KSPSVolterra.R, Matrix.mul_apply, Fin.sum_univ_two]

theorem mt_01 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    (freePropagator x lam * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) 0 1 = 0 := by
  rw [integratedQuadratic_eq]
  simp [freePropagator, KSPSVolterra.R, Matrix.mul_apply, Fin.sum_univ_two]

theorem mt_10 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    (freePropagator x lam * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) 1 0 = 0 := by
  rw [integratedQuadratic_eq]
  simp [freePropagator, KSPSVolterra.R, Matrix.mul_apply, Fin.sum_univ_two]

theorem rem_01 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : secondVolterraRemainder φ x lam 0 1 = 0 := by
  simp [secondVolterraRemainder, volterra2_01, mt_01]

theorem rem_10 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : secondVolterraRemainder φ x lam 1 0 = 0 := by
  simp [secondVolterraRemainder, volterra2_10, mt_10]

theorem inv_I2 {lam : ℂ} (hlam : lam ≠ 0) : (2 * Complex.I * lam)⁻¹ = -((2 * lam)⁻¹ * Complex.I) := by
  simp only [mul_inv, Complex.inv_I]
  ring

theorem rem_00 (φ : SobolevC 1) (x : ℝ) {lam : ℂ} (hlam : lam ≠ 0) :
    secondVolterraRemainder φ x lam 0 0 =
      Complex.exp (-(Complex.I * lam * (x : ℂ))) *
        ((∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.1) t *
            ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
              coverRep38 (physicalSobolevEmbed 1 φ.2) s) +
          (2 * Complex.I * lam)⁻¹ * ∫ t in (0 : ℝ)..x,
            coverRep38 (physicalSobolevEmbed 1 φ.1) t *
              coverRep38 (physicalSobolevEmbed 1 φ.2) t) := by
  rw [secondVolterraRemainder, Matrix.sub_apply, Matrix.smul_apply, mt_00, volterra2_00,
    inv_I2 hlam, smul_eq_mul]
  ring

theorem rem_11 (φ : SobolevC 1) (x : ℝ) {lam : ℂ} (hlam : lam ≠ 0) :
    secondVolterraRemainder φ x lam 1 1 =
      Complex.exp (-(Complex.I * (-lam) * (x : ℂ))) *
        ((∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * (-lam)) * (t : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.2) t *
            ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * (-lam)) * (s : ℂ)) *
              coverRep38 (physicalSobolevEmbed 1 φ.1) s) +
          (2 * Complex.I * (-lam))⁻¹ * ∫ t in (0 : ℝ)..x,
            coverRep38 (physicalSobolevEmbed 1 φ.2) t *
              coverRep38 (physicalSobolevEmbed 1 φ.1) t) := by
  have e1 : Complex.exp (-(Complex.I * (-lam) * (x : ℂ))) = Complex.exp (Complex.I * lam * (x : ℂ)) := by
    congr 1; ring
  have e2 : ∀ t : ℝ, Complex.exp ((2 * Complex.I * (-lam)) * (t : ℂ)) =
      Complex.exp (-(2 * Complex.I * lam) * (t : ℂ)) := fun t => by congr 1; ring
  have e3 : ∀ t : ℝ, Complex.exp (-(2 * Complex.I * (-lam)) * (t : ℂ)) =
      Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) := fun t => by congr 1; ring
  have e4 : (2 * Complex.I * (-lam))⁻¹ = (2 * lam)⁻¹ * Complex.I := by
    have := inv_I2 (neg_ne_zero.mpr hlam)
    rw [this]
    simp only [mul_inv, Complex.inv_I, inv_neg]
    ring
  simp only [e1, e2, e3, e4]
  rw [secondVolterraRemainder, Matrix.sub_apply, Matrix.smul_apply, mt_11, volterra2_11, smul_eq_mul]
  have e5 : (∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.2) t *
      coverRep38 (physicalSobolevEmbed 1 φ.1) t) =
      ∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.1) t *
        coverRep38 (physicalSobolevEmbed 1 φ.2) t :=
    intervalIntegral.integral_congr (fun t _ => mul_comm _ _)
  rw [e5]
  ring

theorem num_bound (K p q e L : ℝ) (he : 0 ≤ e) (hL : 0 < L) :
    2 * e * ((K * p) * (K * q)) / (4 * L ^ 2) ≤ (K ^ 2 + 1) * e * (p ^ 2 + q ^ 2) / L ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := mul_nonneg (mul_nonneg (mul_nonneg he (sq_nonneg K)) (sq_nonneg L)) (sq_nonneg (p - q))
  have h2 := mul_nonneg (mul_nonneg (mul_nonneg he (sq_nonneg K)) (sq_nonneg L))
    (add_nonneg (sq_nonneg p) (sq_nonneg q))
  have h3 := mul_nonneg (mul_nonneg he (sq_nonneg L)) (add_nonneg (sq_nonneg p) (sq_nonneg q))
  nlinarith [h1, h2, h3]

theorem norm_two_I_mul (lam : ℂ) : ‖2 * Complex.I * lam‖ ^ 2 = 4 * ‖lam‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_I, mul_one]
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  ring

open scoped Matrix.Norms.L2Operator in
theorem remainder_matrix_bound (φ : SobolevC 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ}
    (hlam : lam ≠ 0) :
    ‖secondVolterraRemainder φ x lam‖ ≤
      ((‖iotaCLM‖ + ‖derivCLM‖) ^ 2 + 1) * Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 2 /
        ‖lam‖ ^ 2 := by
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have he : 0 ≤ Real.exp (|lam.im| * x) := (Real.exp_pos _).le
  have hs : sobolevNorm 1 φ ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    unfold sobolevNorm
    exact Real.sq_sqrt (by positivity)
  have hr : 0 ≤ ((‖iotaCLM‖ + ‖derivCLM‖) ^ 2 + 1) * Real.exp (|lam.im| * x) *
      sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2 := by positivity
  have h00 : ‖secondVolterraRemainder φ x lam 0 0‖ ≤ ((‖iotaCLM‖ + ‖derivCLM‖) ^ 2 + 1) *
      Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2 := by
    rw [rem_00 φ x hlam]
    refine (scalar_entry_bound φ.1 φ.2 hlam hx).trans ?_
    rw [norm_two_I_mul, hs]
    exact num_bound _ _ _ _ _ he hL
  have h11 : ‖secondVolterraRemainder φ x lam 1 1‖ ≤ ((‖iotaCLM‖ + ‖derivCLM‖) ^ 2 + 1) *
      Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2 := by
    rw [rem_11 φ x hlam]
    refine (scalar_entry_bound φ.2 φ.1 (neg_ne_zero.mpr hlam) hx).trans ?_
    rw [norm_two_I_mul, hs, norm_neg, Complex.neg_im, abs_neg, add_comm (‖φ.1‖ ^ 2)]
    exact num_bound _ _ _ _ _ he hL
  have hA : secondVolterraRemainder φ x lam =
      Matrix.diagonal ![secondVolterraRemainder φ x lam 0 0,
        secondVolterraRemainder φ x lam 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rem_01 φ x lam, rem_10 φ x lam]
  rw [hA, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hr).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simpa using h00
  · simpa using h11

end NlsGge.ThirdConsultation.KSPS003Support2
end
