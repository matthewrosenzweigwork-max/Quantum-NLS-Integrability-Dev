import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Support1
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2
import NlsGge.ThirdConsultation.KSPS.KSPS004Support

/- KSPS-004 SUPPORT02 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS004Support2.lean.
   Entry-wise evaluation of volterraTerm 3 (antidiagonal), continuity of the second term, the two off-diagonal
   entry bounds from the generic third-term estimate, antidiagonal operator norm, and the assembled core bound
   from an arbitrary KSPS-003 constant. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS003Support NlsGge.ThirdConsultation.KSPS004Support

namespace NlsGge.ThirdConsultation.KSPS004Support2

theorem term3_unfold (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 3 x lam φ =
      KSPSVolterra.integrateMatrix 0 x (fun t => KSPSVolterra.E lam (x - t) * KSPSVolterra.R *
        KSPSVolterra.phi (toPotPair φ) t * volterraTerm 2 t lam φ) := rfl

theorem volterra3_00 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : volterraTerm 3 x lam φ 0 0 = 0 := by
  rw [term3_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t _ => ?_)).trans (by simp)
  rw [KSPS003Support2.integrand_00, KSPS003Support2.volterra2_10]
  simp

theorem volterra3_11 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : volterraTerm 3 x lam φ 1 1 = 0 := by
  rw [term3_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t _ => ?_)).trans (by simp)
  rw [KSPS003Support2.integrand_11, KSPS003Support2.volterra2_01]
  simp

theorem volterra3_01 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 3 x lam φ 0 1 =
      Complex.I * ∫ t in (0 : ℝ)..x, Complex.exp (-(Complex.I * lam * ((x - t : ℝ) : ℂ))) *
        coverRep38 (physicalSobolevEmbed 1 φ.1) t * volterraTerm 2 t lam φ 1 1 := by
  rw [term3_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [KSPS003Support2.integrand_01]
  have hp : potRepFst38 (toPotPair φ) t = coverRep38 (physicalSobolevEmbed 1 φ.1) t := rfl
  rw [hp]
  ring

theorem volterra3_10 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 3 x lam φ 1 0 =
      (-Complex.I) * ∫ t in (0 : ℝ)..x, Complex.exp (Complex.I * lam * ((x - t : ℝ) : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 φ.2) t * volterraTerm 2 t lam φ 0 0 := by
  rw [term3_unfold]
  simp only [KSPSVolterra.integrateMatrix]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [KSPS003Support2.integrand_10]
  have hp : potRepSnd38 (toPotPair φ) t = coverRep38 (physicalSobolevEmbed 1 φ.2) t := rfl
  rw [hp]
  ring

theorem M2_00_cont (φ : SobolevC 1) (lam : ℂ) :
    ContinuousOn (fun t : ℝ => volterraTerm 2 t lam φ 0 0) (Set.Icc (0 : ℝ) 1) := by
  have h : (fun t : ℝ => volterraTerm 2 t lam φ 0 0) = fun t : ℝ =>
      (fun t : ℝ => Complex.exp (-(Complex.I * lam * (t : ℂ)))) t *
        ∫ s in (0 : ℝ)..t, Complex.exp ((2 * Complex.I * lam) * (s : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 φ.1) s *
          ∫ r in (0 : ℝ)..s, Complex.exp (-(2 * Complex.I * lam) * (r : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.2) r :=
    funext fun t => KSPS003Support2.volterra2_00 φ t lam
  rw [h]
  exact nested_cont _ (by fun_prop) _ _ (intervalIntegrable_coverRep38_one _)
    (intervalIntegrable_coverRep38_one _)

theorem M2_11_cont (φ : SobolevC 1) (lam : ℂ) :
    ContinuousOn (fun t : ℝ => volterraTerm 2 t lam φ 1 1) (Set.Icc (0 : ℝ) 1) := by
  have h : (fun t : ℝ => volterraTerm 2 t lam φ 1 1) = fun t : ℝ =>
      (fun t : ℝ => Complex.exp (Complex.I * lam * (t : ℂ))) t *
        ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 φ.2) s *
          ∫ r in (0 : ℝ)..s, Complex.exp ((2 * Complex.I * lam) * (r : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.1) r :=
    funext fun t => KSPS003Support2.volterra2_11 φ t lam
  rw [h]
  exact nested_cont _ (by fun_prop) _ _ (intervalIntegrable_coverRep38_one _)
    (intervalIntegrable_coverRep38_one _)

open scoped Matrix.Norms.L2Operator in
theorem rem_entry_le (φ : SobolevC 1) (t : ℝ) (lam : ℂ) (i : Fin 2) :
    ‖secondVolterraRemainder φ t lam i i‖ ≤ ‖secondVolterraRemainder φ t lam‖ := by
  have hA : secondVolterraRemainder φ t lam =
      Matrix.diagonal ![secondVolterraRemainder φ t lam 0 0, secondVolterraRemainder φ t lam 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KSPS003Support2.rem_01 φ t lam, KSPS003Support2.rem_10 φ t lam]
  calc ‖secondVolterraRemainder φ t lam i i‖
      ≤ ‖(![secondVolterraRemainder φ t lam 0 0, secondVolterraRemainder φ t lam 1 1] :
          Fin 2 → ℂ)‖ := by
        fin_cases i
        · simpa using norm_le_pi_norm
            (![secondVolterraRemainder φ t lam 0 0, secondVolterraRemainder φ t lam 1 1] :
              Fin 2 → ℂ) 0
        · simpa using norm_le_pi_norm
            (![secondVolterraRemainder φ t lam 0 0, secondVolterraRemainder φ t lam 1 1] :
              Fin 2 → ℂ) 1
    _ = ‖(Matrix.diagonal ![secondVolterraRemainder φ t lam 0 0,
          secondVolterraRemainder φ t lam 1 1] : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
        (Matrix.l2_opNorm_diagonal _).symm
    _ = ‖secondVolterraRemainder φ t lam‖ := by rw [← hA]

open scoped Matrix.Norms.L2Operator in
theorem swap_norm_le : ‖(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1 := by
  set s : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] with hs
  have h1 : Matrix.conjTranspose s * s = Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hs, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply]
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self s
  rw [h1, Matrix.l2_opNorm_diagonal] at h2
  have h3 : ‖(fun _ : Fin 2 => (1 : ℂ))‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun _ => by simp)
  nlinarith [norm_nonneg s]

open scoped Matrix.Norms.L2Operator in
theorem antidiag_norm_le {a b : ℂ} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖(!![0, a; b, 0] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans ha
  have e : (!![0, a; b, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![a, b] * !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  rw [Matrix.l2_opNorm_diagonal]
  have h1 : ‖(![a, b] : Fin 2 → ℂ)‖ ≤ B :=
    (pi_norm_le_iff_of_nonneg hB).2 (Fin.forall_fin_two.2 ⟨by simpa using ha, by simpa using hb⟩)
  calc _ ≤ B * 1 := mul_le_mul h1 swap_norm_le (norm_nonneg _) hB
    _ = B := mul_one B

open scoped Matrix.Norms.L2Operator in
theorem entry01_bound (φ : SobolevC 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ}
    (hlam : lam ≠ 0) {C3 : ℝ}
    (hC3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖secondVolterraRemainder φ t lam‖ ≤
      C3 * Real.exp (|lam.im| * t) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2) :
    ‖volterraTerm 3 x lam φ 0 1‖ ≤ Real.exp (|lam.im| * x) *
      ((2 * ((‖iotaCLM‖ * ‖φ.1‖) * (‖iotaCLM‖ * ‖φ.1‖) * (‖iotaCLM‖ * ‖φ.2‖)) +
        (‖derivCLM‖ * ‖φ.1‖) * ((‖iotaCLM‖ * ‖φ.1‖) * (‖iotaCLM‖ * ‖φ.2‖))) / (4 * ‖lam‖ ^ 2) +
        (‖iotaCLM‖ * ‖φ.1‖) * (C3 * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2)) := by
  have hu := sobolevPointValue_ae 1 φ.1
  have hv := sobolevPointValue_ae 1 φ.2
  rw [volterra3_01, norm_mul, Complex.norm_I, one_mul]
  have hq : ∀ t : ℝ, ∫ s in (0 : ℝ)..t, sobolevPointValue 1 φ.1 s * sobolevPointValue 1 φ.2 s =
      ∫ s in (0 : ℝ)..t, coverRep38 (physicalSobolevEmbed 1 φ.1) s *
        coverRep38 (physicalSobolevEmbed 1 φ.2) s := by
    intro t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hu, hv] with s h1 h2 _
    rw [h1, h2]
  have hdec : ∀ t ∈ Set.Icc (0 : ℝ) 1, volterraTerm 2 t lam φ 1 1 =
      (2 * lam)⁻¹ * (-Complex.I) * Complex.exp (Complex.I * lam * (t : ℂ)) *
        (∫ s in (0 : ℝ)..t, sobolevPointValue 1 φ.1 s * sobolevPointValue 1 φ.2 s) +
        secondVolterraRemainder φ t lam 1 1 := by
    intro t _
    rw [hq t]
    simp only [secondVolterraRemainder, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [KSPS003Support2.mt_11]
    ring
  exact third_generic (κ := lam) hlam hx (pa := fun t => sobolevPointValue 1 φ.1 t)
    (pb := fun t => sobolevPointValue 1 φ.2 t)
    (pa' := coverRep38 (physicalSobolevDerivative38 1 φ.1))
    (pb' := coverRep38 (physicalSobolevDerivative38 1 φ.2))
    (ac := coverRep38 (physicalSobolevEmbed 1 φ.1))
    (Mf := fun t => volterraTerm 2 t lam φ 1 1)
    (rem := fun t => secondVolterraRemainder φ t lam 1 1)
    (KSPS003Support2.pv_prim φ.1) (KSPS003Support2.pv_prim φ.2) hu (M2_11_cont φ lam)
    (cc := (2 * lam)⁻¹ * (-Complex.I)) (le_of_eq (by simp [norm_mul])) hdec
    (R := C3 * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2)
    (fun t ht => (rem_entry_le φ t lam 1).trans ((hC3 t ht).trans (le_of_eq (by ring))))
    (Ma := ‖iotaCLM‖ * ‖φ.1‖) (Va := ‖derivCLM‖ * ‖φ.1‖) (Mb := ‖iotaCLM‖ * ‖φ.2‖)
    (fun t _ => KSPS003Support2.pv_sup φ.1 t) (KSPS003Support2.deriv_L1 φ.1)
    (fun t _ => KSPS003Support2.pv_sup φ.2 t)

open scoped Matrix.Norms.L2Operator in
theorem entry10_bound (φ : SobolevC 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ}
    (hlam : lam ≠ 0) {C3 : ℝ}
    (hC3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖secondVolterraRemainder φ t lam‖ ≤
      C3 * Real.exp (|lam.im| * t) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2) :
    ‖volterraTerm 3 x lam φ 1 0‖ ≤ Real.exp (|lam.im| * x) *
      ((2 * ((‖iotaCLM‖ * ‖φ.2‖) * (‖iotaCLM‖ * ‖φ.2‖) * (‖iotaCLM‖ * ‖φ.1‖)) +
        (‖derivCLM‖ * ‖φ.2‖) * ((‖iotaCLM‖ * ‖φ.2‖) * (‖iotaCLM‖ * ‖φ.1‖))) / (4 * ‖lam‖ ^ 2) +
        (‖iotaCLM‖ * ‖φ.2‖) * (C3 * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2)) := by
  have hu := sobolevPointValue_ae 1 φ.1
  have hv := sobolevPointValue_ae 1 φ.2
  rw [volterra3_10, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hq : ∀ t : ℝ, ∫ s in (0 : ℝ)..t, sobolevPointValue 1 φ.2 s * sobolevPointValue 1 φ.1 s =
      ∫ s in (0 : ℝ)..t, coverRep38 (physicalSobolevEmbed 1 φ.1) s *
        coverRep38 (physicalSobolevEmbed 1 φ.2) s := by
    intro t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hu, hv] with s h1 h2 _
    rw [h1, h2, mul_comm]
  have hdec : ∀ t ∈ Set.Icc (0 : ℝ) 1, volterraTerm 2 t lam φ 0 0 =
      (2 * lam)⁻¹ * Complex.I * Complex.exp (Complex.I * (-lam) * (t : ℂ)) *
        (∫ s in (0 : ℝ)..t, sobolevPointValue 1 φ.2 s * sobolevPointValue 1 φ.1 s) +
        secondVolterraRemainder φ t lam 0 0 := by
    intro t _
    rw [hq t]
    simp only [secondVolterraRemainder, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [KSPS003Support2.mt_00]
    have e : Complex.exp (Complex.I * (-lam) * (t : ℂ)) =
        Complex.exp (-(Complex.I * lam * (t : ℂ))) := by congr 1; ring
    rw [e]
    ring
  have hrem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖secondVolterraRemainder φ t lam 0 0‖ ≤
      (C3 * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2) * Real.exp (|(-lam).im| * t) := by
    intro t ht
    rw [Complex.neg_im, abs_neg]
    exact (rem_entry_le φ t lam 0).trans ((hC3 t ht).trans (le_of_eq (by ring)))
  have hmain := third_generic (κ := -lam) (neg_ne_zero.mpr hlam) hx
    (pa := fun t => sobolevPointValue 1 φ.2 t) (pb := fun t => sobolevPointValue 1 φ.1 t)
    (pa' := coverRep38 (physicalSobolevDerivative38 1 φ.2))
    (pb' := coverRep38 (physicalSobolevDerivative38 1 φ.1))
    (ac := coverRep38 (physicalSobolevEmbed 1 φ.2))
    (Mf := fun t => volterraTerm 2 t lam φ 0 0)
    (rem := fun t => secondVolterraRemainder φ t lam 0 0)
    (KSPS003Support2.pv_prim φ.2) (KSPS003Support2.pv_prim φ.1) hv (M2_00_cont φ lam)
    (cc := (2 * lam)⁻¹ * Complex.I) (le_of_eq (by simp [norm_mul])) hdec
    (R := C3 * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2) hrem
    (Ma := ‖iotaCLM‖ * ‖φ.2‖) (Va := ‖derivCLM‖ * ‖φ.2‖) (Mb := ‖iotaCLM‖ * ‖φ.1‖)
    (fun t _ => KSPS003Support2.pv_sup φ.2 t) (KSPS003Support2.deriv_L1 φ.2)
    (fun t _ => KSPS003Support2.pv_sup φ.1 t)
  have e : ∀ t : ℝ, Complex.exp (-(Complex.I * (-lam) * ((x - t : ℝ) : ℂ))) =
      Complex.exp (Complex.I * lam * ((x - t : ℝ) : ℂ)) := fun t => by congr 1; ring
  simp only [e, Complex.neg_im, abs_neg, norm_neg] at hmain
  exact hmain

theorem num_final {K D C3 a b A L S : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (hC3 : 0 ≤ C3) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (haA : a ≤ A) (hbA : b ≤ A) (hL : 0 < L) (hS : 0 ≤ S) :
    S * ((2 * ((K * a) * (K * a) * (K * b)) + (D * a) * ((K * a) * (K * b))) / (4 * L ^ 2) +
      (K * a) * (C3 * A ^ 2 / L ^ 2)) ≤
    S * (((2 * K ^ 3 + D * K ^ 2) / 4 + K * C3) * A ^ 3 / L ^ 2) := by
  have hA : 0 ≤ A := ha.trans haA
  have h1 : 2 * ((K * a) * (K * a) * (K * b)) + (D * a) * ((K * a) * (K * b)) ≤
      (2 * K ^ 3 + D * K ^ 2) * A ^ 3 := by
    calc 2 * ((K * a) * (K * a) * (K * b)) + (D * a) * ((K * a) * (K * b))
        = (2 * K ^ 3 + D * K ^ 2) * (a * a * b) := by ring
      _ ≤ (2 * K ^ 3 + D * K ^ 2) * (A * A * A) := by gcongr
      _ = (2 * K ^ 3 + D * K ^ 2) * A ^ 3 := by ring
  have h2 : (K * a) * (C3 * A ^ 2 / L ^ 2) ≤ K * C3 * A ^ 3 / L ^ 2 := by
    calc (K * a) * (C3 * A ^ 2 / L ^ 2) = (K * C3 * a * A ^ 2) / L ^ 2 := by ring
      _ ≤ (K * C3 * A * A ^ 2) / L ^ 2 := by gcongr
      _ = K * C3 * A ^ 3 / L ^ 2 := by ring
  have h3 : (2 * ((K * a) * (K * a) * (K * b)) + (D * a) * ((K * a) * (K * b))) / (4 * L ^ 2) ≤
      (2 * K ^ 3 + D * K ^ 2) * A ^ 3 / (4 * L ^ 2) := by gcongr
  refine mul_le_mul_of_nonneg_left ?_ hS
  calc _ ≤ (2 * K ^ 3 + D * K ^ 2) * A ^ 3 / (4 * L ^ 2) + K * C3 * A ^ 3 / L ^ 2 :=
        add_le_add h3 h2
    _ = ((2 * K ^ 3 + D * K ^ 2) / 4 + K * C3) * A ^ 3 / L ^ 2 := by ring

theorem le_sobolevNorm_fst (φ : SobolevC 1) : ‖φ.1‖ ≤ sobolevNorm 1 φ := by
  unfold sobolevNorm
  calc ‖φ.1‖ = Real.sqrt (‖φ.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖φ.2‖])

theorem le_sobolevNorm_snd (φ : SobolevC 1) : ‖φ.2‖ ≤ sobolevNorm 1 φ := by
  unfold sobolevNorm
  calc ‖φ.2‖ = Real.sqrt (‖φ.2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖φ.1‖])

open scoped Matrix.Norms.L2Operator in
theorem third_core (φ : SobolevC 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ}
    (hlam : lam ≠ 0) {C3 : ℝ} (hC3pos : 0 ≤ C3)
    (hC3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖secondVolterraRemainder φ t lam‖ ≤
      C3 * Real.exp (|lam.im| * t) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2) :
    ‖volterraTerm 3 x lam φ‖ ≤
      (((2 * ‖iotaCLM‖ ^ 3 + ‖derivCLM‖ * ‖iotaCLM‖ ^ 2) / 4 + ‖iotaCLM‖ * C3) + 1) *
        Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2 := by
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hS : 0 ≤ Real.exp (|lam.im| * x) := (Real.exp_pos _).le
  have hK : 0 ≤ ‖iotaCLM‖ := ContinuousLinearMap.opNorm_nonneg _
  have hD : 0 ≤ ‖derivCLM‖ := ContinuousLinearMap.opNorm_nonneg _
  have e1 := entry01_bound φ hx hlam hC3
  have e2 := entry10_bound φ hx hlam hC3
  have n1 := num_final (K := ‖iotaCLM‖) (D := ‖derivCLM‖) (C3 := C3) (a := ‖φ.1‖) (b := ‖φ.2‖)
    (A := sobolevNorm 1 φ) (L := ‖lam‖) (S := Real.exp (|lam.im| * x)) hK hD hC3pos
    (norm_nonneg _) (norm_nonneg _) (le_sobolevNorm_fst φ) (le_sobolevNorm_snd φ) hL hS
  have n2 := num_final (K := ‖iotaCLM‖) (D := ‖derivCLM‖) (C3 := C3) (a := ‖φ.2‖) (b := ‖φ.1‖)
    (A := sobolevNorm 1 φ) (L := ‖lam‖) (S := Real.exp (|lam.im| * x)) hK hD hC3pos
    (norm_nonneg _) (norm_nonneg _) (le_sobolevNorm_snd φ) (le_sobolevNorm_fst φ) hL hS
  have hM : volterraTerm 3 x lam φ = !![0, volterraTerm 3 x lam φ 0 1;
      volterraTerm 3 x lam φ 1 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [volterra3_00, volterra3_11]
  rw [hM]
  have hA : 0 ≤ sobolevNorm 1 φ := Real.sqrt_nonneg _
  have hpos : 0 ≤ Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2 := by positivity
  refine (antidiag_norm_le (e1.trans n1) (e2.trans n2)).trans ?_
  have : (((2 * ‖iotaCLM‖ ^ 3 + ‖derivCLM‖ * ‖iotaCLM‖ ^ 2) / 4 + ‖iotaCLM‖ * C3) + 1) *
        Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2 =
      Real.exp (|lam.im| * x) * ((((2 * ‖iotaCLM‖ ^ 3 + ‖derivCLM‖ * ‖iotaCLM‖ ^ 2) / 4 +
        ‖iotaCLM‖ * C3) * sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2)) +
      Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2 := by ring
  rw [this]
  linarith

end NlsGge.ThirdConsultation.KSPS004Support2
end
