import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support5
import NlsGge.ThirdConsultation.KSPS.KSPS006Support
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2
import NlsGge.ThirdConsultation.KSPS.IBP002Support
import NlsGge.ThirdConsultation.KSPSSupport.A1U01

/- KSPS-007 SUPPORT06 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Support6.lean.
   Pointwise analytic inputs on [0,1]: entrywise bounds of E, R, of the first Volterra term (O(1/lam), by the H1
   integration by parts ibp_scalar), of the integrated quadratic; l2Norm <= sobolevNorm; continuity ("Good") of
   E, M1, Q and of the inverse fundamental matrix. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS007Support5
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support6

/-! ### E and R -/

theorem EB_E (lam : ℂ) {Λ u : ℝ} (hΛ : |lam.im| ≤ Λ) (hu : |u| ≤ 1) :
    EB (KSPSVolterra.E lam u) (Real.exp Λ) := by
  have hle : |lam.im * u| ≤ Λ := by
    rw [abs_mul]
    calc |lam.im| * |u| ≤ Λ * 1 := mul_le_mul hΛ hu (abs_nonneg _) ((abs_nonneg _).trans hΛ)
      _ = Λ := mul_one _
  have he := Real.exp_pos Λ
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [KSPSVolterra.E] <;> simp [he.le]
  · rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (-(Complex.I * lam * (u : ℂ))).re = lam.im * u := by
      simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [this]; exact (le_abs_self _).trans hle
  · rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (Complex.I * lam * (u : ℂ)).re = -(lam.im * u) := by
      simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [this]; exact (neg_le_abs _).trans hle

theorem EB_R : EB KSPSVolterra.R 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [KSPSVolterra.R]

theorem Good_E (lam : ℂ) (x : ℝ) : Good (fun t => KSPSVolterra.E lam (x - t)) := by
  intro i j
  have : Continuous (fun u : ℝ => KSPSVolterra.E lam u) := NlsGge.GK38.continuous_freeE lam
  exact ((this.comp (continuous_const.sub continuous_id)).matrix_elem i j).continuousOn

theorem Good_Eneg (lam : ℂ) : Good (fun t => KSPSVolterra.E lam (-t)) := by
  intro i j
  have : Continuous (fun u : ℝ => KSPSVolterra.E lam u) := NlsGge.GK38.continuous_freeE lam
  exact ((this.comp continuous_neg).matrix_elem i j).continuousOn

/-! ### l2Norm <= sobolevNorm -/

theorem l2Norm_le (φ : SobolevC 1) : l2Norm φ ≤ sobolevNorm 1 φ := by
  unfold l2Norm sobolevNorm
  refine Real.sqrt_le_sqrt ?_
  have h1 := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 φ.1
  have h2 := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 φ.2
  have e1 : (toPotPair φ).1 = physicalSobolevEmbed 1 φ.1 := rfl
  have e2 : (toPotPair φ).2 = physicalSobolevEmbed 1 φ.2 := rfl
  rw [e1, e2]
  have := norm_nonneg (physicalSobolevEmbed 1 φ.1)
  have := norm_nonneg (physicalSobolevEmbed 1 φ.2)
  nlinarith

/-! ### a scalar oscillatory estimate (one H1 integration by parts) -/

theorem exp_le_of_re (ν : ℂ) {Λ2 : ℝ} (hre : |ν.re| ≤ Λ2) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp (ν * (s : ℂ))‖ ≤ Real.exp Λ2 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (ν * (s : ℂ)).re = ν.re * s := by simp [Complex.mul_re]
  rw [this]
  calc ν.re * s ≤ |ν.re * s| := le_abs_self _
    _ = |ν.re| * |s| := abs_mul _ _
    _ ≤ Λ2 * 1 := mul_le_mul hre (by rw [abs_of_nonneg hs.1]; exact hs.2) (abs_nonneg _)
        ((abs_nonneg _).trans hre)
    _ = Λ2 := mul_one _

theorem osc_bound (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) {ν : ℂ} (hν : ν ≠ 0) {Λ2 : ℝ}
    (hre : |ν.re| ≤ Λ2) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s‖ ≤
      Real.exp Λ2 * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) / ‖ν‖ := by
  have hνpos : 0 < ‖ν‖ := norm_pos_iff.mpr hν
  have hib := NlsGge.ThirdConsultation.KSPS002Support.ibp_scalar u ht ν
  set Iint := ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s
    with hIint
  set D := ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) *
    coverRep38 (physicalSobolevDerivative38 1 u) s with hDdef
  have hΛ2 : 0 ≤ Λ2 := (abs_nonneg _).trans hre
  have hE1 : 1 ≤ Real.exp Λ2 := Real.one_le_exp hΛ2
  have hι : 0 ≤ ‖iotaCLM‖ * ‖u‖ := by positivity
  have hδ : 0 ≤ ‖derivCLM‖ * ‖u‖ := by positivity
  have hkii : IntervalIntegrable (coverRep38 (physicalSobolevDerivative38 1 u)) volume 0 1 :=
    intervalIntegrable_coverRep38_one _
  have hkt : IntervalIntegrable (coverRep38 (physicalSobolevDerivative38 1 u)) volume 0 t :=
    NlsGge.ThirdConsultation.KSPS003Support.ii_mono hkii ht
  have hD : ‖D‖ ≤ Real.exp Λ2 * (‖derivCLM‖ * ‖u‖) := by
    have h1 := NlsGge.ThirdConsultation.KSPS003Support.norm_int_mul_le
      (w := fun s : ℝ => Complex.exp (ν * (s : ℂ))) (k := coverRep38 (physicalSobolevDerivative38 1 u))
      (x := t) (B := Real.exp Λ2) ht.1
      (fun s hs => exp_le_of_re ν hre ⟨hs.1, hs.2.trans ht.2⟩) hkt
    have h2 := NlsGge.ThirdConsultation.KSPS003Support.int_norm_mono hkii ht
    have h3 := NlsGge.ThirdConsultation.KSPS003Support2.deriv_L1 u
    calc ‖D‖ ≤ Real.exp Λ2 * ∫ s in (0 : ℝ)..t, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖ := h1
      _ ≤ Real.exp Λ2 * (‖derivCLM‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (Real.exp_pos _).le
  have hp1 : ‖Complex.exp (ν * (t : ℂ)) * sobolevPointValue 1 u t‖ ≤ Real.exp Λ2 * (‖iotaCLM‖ * ‖u‖) := by
    rw [norm_mul]
    exact mul_le_mul (exp_le_of_re ν hre ht) (NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u t)
      (norm_nonneg _) (Real.exp_pos _).le
  have hp0 : ‖sobolevPointValue 1 u 0‖ ≤ Real.exp Λ2 * (‖iotaCLM‖ * ‖u‖) :=
    (NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u 0).trans (le_mul_of_one_le_left hι hE1)
  have key : ‖ν‖ * ‖Iint‖ ≤ Real.exp Λ2 * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) := by
    rw [← norm_mul, hib]
    calc ‖Complex.exp (ν * (t : ℂ)) * sobolevPointValue 1 u t - sobolevPointValue 1 u 0 - D‖
        ≤ ‖Complex.exp (ν * (t : ℂ)) * sobolevPointValue 1 u t‖ + ‖sobolevPointValue 1 u 0‖ + ‖D‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ Real.exp Λ2 * (‖iotaCLM‖ * ‖u‖) + Real.exp Λ2 * (‖iotaCLM‖ * ‖u‖) +
            Real.exp Λ2 * (‖derivCLM‖ * ‖u‖) := by linarith
      _ = _ := by ring
  rw [le_div_iff₀ hνpos]
  linarith

theorem norm_fst_le_s (φ : SobolevC 1) : ‖φ.1‖ ≤ sobolevNorm 1 φ := by
  unfold sobolevNorm
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖φ.2‖])

theorem norm_snd_le_s (φ : SobolevC 1) : ‖φ.2‖ ≤ sobolevNorm 1 φ := by
  unfold sobolevNorm
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖φ.1‖])

/-! ### the first Volterra term is O(1/lam) -/

theorem entry_aux (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) {c ph ν lam : ℂ} {Λ s t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ≠ 0) (hc : ‖c‖ = 1) (hph : ‖ph‖ ≤ Real.exp Λ)
    (hν : ν ≠ 0) (hνn : ‖ν‖ = 2 * ‖lam‖) (hre : |ν.re| ≤ 2 * Λ) (hs : ‖u‖ ≤ s) :
    ‖c * ph * ∫ s' in (0 : ℝ)..t, Complex.exp (ν * (s' : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s'‖ ≤
      Real.exp (3 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * s) / ‖lam‖ := by
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hΛ0 : 0 ≤ Λ := by
    have := (abs_nonneg ν.re).trans hre
    linarith
  have hosc := osc_bound u hν hre ht
  rw [hνn] at hosc
  have hex : Real.exp (3 * Λ) = Real.exp Λ * Real.exp (2 * Λ) := by rw [← Real.exp_add]; ring_nf
  rw [norm_mul, norm_mul, hc, one_mul]
  have hκ : 0 ≤ 2 * ‖iotaCLM‖ + ‖derivCLM‖ := by positivity
  have h1 : ‖ph‖ * ‖∫ s' in (0 : ℝ)..t, Complex.exp (ν * (s' : ℂ)) *
      coverRep38 (physicalSobolevEmbed 1 u) s'‖ ≤
      Real.exp Λ * (Real.exp (2 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) / (2 * ‖lam‖)) :=
    mul_le_mul hph hosc (norm_nonneg _) (Real.exp_pos _).le
  refine h1.trans ?_
  rw [hex]
  have hE : 0 ≤ Real.exp Λ * Real.exp (2 * Λ) := by positivity
  have h3 : (2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖ ≤ (2 * ‖iotaCLM‖ + ‖derivCLM‖) * s :=
    mul_le_mul_of_nonneg_left hs hκ
  have h4 : Real.exp Λ * (Real.exp (2 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) / (2 * ‖lam‖)) =
      (Real.exp Λ * Real.exp (2 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖)) / 2 / ‖lam‖ := by
    field_simp
  rw [h4]
  have h5 : Real.exp Λ * Real.exp (2 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) ≤
      Real.exp Λ * Real.exp (2 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * s) :=
    mul_le_mul_of_nonneg_left h3 hE
  have h6 : 0 ≤ Real.exp Λ * Real.exp (2 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) := by positivity
  rw [mul_assoc (Real.exp Λ)]
  gcongr
  linarith

theorem M1_EB (φ : SobolevC 1) {lam : ℂ} (hlam : lam ≠ 0) {Λ : ℝ} (hΛ : |lam.im| ≤ Λ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    EB (volterraTerm 1 t lam φ)
      (Real.exp (3 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * sobolevNorm 1 φ) / ‖lam‖) := by
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans hΛ
  have hs0 : 0 ≤ sobolevNorm 1 φ := Real.sqrt_nonneg _
  have hpos : 0 ≤ Real.exp (3 * Λ) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * sobolevNorm 1 φ) / ‖lam‖ := by
    positivity
  have hph0 : ‖Complex.exp (-(Complex.I * lam * (t : ℂ)))‖ ≤ Real.exp Λ :=
    (NlsGge.ThirdConsultation.KSPS003Support.phase0_le lam ht.1).trans (Real.exp_le_exp.mpr (by
      calc |lam.im| * t ≤ |lam.im| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
        _ ≤ Λ := by linarith))
  have hph1 : ‖Complex.exp (Complex.I * lam * (t : ℂ))‖ ≤ Real.exp Λ :=
    (NlsGge.ThirdConsultation.KSPS005Support.phase_pos_le lam ht.1).trans (Real.exp_le_exp.mpr (by
      calc |lam.im| * t ≤ |lam.im| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
        _ ≤ Λ := by linarith))
  have hn2 : ‖(2 : ℂ) * Complex.I * lam‖ = 2 * ‖lam‖ := by simp
  have hn2' : ‖-((2 : ℂ) * Complex.I * lam)‖ = 2 * ‖lam‖ := by simp
  have hne : (2 : ℂ) * Complex.I * lam ≠ 0 := by simp [hlam]
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, NlsGge.ThirdConsultation.KSPS002Support.term1_00, norm_zero]; exact hpos
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [NlsGge.ThirdConsultation.KSPS002Support.term1_01]
    have hre : |(2 * Complex.I * lam).re| ≤ 2 * Λ := by
      have : (2 * Complex.I * lam).re = -(2 * lam.im) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, abs_neg, abs_mul]; simp only [abs_two]; linarith
    exact entry_aux φ.1 ht hlam Complex.norm_I hph0 hne hn2 hre (norm_fst_le_s φ)
  · simp only [Fin.mk_one, Fin.zero_eta]
    rw [NlsGge.ThirdConsultation.KSPS002Support.term1_10]
    have hre : |(-(2 * Complex.I * lam)).re| ≤ 2 * Λ := by
      have : (-(2 * Complex.I * lam)).re = 2 * lam.im := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, abs_mul]; simp only [abs_two]; linarith
    have hc : ‖-Complex.I‖ = 1 := by simp
    exact entry_aux φ.2 ht hlam hc hph1 (neg_ne_zero.mpr hne) hn2' hre (norm_snd_le_s φ)
  · simp only [Fin.mk_one, NlsGge.ThirdConsultation.KSPS002Support.term1_11, norm_zero]; exact hpos

end NlsGge.ThirdConsultation.KSPS007Support6
