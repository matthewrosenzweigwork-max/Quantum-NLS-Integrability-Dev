import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPSSupport.ANA01
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.Atomic.KSPS.KSPS010
import NlsGge.GK38.GradFundamentalL2

/- KSPS-011 SUPPORT7 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support7.lean.
   Step M3a: uniform L2 bound on the source forcing vector over |lam| >= Lambda, |Im lam| <= a, for EVERY PotPair f
   representing it a.e. on [0,1] (so independent of the choice made in Support5). Route as in KSPS011_STOP.md:
   KSPS-010 WKB_residual_regularity last clause (psi := phi), h150_forcing_ae, |exp| <= e^a. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem integral_sq_eq_eLpNorm {g : ℝ → ℂ}
    (hg : MemLp g 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    ∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2 =
      (eLpNorm g 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hnn : 0 ≤ ∫ t, ‖g t‖ ^ 2 ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    integral_nonneg (fun _ => by positivity)
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]
  have h2 : ((∫ t, ‖g t‖ ^ 2 ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) ^ (2⁻¹ : ℝ)) ^ 2 =
      ∫ t, ‖g t‖ ^ 2 ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
  rw [h2, intervalIntegral.integral_of_le zero_le_one,
    NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure, restrict_Ioc_eq_restrict_Icc]

theorem eLpNorm_coverRep38_eq (u : PhysicalL2) :
    eLpNorm (coverRep38 u) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure =
      ENNReal.ofReal ‖u‖ := by
  have hm := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc u
  have h := integral_sq_eq_eLpNorm hm
  rw [integral_sq_coverRep38_one] at h
  have hfin : eLpNorm (coverRep38 u) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≠ ∞ := hm.eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  have h0 := ENNReal.toReal_nonneg (a := eLpNorm (coverRep38 u) 2
    NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
  exact (sq_eq_sq₀ h0 (norm_nonneg u)).1 h.symm

theorem eLpNorm_const_mul_le (s : ℂ) (g : ℝ → ℂ) :
    eLpNorm (fun x => s * g x) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure =
      ENNReal.ofReal ‖s‖ * eLpNorm g 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
  have := eLpNorm_const_smul (μ := NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) (p := 2) s g
  simpa [Pi.smul_def, smul_eq_mul, ofReal_norm_eq_enorm] using this

theorem forcing_eLpNorm_uniform {N : ℕ} (hN : 1 ≤ N) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (b : Bool) (lam : ℂ), Λ ≤ ‖lam‖ →
      eLpNorm (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam) 2
        NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal M := by
  obtain ⟨ε, C, hε, hC, h⟩ :=
    (NlsGge.ThirdConsultation.KSPS.WKB_residual_regularity N hN φ).2.2.2.2.2.2.2 Λ hΛ
  obtain ⟨hco, ha1, ha2⟩ := h φ (by simpa using hε)
  refine ⟨C + C / (2 * Λ) + C / (4 * Λ ^ 2), by positivity, fun b lam hlam => ?_⟩
  have hl0 : lam ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlam; linarith
  have hae := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_ae φ b lam hl0
  obtain ⟨hA1m, hA1⟩ := ha1 b
  obtain ⟨hA2m, hA2⟩ := ha2 b lam hlam
  have hcm := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1))
  have hc : eLpNorm (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C := by
    show eLpNorm (coverRep38 _) 2 _ ≤ _
    rw [eLpNorm_coverRep38_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (hco b (N + 1) (by omega) le_rfl).2
    rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at this
    exact this
  have hn1 : ‖(2 * Complex.I * lam)⁻¹‖ ≤ (2 * Λ)⁻¹ := by
    rw [norm_inv]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    exact inv_anti₀ (by positivity) (by linarith)
  have hn2 : ‖((2 * Complex.I * lam) ^ 2)⁻¹‖ ≤ (4 * Λ ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    refine inv_anti₀ (by positivity) ?_
    nlinarith
  have m1 : MemLp (fun x => (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
    exact hA1m.const_mul _
  have m2 : MemLp (fun x => ((2 * Complex.I * lam) ^ 2)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
    exact hA2m.const_mul _
  rw [eLpNorm_congr_ae hae]
  calc _ ≤ eLpNorm (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x +
          (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure +
        eLpNorm (fun x => ((2 * Complex.I * lam) ^ 2)⁻¹ *
          NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure +
        eLpNorm (fun x => (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) +
        eLpNorm (fun x => ((2 * Complex.I * lam) ^ 2)⁻¹ *
          NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal C + ENNReal.ofReal ((2 * Λ)⁻¹) * ENNReal.ofReal C) +
        ENNReal.ofReal ((4 * Λ ^ 2)⁻¹) * ENNReal.ofReal C := by
        rw [eLpNorm_const_mul_le, eLpNorm_const_mul_le]
        exact add_le_add (add_le_add hc (mul_le_mul' (ENNReal.ofReal_le_ofReal hn1) hA1))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hn2) hA2)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hC.le (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp

theorem sourceForcingVector_component_norm_le {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (a : ℝ) (ha : |lam.1.im| ≤ a) (i : Fin 2) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖sourceForcingVector φ b lam t i‖ ≤
      Real.exp a * ‖NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1 t‖ := by
  have hex : ∀ s : ℝ, s = lam.1.im ∨ s = -lam.1.im →
      Real.exp (s * t) ≤ Real.exp a := by
    intro s hs
    apply Real.exp_le_exp.2
    have h1 : |s| ≤ a := by rcases hs with rfl | rfl <;> simpa using ha
    have h2 : |s * t| ≤ |s| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_nonneg ht.1]; exact ht.2)
    exact (le_abs_self _).trans (h2.trans h1)
  have hnn := norm_nonneg (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1 t)
  have hexp := Real.exp_pos a
  cases b
  · fin_cases i
    · simp [sourceForcingVector]; positivity
    · simp only [sourceForcingVector, Bool.false_eq_true, ↓reduceIte, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ hnn
      rw [Complex.norm_exp]
      convert hex lam.1.im (Or.inl rfl) using 2
      simp
  · fin_cases i
    · simp only [sourceForcingVector, ↓reduceIte, Fin.zero_eta, Matrix.cons_val_zero, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ hnn
      rw [Complex.norm_exp]
      convert hex (-lam.1.im) (Or.inr rfl) using 2
      simp
    · simp [sourceForcingVector]; positivity

theorem norm_le_of_ae_le {u : PhysicalL2} {g : ℝ → ℂ} {E : ℝ} (hE : 0 ≤ E)
    (hg : MemLp g 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (hae : ∀ᵐ t ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure, ‖coverRep38 u t‖ ≤ E * ‖g t‖) :
    ‖u‖ ≤ E * (eLpNorm g 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal := by
  have hIoc : volume.restrict (Ioc (0 : ℝ) 1) = NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
    unfold NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure; exact restrict_Ioc_eq_restrict_Icc
  have hint : IntervalIntegrable (fun t => (E * ‖g t‖) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn, hIoc]
    simpa [mul_pow] using ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg).const_mul (E ^ 2)
  have h1 : ‖u‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, (E * ‖g t‖) ^ 2 := by
    rw [← integral_sq_coverRep38_one]
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one
      (intervalIntegrable_coverRep38_sq_one u) hint ?_
    show _ ≤ᵐ[NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure] _
    filter_upwards [hae] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have h2 : ∫ t in (0 : ℝ)..1, (E * ‖g t‖) ^ 2 =
      (E * (eLpNorm g 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal) ^ 2 := by
    simp only [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_sq_eq_eLpNorm hg]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (h1.trans h2.le)

theorem sourceForcing_vectorL2Norm_le {N : ℕ} (hN : 1 ≤ N) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (Λ a : ℝ) (hΛ : 0 < Λ) (ha : 0 ≤ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), Λ ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) →
        NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm f ≤ K := by
  obtain ⟨M, hM0, hM⟩ := forcing_eLpNorm_uniform hN φ Λ hΛ
  refine ⟨2 * Real.exp a * M, by positivity, fun b lam hlam hIm f hf => ?_⟩
  have hfm := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_memLp φ b lam.1
  have hMb : (eLpNorm (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal ≤ M :=
    ENNReal.toReal_le_of_le_ofReal hM0 (hM b lam.1 hlam)
  have hcomp : ∀ (u : PhysicalL2) (i : Fin 2),
      (∀ t, coverRep38 u t = ![potRepFst38 f t, potRepSnd38 f t] i) → ‖u‖ ≤ Real.exp a * M := by
    intro u i hu
    refine (norm_le_of_ae_le (Real.exp_pos a).le hfm ?_).trans
      (mul_le_mul_of_nonneg_left hMb (Real.exp_pos a).le)
    have hae : ∀ᵐ t ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure,
        ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t := hf
    have hmem : ∀ᵐ t ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure, t ∈ Icc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hae, hmem] with t ht1 ht2
    rw [hu t, ht1]
    exact sourceForcingVector_component_norm_le φ b lam a hIm i t ht2
  have h1 : ‖f.1‖ ≤ Real.exp a * M := hcomp f.1 0 (fun t => rfl)
  have h2 : ‖f.2‖ ≤ Real.exp a * M := hcomp f.2 1 (fun t => rfl)
  unfold NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm
  calc Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2) ≤ Real.sqrt ((‖f.1‖ + ‖f.2‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg f.1, norm_nonneg f.2])
    _ = ‖f.1‖ + ‖f.2‖ := Real.sqrt_sq (by positivity)
    _ ≤ 2 * Real.exp a * M := by linarith

end NlsGge.ThirdConsultation.KSPSWKB
