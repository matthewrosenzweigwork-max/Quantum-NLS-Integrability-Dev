import Mathlib
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.G4.G4021
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN006Host
import NlsGge.Atomic.KSN.KSN006
import NlsGge.Atomic.KSN.KSN007Host

                                                                                                                     
                                                                                                                            
                                                                                                                     
                                                                                       
                                                                                                                                   
                                                                                                                                
                                                                                                                                 
                                                                                                     
set_option autoImplicit false

namespace NlsGge.Atomic.KSN007Support
noncomputable section
open Set Filter Topology MeasureTheory
open NlsGge.Atomic.KSN006Support

/-- Pure real inequality behind the KSN-007 pointwise bound. -/
theorem key_real7 {g m t w C c : ℝ} (hg : 0 < g) (hm : 0 < m) (ht : 0 < t)
    (hw1 : g / 2 ≤ w) (hC : 0 ≤ C) (hc : c ≤ C * g) :
    m * c / (Real.sqrt t * Real.sqrt m * Real.sqrt w)
      ≤ 2 * C * Real.sqrt m * Real.sqrt g * (Real.sqrt t)⁻¹ := by
  have hw : 0 < w := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have ha2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have hs2 : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  have hsa : Real.sqrt g / 2 ≤ Real.sqrt w := by
    by_contra h
    have h' := not_le.1 h
    nlinarith [mul_pos (sub_pos.2 h') (add_pos (div_pos hsg two_pos) hsw)]
  have hden : 0 < Real.sqrt t * Real.sqrt m * Real.sqrt w := by positivity
  rw [div_le_iff₀ hden]
  have hinv : (Real.sqrt t)⁻¹ * Real.sqrt t = 1 := inv_mul_cancel₀ hst.ne'
  have hqq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have hE : 2 * C * Real.sqrt m * Real.sqrt g * (Real.sqrt t)⁻¹
        * (Real.sqrt t * Real.sqrt m * Real.sqrt w)
      = 2 * C * m * Real.sqrt g * Real.sqrt w := by
    linear_combination (2 * C * Real.sqrt g * Real.sqrt w * ((Real.sqrt t)⁻¹ * Real.sqrt t)) * hqq
      + (2 * C * Real.sqrt g * Real.sqrt w * m) * hinv
  rw [hE]
  have h1 : c ≤ 2 * C * Real.sqrt g * Real.sqrt w := by
    have e1 : C * g ≤ 2 * C * Real.sqrt g * Real.sqrt w := by
      have : Real.sqrt g * (Real.sqrt g / 2) ≤ Real.sqrt g * Real.sqrt w :=
        mul_le_mul_of_nonneg_left hsa hsg.le
      nlinarith [mul_le_mul_of_nonneg_left this hC]
    linarith
  calc m * c ≤ m * (2 * C * Real.sqrt g * Real.sqrt w) := mul_le_mul_of_nonneg_left h1 hm.le
    _ = 2 * C * m * Real.sqrt g * Real.sqrt w := by ring

/-- Parametrised data of KSN-007 (constant numerator over the near root). -/
def constF (A B μ R c : ℂ) (t : ℝ) : ℂ := c * (μ - B) / nrF A B μ R t

theorem core7 {A B μ R c : ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C * ‖A - B‖)
    (hg : A - B ≠ 0) (hnear : ‖μ - B‖ ≤ ‖μ - A‖)
    (hR : R ^ 2 = (A - μ) * (B - μ)) :
    IntervalIntegrable (constF A B μ R c) volume 0 1 ∧
    ‖∫ t in (0 : ℝ)..1, constF A B μ R c t‖ ≤
      4 * C * Real.sqrt ‖A - B‖ * Real.sqrt ‖μ - B‖ := by
  by_cases hm : μ = B
  · have hF : constF A B μ R c = fun _ => 0 := by
      funext t
      simp [constF, hm]
    rw [hF]
    refine ⟨intervalIntegrable_const, ?_⟩
    simp [hm]
  · have hmne : μ - B ≠ 0 := sub_ne_zero.2 hm
    have hmpos : 0 < ‖μ - B‖ := norm_pos_iff.2 hmne
    have hgpos : 0 < ‖A - B‖ := norm_pos_iff.2 hg
    have hAμ : A - μ ≠ 0 := by
      intro h
      have hA : A = μ := sub_eq_zero.1 h
      apply hm
      have h0 : ‖μ - A‖ = 0 := by rw [← hA, sub_self, norm_zero]
      have h1 : ‖μ - B‖ ≤ 0 := by linarith
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
    have hlow : ∀ t ∈ Icc (0 : ℝ) 1, ‖A - B‖ / 2 ≤ ‖A - segF B μ t‖ := by
      intro t ht
      have hn : ‖μ - B‖ ≤ ‖(μ - B) - (A - B)‖ := by
        have e : (μ - B) - (A - B) = μ - A := by ring
        rw [e]
        exact hnear
      have h1 := seg_lower ht.1 ht.2 hg hn
      have e : A - B - (t : ℂ) * (μ - B) = A - segF B μ t := by
        simp only [segF]
        ring
      rwa [e] at h1
    have hAs : ∀ t ∈ Icc (0 : ℝ) 1, A - segF B μ t ≠ 0 := by
      intro t ht h
      have h1 := hlow t ht
      rw [h, norm_zero] at h1
      linarith
    have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖constF A B μ R c t‖ ≤
          (2 * C * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ)) := by
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hnr := nr_norm ht.1 hR hAμ (hAs t htI)
      have key := key_real7 (g := ‖A - B‖) (m := ‖μ - B‖) (t := t) (w := ‖A - segF B μ t‖)
        (C := C) (c := ‖c‖) hgpos hmpos ht.1 (hlow t htI) hC hc
      have e : ‖constF A B μ R c t‖ = ‖μ - B‖ * ‖c‖ /
          (Real.sqrt t * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - segF B μ t‖) := by
        unfold constF
        rw [norm_div, norm_mul, hnr, mul_comm]
      rw [e]
      have hrp : (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.1.le]
      rw [hrp] at key
      calc _ ≤ _ := key
        _ = _ := by ring
    have hG : IntervalIntegrable
        (fun t : ℝ => (2 * C * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ)))
        volume 0 1 :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul _
    have hmeas : AEStronglyMeasurable (constF A B μ R c)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have hseg : Measurable (segF B μ) := (continuous_segF B μ).measurable
      have hsq : Measurable (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable
      have hcs : Measurable (fun t : ℝ => Complex.sqrt ((A - segF B μ t) / (A - μ))) := by
        have h2 : Measurable (fun t : ℝ => (A - segF B μ t) / (A - μ)) :=
          (measurable_const.sub hseg).div_const _
        exact h2.pow_const (2⁻¹ : ℂ)
      have hden : Measurable (nrF A B μ R) := (hsq.mul measurable_const).mul hcs
      exact ((measurable_const.div hden).aestronglyMeasurable)
    have hint : IntervalIntegrable (constF A B μ R c) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      have hGi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hG
      refine Integrable.mono' hGi hmeas ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt)
    refine ⟨hint, ?_⟩
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall hpt) hG
    have hI : ∫ t in (0 : ℝ)..1,
        ((2 * C * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ)))
        = 2 * (2 * C * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
      have h0 : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
      rw [h0]
      simp only [Real.one_rpow]
      norm_num
      ring
    calc ‖∫ t in (0 : ℝ)..1, constF A B μ R c t‖
        ≤ ∫ t in (0 : ℝ)..1,
          ((2 * C * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ))) := hnorm
      _ = 2 * (2 * C * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) := hI
      _ = 4 * C * Real.sqrt ‖A - B‖ * Real.sqrt ‖μ - B‖ := by ring

end
end NlsGge.Atomic.KSN007Support

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign

theorem KSN007_main (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ (U : Set PotPair) (C : ℝ), IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧ 0 ≤ C ∧
    ∀ φ ∈ U, ∀ n : ℤ, gamma2 φ n ≠ 0 →
      ‖muSeq φ n - lamMinus φ n‖ ≤ ‖muSeq φ n - lamPlus φ n‖ →
      IntervalIntegrable (constantIntegrand n φ) volume 0 1 ∧
      ‖constantPart n φ‖ ≤ C * Real.sqrt ‖lamPlus φ n - lamMinus φ n‖ *
        Real.sqrt ‖muSeq φ n - lamMinus φ n‖ := by
  obtain ⟨V, hVn, hVB, C0, hC0, hfam⟩ := G4021 φ₀ hφ₀
  refine ⟨interior V, 4 * C0, isOpen_interior, mem_interior_iff_mem_nhds.2 hVn,
    interior_subset.trans hVB, by linarith, ?_⟩
  intro φ hφ n hγ hnear
  have hφV : φ ∈ V := interior_subset hφ
  have hφS : φ ∈ sourceBetaW := hVB hφV
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφS)
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hgk n
  have hg2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  have hg : lamPlus φ n - lamMinus φ n ≠ 0 := by
    intro h
    apply hγ
    rw [hg2, h]
    norm_num
  have hRsq := ((KSN002_main n).2 φ hφS).2.2.2
  have hτseg : tauN φ n ∈ gapSegment φ n := by
    rw [hτ]
    unfold gapSegment
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    ring
  have hK := (hfam φ hφV n).1 (tauN φ n) hτseg
  have hcore := NlsGge.Atomic.KSN007Support.core7 (A := lamPlus φ n) (B := lamMinus φ n)
    (μ := muSeq φ n) (R := terminalRoot n φ) (c := normalizedZeta n φ (tauN φ n) - 1)
    (C := C0) hC0.le hK hg hnear hRsq
  exact ⟨hcore.1, by
    have := hcore.2
    calc ‖constantPart n φ‖
        = ‖∫ t in (0 : ℝ)..1, NlsGge.Atomic.KSN007Support.constF (lamPlus φ n) (lamMinus φ n)
            (muSeq φ n) (terminalRoot n φ) (normalizedZeta n φ (tauN φ n) - 1) t‖ := rfl
      _ ≤ _ := this⟩

end
end NlsGge.ThirdConsultation.KSN
