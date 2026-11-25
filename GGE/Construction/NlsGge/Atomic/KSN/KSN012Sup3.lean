import Mathlib
import NlsGge.Atomic.KSN.KSN012Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Host

                                                                                                                             
                                                                                                                       
                                                                                                                          
                                                                                                               
                                                                           
                                                                                                                           
                                                                                                                          
                                                                                                                           
                                                                     
                                                                                                                             
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem sup3_fourierSeq38_symm (v : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    fourierSeq38 (physicalFourierL2.symm v) n = -(v (-n)) := by
  change -physicalFourierL2 (physicalFourierL2.symm v) (-n) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem sup3_weight_bound (m : ℤ) : 1 + (m : ℝ) ^ 2 ≤ 2 * scaleWeight 1 m ^ 2 := by
  have hw : scaleWeight 1 m = max 1 |(m : ℝ)| := by
    unfold scaleWeight bracket
    rw [Real.rpow_one, Nat.cast_natAbs, Int.cast_abs]
  rw [hw]
  have h1 : (1 : ℝ) ≤ max 1 |(m : ℝ)| := le_max_left _ _
  have h2 : |(m : ℝ)| ≤ max 1 |(m : ℝ)| := le_max_right _ _
  have h3 : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
  have h4 : (1 : ℝ) ≤ (max 1 |(m : ℝ)|) ^ 2 := one_le_pow₀ h1
  have h5 : |(m : ℝ)| ^ 2 ≤ (max 1 |(m : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  linarith

theorem sup3_scaleWeight_one_pos (m : ℤ) : 0 < scaleWeight 1 m := by
  unfold scaleWeight bracket
  rw [Real.rpow_one]
  exact lt_of_lt_of_le one_pos (le_max_left _ _)

theorem sup3_norm_sq_hasSum (x : PairScale 1) :
    HasSum (fun j : Bool × ℤ => ‖x j‖ ^ 2) (‖x‖ ^ 2) := by
  have hx := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hx

theorem sup3_fibre_summable (x : PairScale 1) (b : Bool) :
    Summable (fun n : ℤ => ‖x (b, -n)‖ ^ 2) := by
  have h := ((sup3_norm_sq_hasSum x).summable.comp_injective (Prod.mk_right_injective b))
  exact h.comp_injective neg_injective

theorem sup3_fibre_tsum_le (x : PairScale 1) (b : Bool) :
    (∑' n : ℤ, ‖x (b, -n)‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  have hneg : (∑' n : ℤ, ‖x (b, -n)‖ ^ 2) = ∑' n : ℤ, ‖x (b, n)‖ ^ 2 :=
    tsum_comp_neg (fun n : ℤ => ‖x (b, n)‖ ^ 2)
  rw [hneg, ← (sup3_norm_sq_hasSum x).tsum_eq]
  exact tsum_comp_le_tsum_of_inj (sup3_norm_sq_hasSum x).summable (fun _ => sq_nonneg _)
    (Prod.mk_right_injective b)

/-- The reflected Fourier sequence of the `b`-component of `pairPotential 1 x`. -/
def sup3_componentSeq (x : PairScale 1) (b : Bool) : ℤ → ℂ :=
  fourierSeq38 (physicalFourierL2.symm ⟨rawCoefficient 1 x b, rawCoefficient_mem 1 (by norm_num) x b⟩)

theorem sup3_componentSeq_apply (x : PairScale 1) (b : Bool) (n : ℤ) :
    sup3_componentSeq x b n = -(rawCoefficient 1 x b (-n)) := by
  unfold sup3_componentSeq
  rw [sup3_fourierSeq38_symm]

theorem sup3_mode_weight_nonneg (n : ℤ) : 0 ≤ sobolevModeWeight ((1 : ℕ) : ℝ) n :=
  Real.rpow_nonneg (le_of_lt (japaneseBracket_pos n)) _

theorem sup3_pointwise (x : PairScale 1) (b : Bool) (n : ℤ) :
    sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖sup3_componentSeq x b n‖ ^ 2 ≤ 2 * ‖x (b, -n)‖ ^ 2 := by
  rw [Nat.cast_one, NlsGge.NLS38.sobolevModeWeight_one_eq, sup3_componentSeq_apply, norm_neg]
  have hwpos := sup3_scaleWeight_one_pos (-n)
  have hbound := sup3_weight_bound (-n)
  have hcast : ((-n : ℤ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by push_cast; ring
  rw [hcast] at hbound
  have hnorm : ‖rawCoefficient 1 x b (-n)‖ = ‖x (b, -n)‖ / scaleWeight 1 (-n) := by
    unfold rawCoefficient
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hwpos.le]
  rw [hnorm, div_pow]
  have hw2 : 0 < scaleWeight 1 (-n) ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hw2]
  nlinarith [mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖x (b, -n)‖)]

theorem sup3_weighted_summable (x : PairScale 1) (b : Bool) :
    Summable (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖sup3_componentSeq x b n‖ ^ 2) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sup3_mode_weight_nonneg n) (sq_nonneg _))
    (sup3_pointwise x b) ((sup3_fibre_summable x b).mul_left 2)

theorem sup3_componentSeq_mem (x : PairScale 1) (b : Bool) :
    sup3_componentSeq x b ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
  (mem_seqSobolev38_iff _ _).2 (sup3_weighted_summable x b)

theorem sup3_weighted_tsum_le (x : PairScale 1) (b : Bool) :
    (∑' n : ℤ, sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖sup3_componentSeq x b n‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  have h := Summable.tsum_le_tsum (sup3_pointwise x b) (sup3_weighted_summable x b)
    ((sup3_fibre_summable x b).mul_left 2)
  rw [tsum_mul_left] at h
  linarith [sup3_fibre_tsum_le x b]

/-- The `h^1` carrier element of the `b`-component. -/
def sup3_componentCarrier (x : PairScale 1) (b : Bool) : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierMk38 ((1 : ℕ) : ℝ) (sup3_componentSeq x b) (sup3_componentSeq_mem x b)

/-- Bridge B3: the KSN pair scale `PairScale 1` into the KSPS complex Sobolev carrier `SobolevC 1`. -/
def toSobolevC (x : PairScale 1) : NlsGge.ThirdConsultation.KSPS.SobolevC 1 :=
  ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x true),
   (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x false))

theorem sup3_embed_component (x : PairScale 1) (b : Bool) :
    physicalSobolevEmbed 1 ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x b)) =
      physicalFourierL2.symm ⟨rawCoefficient 1 x b, rawCoefficient_mem 1 (by norm_num) x b⟩ := by
  apply fourierSeq38_injective
  funext n
  rw [physicalSobolevEmbed_fourier, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem toPotPair_toSobolevC (x : PairScale 1) :
    NlsGge.ThirdConsultation.KSPS.toPotPair (toSobolevC x) = pairPotential 1 (by norm_num) x :=
  Prod.ext (sup3_embed_component x true) (sup3_embed_component x false)

theorem sup3_component_norm_sq_le (x : PairScale 1) (b : Bool) :
    ‖(physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x b)‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
  rw [LinearIsometryEquiv.norm_map, sup3_componentCarrier, NlsGge.NLS38.norm_carrierMk38_eq_sqrt,
    Real.sq_sqrt (tsum_nonneg fun n => mul_nonneg (sup3_mode_weight_nonneg n) (sq_nonneg _))]
  exact sup3_weighted_tsum_le x b

theorem sobolevNorm_toSobolevC_le (x : PairScale 1) :
    NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 (toSobolevC x) ≤ 2 * ‖x‖ := by
  unfold NlsGge.ThirdConsultation.KSPS.sobolevNorm
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := sup3_component_norm_sq_le x true
  have h2 := sup3_component_norm_sq_le x false
  change ‖(physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x true)‖ ^ 2 +
      ‖(physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x false)‖ ^ 2 ≤ _
  nlinarith

theorem mu_eq_muSeq_toPotPair {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.mu φ n = muSeq (NlsGge.ThirdConsultation.KSPS.toPotPair φ) n := rfl

theorem criticalEigenvalue_eq_lamDot_toPotPair {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.criticalEigenvalue φ n =
      lamDot (NlsGge.ThirdConsultation.KSPS.toPotPair φ) n := rfl

theorem mu_toSobolevC (x : PairScale 1) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.mu (toSobolevC x) n = muSeq (pairPotential 1 (by norm_num) x) n := by
  rw [mu_eq_muSeq_toPotPair, toPotPair_toSobolevC]

theorem criticalEigenvalue_toSobolevC (x : PairScale 1) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.criticalEigenvalue (toSobolevC x) n =
      lamDot (pairPotential 1 (by norm_num) x) n := by
  rw [criticalEigenvalue_eq_lamDot_toPotPair, toPotPair_toSobolevC]

/-- Bridge B3, packaged. -/
theorem pairScale_sobolevC_bridge :
    ∃ T : PairScale 1 → NlsGge.ThirdConsultation.KSPS.SobolevC 1,
      (∀ x : PairScale 1, NlsGge.ThirdConsultation.KSPS.toPotPair (T x) = pairPotential 1 (by norm_num) x) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : PairScale 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 (T x) ≤ C * ‖x‖) ∧
      (∀ (x : PairScale 1) (n : ℤ),
        NlsGge.ThirdConsultation.KSPS.mu (T x) n = muSeq (pairPotential 1 (by norm_num) x) n) ∧
      (∀ (x : PairScale 1) (n : ℤ),
        NlsGge.ThirdConsultation.KSPS.criticalEigenvalue (T x) n = lamDot (pairPotential 1 (by norm_num) x) n) :=
  ⟨toSobolevC, toPotPair_toSobolevC, ⟨2, by norm_num, sobolevNorm_toSobolevC_le⟩,
    mu_toSobolevC, criticalEigenvalue_toSobolevC⟩

end
end NlsGge.ThirdConsultation.KSN
