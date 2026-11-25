import Mathlib
import NlsGge.Atomic.KSN.KSN012Sup3

                                                                                                                             
                                                                                                                    
                                                                                                                       
                                                                                                                        
                                                                                                                    
                                                                                                                        
                                                                                                                     
                                                                                                   
                                                                                                       
                                                                      
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem supN_scaleWeight_eq (N : ℕ) (m : ℤ) :
    scaleWeight (N : ℝ) m = (max 1 |(m : ℝ)|) ^ N := by
  unfold scaleWeight bracket
  rw [Real.rpow_natCast, Nat.cast_natAbs, Int.cast_abs]

theorem supN_scaleWeight_pos (N : ℕ) (m : ℤ) : 0 < scaleWeight (N : ℝ) m := by
  rw [supN_scaleWeight_eq]
  exact pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) N

theorem supN_modeWeight_eq (N : ℕ) (n : ℤ) :
    sobolevModeWeight (N : ℝ) n = (1 + (n : ℝ) ^ 2) ^ N := by
  rw [NlsGge.NLS38.sobolevModeWeight_natCast_eq, pow_mul]
  congr 1
  unfold japaneseBracket
  exact Real.sq_sqrt (by positivity)

theorem supN_modeWeight_nonneg (N : ℕ) (n : ℤ) : 0 ≤ sobolevModeWeight (N : ℝ) n := by
  rw [supN_modeWeight_eq]; positivity

theorem supN_weight_bound (N : ℕ) (m : ℤ) :
    (1 + (m : ℝ) ^ 2) ^ N ≤ (2 : ℝ) ^ N * (scaleWeight (N : ℝ) m) ^ 2 := by
  rw [supN_scaleWeight_eq, ← pow_mul, mul_comm N 2, pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h1 : (1 : ℝ) ≤ max 1 |(m : ℝ)| := le_max_left _ _
  have h2 : |(m : ℝ)| ≤ max 1 |(m : ℝ)| := le_max_right _ _
  have h3 : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
  have h4 : (1 : ℝ) ≤ (max 1 |(m : ℝ)|) ^ 2 := one_le_pow₀ h1
  have h5 : |(m : ℝ)| ^ 2 ≤ (max 1 |(m : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  linarith

theorem supN_norm_sq_hasSum (N : ℕ) (x : PairScale (N : ℝ)) :
    HasSum (fun j : Bool × ℤ => ‖x j‖ ^ 2) (‖x‖ ^ 2) := by
  have hx := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hx

theorem supN_fibre_hasSum (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) :
    HasSum (fun n : ℤ => ‖x (b, -n)‖ ^ 2) (∑' n : ℤ, ‖x (b, n)‖ ^ 2) := by
  have h := ((supN_norm_sq_hasSum N x).summable.comp_injective (Prod.mk_right_injective b))
  have h2 : Summable (fun n : ℤ => ‖x (b, -n)‖ ^ 2) := h.comp_injective neg_injective
  have hneg : (∑' n : ℤ, ‖x (b, -n)‖ ^ 2) = ∑' n : ℤ, ‖x (b, n)‖ ^ 2 :=
    tsum_comp_neg (fun n : ℤ => ‖x (b, n)‖ ^ 2)
  rw [← hneg]
  exact h2.hasSum

theorem supN_fibre_sum (N : ℕ) (x : PairScale (N : ℝ)) :
    (∑' n : ℤ, ‖x (true, n)‖ ^ 2) + (∑' n : ℤ, ‖x (false, n)‖ ^ 2) = ‖x‖ ^ 2 := by
  have hf : ∀ b : Bool, HasSum (fun n : ℤ => ‖x (b, n)‖ ^ 2) (∑' n : ℤ, ‖x (b, n)‖ ^ 2) := fun b =>
    ((supN_norm_sq_hasSum N x).summable.comp_injective (Prod.mk_right_injective b)).hasSum
  have h := (supN_norm_sq_hasSum N x).prod_fiberwise hf
  have h2 := hasSum_fintype (fun b : Bool => ∑' n : ℤ, ‖x (b, n)‖ ^ 2)
  rw [Fintype.sum_bool] at h2
  exact h2.unique h

theorem supN_pointwise (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) (n : ℤ) :
    sobolevModeWeight (N : ℝ) n * ‖-rawCoefficient (N : ℝ) x b (-n)‖ ^ 2 ≤
      (2 : ℝ) ^ N * ‖x (b, -n)‖ ^ 2 := by
  rw [norm_neg, supN_modeWeight_eq]
  have hwpos := supN_scaleWeight_pos N (-n)
  have hbound := supN_weight_bound N (-n)
  have hcast : ((-n : ℤ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by push_cast; ring
  rw [hcast] at hbound
  have hnorm : ‖rawCoefficient (N : ℝ) x b (-n)‖ = ‖x (b, -n)‖ / scaleWeight (N : ℝ) (-n) := by
    unfold rawCoefficient
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hwpos.le]
  rw [hnorm, div_pow]
  have hw2 : 0 < scaleWeight (N : ℝ) (-n) ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hw2]
  nlinarith [mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖x (b, -n)‖)]

theorem supN_weighted_summable (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) :
    Summable (fun n : ℤ =>
      sobolevModeWeight (N : ℝ) n * ‖-rawCoefficient (N : ℝ) x b (-n)‖ ^ 2) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (supN_modeWeight_nonneg N n) (sq_nonneg _))
    (supN_pointwise N x b) ((supN_fibre_hasSum N x b).summable.mul_left _)

theorem supN_weighted_tsum_le (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) :
    (∑' n : ℤ, sobolevModeWeight (N : ℝ) n * ‖-rawCoefficient (N : ℝ) x b (-n)‖ ^ 2) ≤
      (2 : ℝ) ^ N * ∑' n : ℤ, ‖x (b, n)‖ ^ 2 := by
  have h := Summable.tsum_le_tsum (supN_pointwise N x b) (supN_weighted_summable N x b)
    ((supN_fibre_hasSum N x b).summable.mul_left _)
  rw [tsum_mul_left, (supN_fibre_hasSum N x b).tsum_eq] at h
  exact h

theorem rawCoefficient_reflected_mem
    (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) :
  (fun n : ℤ => -rawCoefficient (N : ℝ) x b (-n)) ∈
    seqSobolev38 (N : ℝ) :=
  (mem_seqSobolev38_iff _ _).2 (supN_weighted_summable N x b)

def toSobolevCN (N : ℕ) (x : PairScale (N : ℝ)) :
    KSPS.SobolevC N :=
  ((physicalSobolevFourierEquiv38 (N : ℝ)).symm
      (carrierMk38 (N : ℝ)
        (fun n : ℤ => -rawCoefficient (N : ℝ) x true (-n))
        (rawCoefficient_reflected_mem N x true)),
   (physicalSobolevFourierEquiv38 (N : ℝ)).symm
      (carrierMk38 (N : ℝ)
        (fun n : ℤ => -rawCoefficient (N : ℝ) x false (-n))
        (rawCoefficient_reflected_mem N x false)))

theorem toSobolevCN_fourier_first
    (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ) :
  fourierSeq38 (physicalSobolevEmbed N (toSobolevCN N x).1) n =
    -rawCoefficient (N : ℝ) x true (-n) := by
  rw [physicalSobolevEmbed_fourier]
  unfold toSobolevCN
  rw [LinearIsometryEquiv.apply_symm_apply, carrierCoe38_mk]

theorem toSobolevCN_fourier_second
    (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ) :
  fourierSeq38 (physicalSobolevEmbed N (toSobolevCN N x).2) n =
    -rawCoefficient (N : ℝ) x false (-n) := by
  rw [physicalSobolevEmbed_fourier]
  unfold toSobolevCN
  rw [LinearIsometryEquiv.apply_symm_apply, carrierCoe38_mk]

theorem supN_embed_eq (N : ℕ) (u : PhysicalSobolev38 (N : ℝ)) (x : PairScale (N : ℝ)) (b : Bool)
    (hu : ∀ n : ℤ, fourierSeq38 (physicalSobolevEmbed N u) n = -rawCoefficient (N : ℝ) x b (-n)) :
    physicalSobolevEmbed N u =
      physicalFourierL2.symm ⟨rawCoefficient (N : ℝ) x b,
        rawCoefficient_mem (N : ℝ) (Nat.cast_nonneg N) x b⟩ := by
  apply fourierSeq38_injective
  funext n
  rw [hu n, sup3_fourierSeq38_symm]

theorem toPotPair_toSobolevCN
    (N : ℕ) (x : PairScale (N : ℝ)) :
  KSPS.toPotPair (toSobolevCN N x) =
    pairPotential (N : ℝ) (Nat.cast_nonneg N) x :=
  Prod.ext (supN_embed_eq N _ x true (toSobolevCN_fourier_first N x))
    (supN_embed_eq N _ x false (toSobolevCN_fourier_second N x))

theorem supN_component_norm_sq (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) :
    ‖(physicalSobolevFourierEquiv38 (N : ℝ)).symm
        (carrierMk38 (N : ℝ) (fun n : ℤ => -rawCoefficient (N : ℝ) x b (-n))
          (rawCoefficient_reflected_mem N x b))‖ ^ 2 ≤
      (2 : ℝ) ^ N * ∑' n : ℤ, ‖x (b, n)‖ ^ 2 := by
  rw [LinearIsometryEquiv.norm_map, NlsGge.NLS38.norm_carrierMk38_eq_sqrt,
    Real.sq_sqrt (tsum_nonneg fun n => mul_nonneg (supN_modeWeight_nonneg N n) (sq_nonneg _))]
  exact supN_weighted_tsum_le N x b

theorem supN_sobolevNorm_sq (N : ℕ) (φ : KSPS.SobolevC N) :
    KSPS.sobolevNorm N φ ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
  unfold KSPS.sobolevNorm
  exact Real.sq_sqrt (by positivity)

theorem sobolevNorm_toSobolevCN_sq_le
    (N : ℕ) (x : PairScale (N : ℝ)) :
  KSPS.sobolevNorm N (toSobolevCN N x) ^ 2 ≤
    (2 : ℝ) ^ N * ‖x‖ ^ 2 := by
  rw [supN_sobolevNorm_sq, ← supN_fibre_sum N x, mul_add]
  exact add_le_add (supN_component_norm_sq N x true) (supN_component_norm_sq N x false)

theorem sobolevNorm_toSobolevCN_le
    (N : ℕ) (x : PairScale (N : ℝ)) :
  KSPS.sobolevNorm N (toSobolevCN N x) ≤
    (2 : ℝ) ^ N * ‖x‖ := by
  have h := sobolevNorm_toSobolevCN_sq_le N x
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have h2 : (2 : ℝ) ^ N * ‖x‖ ^ 2 ≤ ((2 : ℝ) ^ N * ‖x‖) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hnn : 0 ≤ KSPS.sobolevNorm N (toSobolevCN N x) := Real.sqrt_nonneg _
  have hr : 0 ≤ (2 : ℝ) ^ N * ‖x‖ := by positivity
  exact (pow_le_pow_iff_left₀ hnn hr (by norm_num : (2 : ℕ) ≠ 0)).1 (h.trans h2)

theorem supN_component_add (N : ℕ) (x y : PairScale (N : ℝ)) (b : Bool) :
    (physicalSobolevFourierEquiv38 (N : ℝ)).symm
        (carrierMk38 (N : ℝ) (fun n : ℤ => -rawCoefficient (N : ℝ) (x + y) b (-n))
          (rawCoefficient_reflected_mem N (x + y) b)) =
      (physicalSobolevFourierEquiv38 (N : ℝ)).symm
          (carrierMk38 (N : ℝ) (fun n : ℤ => -rawCoefficient (N : ℝ) x b (-n))
            (rawCoefficient_reflected_mem N x b)) +
        (physicalSobolevFourierEquiv38 (N : ℝ)).symm
          (carrierMk38 (N : ℝ) (fun n : ℤ => -rawCoefficient (N : ℝ) y b (-n))
            (rawCoefficient_reflected_mem N y b)) := by
  rw [← map_add]
  congr 1
  apply carrierExt38
  funext n
  change -rawCoefficient (N : ℝ) (x + y) b (-n) =
    -rawCoefficient (N : ℝ) x b (-n) + -rawCoefficient (N : ℝ) y b (-n)
  unfold rawCoefficient
  rw [lp.coeFn_add, Pi.add_apply]
  ring

theorem supN_component_smul (N : ℕ) (a : ℝ) (x : PairScale (N : ℝ)) (b : Bool) :
    (physicalSobolevFourierEquiv38 (N : ℝ)).symm
        (carrierMk38 (N : ℝ) (fun n : ℤ => -rawCoefficient (N : ℝ) (a • x) b (-n))
          (rawCoefficient_reflected_mem N (a • x) b)) =
      a • (physicalSobolevFourierEquiv38 (N : ℝ)).symm
          (carrierMk38 (N : ℝ) (fun n : ℤ => -rawCoefficient (N : ℝ) x b (-n))
            (rawCoefficient_reflected_mem N x b)) := by
  rw [← map_smul]
  congr 1
  apply carrierExt38
  funext n
  change -rawCoefficient (N : ℝ) (a • x) b (-n) =
    ((a : ℝ) • carrierCoe38 (N : ℝ) (carrierMk38 (N : ℝ)
      (fun n : ℤ => -rawCoefficient (N : ℝ) x b (-n)) (rawCoefficient_reflected_mem N x b))) n
  rw [carrierCoe38_mk]
  unfold rawCoefficient
  rw [lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, Complex.real_smul]
  ring

theorem toSobolevCN_add
    (N : ℕ) (x y : PairScale (N : ℝ)) :
  toSobolevCN N (x + y) = toSobolevCN N x + toSobolevCN N y :=
  Prod.ext (supN_component_add N x y true) (supN_component_add N x y false)

theorem toSobolevCN_smul_real
    (N : ℕ) (a : ℝ) (x : PairScale (N : ℝ)) :
  toSobolevCN N (a • x) = a • toSobolevCN N x :=
  Prod.ext (supN_component_smul N a x true) (supN_component_smul N a x false)

theorem supN_norm_le_sobolevNorm (N : ℕ) (φ : KSPS.SobolevC N) :
    ‖φ‖ ≤ KSPS.sobolevNorm N φ := by
  unfold KSPS.sobolevNorm
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖φ.2‖]))
  · exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖φ.1‖]))

theorem continuous_toSobolevCN (N : ℕ) :
  Continuous (toSobolevCN N) := by
  let f : PairScale (N : ℝ) →+ KSPS.SobolevC N :=
    AddMonoidHom.mk' (toSobolevCN N) (toSobolevCN_add N)
  exact AddMonoidHomClass.continuous_of_bound f ((2 : ℝ) ^ N) (fun x =>
    (supN_norm_le_sobolevNorm N (toSobolevCN N x)).trans (sobolevNorm_toSobolevCN_le N x))

/-- The landed order-one worker bridge `toSobolevC` (KSN012Sup3) is the order-one instance. -/
theorem toSobolevC_eq_toSobolevCN_one (x : PairScale 1) :
    toSobolevC x = toSobolevCN 1 x := by
  refine Prod.ext ?_ ?_
  · change (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x true) = _
    congr 1
    apply carrierExt38
    funext n
    change sup3_componentSeq x true n = -rawCoefficient ((1 : ℕ) : ℝ) x true (-n)
    rw [sup3_componentSeq_apply, Nat.cast_one]
  · change (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm (sup3_componentCarrier x false) = _
    congr 1
    apply carrierExt38
    funext n
    change sup3_componentSeq x false n = -rawCoefficient ((1 : ℕ) : ℝ) x false (-n)
    rw [sup3_componentSeq_apply, Nat.cast_one]

end
end NlsGge.ThirdConsultation.KSN
