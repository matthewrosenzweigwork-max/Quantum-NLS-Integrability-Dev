import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.DM.DM047
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST045Support
import NlsGge.ThirdConsultation.KST.KST046Host

                                                                                                        
                                                                                                    
                                                                                                              
                                                                                                                  
                                                                             
                                                       
                                                                                                                 
                                                                                
                                                                                               
                                                                                                                      
                                                                                                            
                                                                                  
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST001 NlsGge.Atomic.KST002 NlsGge.Pilot
open NlsGge.Atomic.KST043 (KSTLogRatio)
open NlsGge.Atomic.DM046 (SubmultiplicativeWeight)

namespace NlsGge.ThirdConsultation.KST

namespace KST046W

theorem exp_le_nat (v : ℤ → ℝ) (χ : ℝ) (hv : ExponentialWeight v χ) (n : ℕ) :
    Real.exp (χ * (n : ℝ)) ≤ v (n : ℤ) := by
  obtain ⟨⟨hone, -, -⟩, hsub, -, hlim⟩ := hv
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simpa using hone 0
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hvn : 0 < v (n : ℤ) := lt_of_lt_of_le zero_lt_one (hone _)
    have hpow : ∀ m : ℕ, v ((((m + 1) * n : ℕ)) : ℤ) ≤ v (n : ℤ) ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          have hcast : ((((m + 1 + 1) * n : ℕ)) : ℤ) = ((((m + 1) * n : ℕ)) : ℤ) + (n : ℤ) := by
            push_cast; ring
          rw [hcast]
          calc v (((((m + 1) * n : ℕ)) : ℤ) + (n : ℤ))
              ≤ v ((((m + 1) * n : ℕ)) : ℤ) * v (n : ℤ) := hsub _ _
            _ ≤ v (n : ℤ) ^ (m + 1) * v (n : ℤ) :=
                mul_le_mul_of_nonneg_right ih hvn.le
            _ = v (n : ℤ) ^ (m + 1 + 1) := by ring
    let p : ℕ → ℕ+ := fun m => ⟨(m + 1) * n, Nat.mul_pos (Nat.succ_pos m) hn⟩
    have hratio : ∀ m : ℕ, KSTLogRatio v (p m) ≤ Real.log (v (n : ℤ)) / (n : ℝ) := by
      intro m
      have hmn : (0 : ℝ) < (((m + 1) * n : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.succ_pos m) hn
      have hvpos : 0 < v ((((m + 1) * n : ℕ)) : ℤ) := lt_of_lt_of_le zero_lt_one (hone _)
      have h1 : Real.log (v ((((m + 1) * n : ℕ)) : ℤ)) ≤ ((m : ℝ) + 1) * Real.log (v (n : ℤ)) := by
        calc Real.log (v ((((m + 1) * n : ℕ)) : ℤ))
            ≤ Real.log (v (n : ℤ) ^ (m + 1)) := Real.log_le_log hvpos (hpow m)
          _ = ((m : ℝ) + 1) * Real.log (v (n : ℤ)) := by
              rw [Real.log_pow]; push_cast; ring
      show Real.log (v ((((m + 1) * n : ℕ)) : ℤ)) / (((m + 1) * n : ℕ) : ℝ) ≤ _
      rw [div_le_div_iff₀ hmn hnR]
      have : (((m + 1) * n : ℕ) : ℝ) = ((m : ℝ) + 1) * (n : ℝ) := by push_cast; ring
      rw [this]
      nlinarith [h1, hnR]
    have htend : Tendsto p atTop atTop := by
      refine Filter.tendsto_atTop_atTop.2 (fun b => ⟨(b : ℕ), fun a ha => ?_⟩)
      rw [← PNat.coe_le_coe]
      show (b : ℕ) ≤ (a + 1) * n
      calc (b : ℕ) ≤ a := ha
        _ ≤ (a + 1) * n := by nlinarith
    have hlim' : Tendsto (fun m : ℕ => KSTLogRatio v (p m)) atTop (nhds χ) := hlim.comp htend
    have hχle : χ ≤ Real.log (v (n : ℤ)) / (n : ℝ) := le_of_tendsto' hlim' hratio
    have h2 : χ * (n : ℝ) ≤ Real.log (v (n : ℤ)) := (le_div_iff₀ hnR).1 hχle
    calc Real.exp (χ * (n : ℝ)) ≤ Real.exp (Real.log (v (n : ℤ))) := Real.exp_le_exp.2 h2
      _ = v (n : ℤ) := Real.exp_log hvn

theorem exp_le_of_exponentialWeight (v : ℤ → ℝ) (χ : ℝ) (hv : ExponentialWeight v χ) (k : ℤ) :
    expWeight χ k ≤ v k := by
  have hveven : ∀ j : ℤ, v (-j) = v j := hv.1.2.1
  have hvnat : v k = v (k.natAbs : ℤ) := by
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact hveven _
  rw [hvnat]
  exact exp_le_nat v χ hv k.natAbs

theorem cutoff_eq_exp (v : ℤ → ℝ) (χ : ℝ) (hv : ExponentialWeight v χ) (δ : ℝ)
    (hδ : 0 < δ) (hδχ : δ < χ) (k : ℤ) :
    NlsGge.Atomic.DM047.secondaryCutoff v δ k = expWeight δ k := by
  unfold NlsGge.Atomic.DM047.secondaryCutoff
  refine min_eq_left ?_
  refine le_trans ?_ (exp_le_of_exponentialWeight v χ hv k)
  unfold expWeight
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hδχ.le (Nat.cast_nonneg _))

theorem secondary_expWeight (δ : ℝ) (hδ : 0 < δ) : SecondaryWeight (expWeight δ) := by
  refine ⟨⟨fun k => ?_, fun k => ?_, fun j k hjk => ?_⟩, fun k l => ?_⟩
  · unfold expWeight
    exact Real.one_le_exp (mul_nonneg hδ.le (Nat.cast_nonneg _))
  · unfold expWeight
    rw [Int.natAbs_neg]
  · unfold expWeight
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hjk) hδ.le)
  · unfold expWeight
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Int.natAbs_add_le k l) hδ.le

end KST046W

theorem kst046 (w v : ℤ → ℝ) (Cw M χ : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (hv : ExponentialWeight v χ) (φ : Potential)
    (hφ : weightedNormSq₂ w (periodicPair φ) < ⊤)
    (hmargin : 8*Real.sqrt (weightedNormSq₂ w (periodicPair φ)).toReal ≤ M)
    (hF : rawEnergy (productWeight w v)
      (adaptedCoefficients (adaptedThreshold w M) φ) < ⊤) :
  (∀ k : ℤ, expWeight χ k ≤ v k) ∧
  (∀ δ : ℝ, 0 < δ → δ < χ → ∀ k : ℤ,
    NlsGge.Atomic.DM047.secondaryCutoff v δ k = expWeight δ k) ∧
  ∃ δ : ℝ, 0 < δ ∧ δ < χ ∧
    rawEnergy (productWeight w (expWeight δ))
      (adaptedCoefficients (adaptedThreshold w M) φ) ≤ ENNReal.ofReal ((M/2)^2) ∧
    weightedNormSq₂ (productWeight w (expWeight δ)) (periodicPair φ) < ⊤ := by
  have hχ : 0 < χ := hv.2.2.1
  have hv1 : ∀ k, 1 ≤ v k := hv.1.1
  refine ⟨KST046W.exp_le_of_exponentialWeight v χ hv,
    fun δ hδ hδχ k => KST046W.cutoff_eq_exp v χ hv δ hδ hδχ k, ?_⟩
  have hlim := KST045S.rawEnergy_cutoff_tendsto w v hv1
    (adaptedCoefficients (adaptedThreshold w M) φ) hF.ne
  have hlt := KST045S.rawEnergy_adapted_lt w Cw M hM hw hunbounded φ hφ hmargin
  have hev := hlim.eventually (gt_mem_nhds hlt)
  have hIoo : Set.Ioo (0 : ℝ) χ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hχ
  obtain ⟨δ, hδE, hδI⟩ := (hev.and (show ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
    ε ∈ Set.Ioo (0 : ℝ) χ from hIoo)).exists
  have hfun : NlsGge.Atomic.DM047.secondaryCutoff v δ = expWeight δ :=
    funext (KST046W.cutoff_eq_exp v χ hv δ hδI.1 hδI.2)
  rw [hfun] at hδE
  exact ⟨δ, hδI.1, hδI.2, hδE.le,
    KST045S.energy_of_inverse w Cw M hM hw hunbounded _ (KST046W.secondary_expWeight δ hδI.1)
      φ hφ hmargin hδE.le⟩

end NlsGge.ThirdConsultation.KST
end
