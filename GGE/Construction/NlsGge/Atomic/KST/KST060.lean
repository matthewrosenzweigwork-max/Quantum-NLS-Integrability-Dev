import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.KST.KST044
import NlsGge.Atomic.KST.KST046
import NlsGge.Atomic.KST.KST054
import NlsGge.Atomic.KST.KST058
import NlsGge.Atomic.KST.KST059
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST046Host

                                                                                                        
                                                                                                    
                                                                                                              
                                                                                                     
                                                
                                                                                                                   
                                                                    
                                                                                                                              
                                                                                                     
                                                                                                                     
                                                                                                                               
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST001 NlsGge.Atomic.KST002 NlsGge.Pilot NlsGge.GK38
open NlsGge.Atomic.KST059
open NlsGge.Atomic.KST043 (KSTSubexponentialWeight)

namespace NlsGge.ThirdConsultation.KST

namespace KST060S

theorem weightedNormSq₂_mono (W₁ W₂ : ℤ → ℝ) (h0 : ∀ k, 0 ≤ W₁ k) (h : ∀ k, W₁ k ≤ W₂ k)
    (φ : PeriodicPair) : weightedNormSq₂ W₁ φ ≤ weightedNormSq₂ W₂ φ := by
  unfold weightedNormSq₂
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  unfold weightedPairMode
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (h0 k) (h k) 2)) le_rfl

theorem weightedNormSq₂_const_mul (C : ℝ) (W : ℤ → ℝ) (φ : PeriodicPair) :
    weightedNormSq₂ (fun k => C * W k) φ = ENNReal.ofReal (C^2) * weightedNormSq₂ W φ := by
  unfold weightedNormSq₂
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  unfold weightedPairMode
  rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

theorem evenWeight_of_subexp (ω : ℤ → ℝ) (hv : KSTSubexponentialWeight ω) : EvenWeight ω :=
  ⟨NlsGge.Atomic.KST044.subexponentialWeight_ge_one ω hv, hv.2.1⟩

theorem secondary_of_subexp (ω : ℤ → ℝ) (hv : KSTSubexponentialWeight ω) : SecondaryWeight ω := by
  have hone := NlsGge.Atomic.KST044.subexponentialWeight_ge_one ω hv
  have hveven : ∀ k : ℤ, ω (-k) = ω k := hv.2.1
  have hvnat : ∀ k : ℤ, ω k = ω (k.natAbs : ℤ) := by
    intro k
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact hveven _
  refine ⟨⟨hone, hveven, fun j k hjk => ?_⟩, hv.2.2.2.1⟩
  rw [hvnat j, hvnat k]
  exact hv.2.2.1 hjk

/-- Upper bound for a submultiplicative radial weight by powers of its value at `1`. -/
theorem le_pow_one (ω : ℤ → ℝ) (hω : SecondaryWeight ω) (n : ℕ) :
    ω (n : ℤ) ≤ ω 1 ^ (n + 1) := by
  have hone := hω.1.1
  have hmono := hω.1.2.2
  have hsub := hω.2
  induction n with
  | zero =>
      simpa using hmono 0 1 (by simp)
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      have h1pos : 0 < ω 1 := lt_of_lt_of_le zero_lt_one (hone 1)
      calc ω ((n : ℤ) + 1) ≤ ω (n : ℤ) * ω 1 := hsub _ _
        _ ≤ ω 1 ^ (n + 1) * ω 1 := mul_le_mul_of_nonneg_right ih h1pos.le
        _ = ω 1 ^ (n + 1 + 1) := by ring

theorem rpow_le (ω : ℤ → ℝ) (hω : SecondaryWeight ω) (δ ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ * Real.log (ω 1) ≤ δ) (k : ℤ) :
    ω k ^ ρ ≤ Real.exp δ * expWeight δ k := by
  have hone := hω.1.1
  have hev := hω.1.2.1
  have hωk : ω k = ω (k.natAbs : ℤ) := by
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact hev _
  have hle := le_pow_one ω hω k.natAbs
  have hpos : 0 < ω k := lt_of_lt_of_le zero_lt_one (hone k)
  have hlog : Real.log (ω k) ≤ ((k.natAbs : ℝ) + 1) * Real.log (ω 1) := by
    rw [hωk]
    calc Real.log (ω (k.natAbs : ℤ)) ≤ Real.log (ω 1 ^ (k.natAbs + 1)) :=
          Real.log_le_log (by rw [← hωk]; exact hpos) hle
      _ = ((k.natAbs : ℝ) + 1) * Real.log (ω 1) := by rw [Real.log_pow]; push_cast; ring
  rw [Real.rpow_def_of_pos hpos]
  unfold expWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : Real.log (ω k) * ρ ≤ ((k.natAbs : ℝ) + 1) * Real.log (ω 1) * ρ :=
    mul_le_mul_of_nonneg_right hlog hρ0
  have h2 : ((k.natAbs : ℝ) + 1) * (ρ * Real.log (ω 1)) ≤ ((k.natAbs : ℝ) + 1) * δ :=
    mul_le_mul_of_nonneg_left hρ (by positivity)
  nlinarith [h1, h2]

/-- The KST-059 producer repackaged with the KST-054 hypotheses. -/
theorem common_weight (φ : PotPair) (ω : ℤ → ℝ) (hE : EvenWeight ω)
    (hγ : weightedGapEnergy ω (actualGapSequence φ) < ⊤) :
    ∃ (w : ℤ → ℝ) (Cw : ℝ), SlowWeight w Cw ∧
      Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop ∧
      weightedNormSq₂ w φ < ⊤ ∧
      weightedGapEnergy (productWeight w ω) (actualGapSequence φ) < ⊤ := by
  obtain ⟨c, h⟩ := exists_common_auxiliary_weight_actual φ ω hE hγ
  exact ⟨_, 2, h.1.1, h.1.2.2.1, h.2.1, h.2.2⟩

end KST060S

theorem kst060 (φ : PotPair) (ε : ℝ) (hreal : RealForm ε φ)
    (ω : ℤ → ℝ) (hγ : weightedGapEnergy ω (actualGapSequence φ) < ⊤) :
  (KSTSubexponentialWeight ω → weightedNormSq₂ ω φ < ⊤) ∧
  (∀ χ : ℝ, ExponentialWeight ω χ →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      weightedNormSq₂ (fun k => (ω k)^ρ) φ < ⊤) := by
  refine ⟨fun hsub => ?_, fun χ hχ => ?_⟩
  · have hEven := KST060S.evenWeight_of_subexp ω hsub
    have hSec := KST060S.secondary_of_subexp ω hsub
    obtain ⟨w, Cw, hw, hun, hwφ, hgap⟩ := KST060S.common_weight φ ω hEven hγ
    have h := (kst054 w ω Cw hw hun hSec φ hwφ ε hreal hgap).1 hsub
    refine lt_of_le_of_lt (KST060S.weightedNormSq₂_mono ω (productWeight w ω)
      (fun k => (lt_of_lt_of_le zero_lt_one (hEven.one_le k)).le) (fun k => ?_) φ) h
    exact le_mul_of_one_le_left (lt_of_lt_of_le zero_lt_one (hEven.one_le k)).le (hw.one_le k)
  · have hSec : SecondaryWeight ω := ⟨hχ.1, hχ.2.1⟩
    have hEven : EvenWeight ω := ⟨hχ.1.1, hχ.1.2.1⟩
    obtain ⟨w, Cw, hw, hun, hwφ, hgap⟩ := KST060S.common_weight φ ω hEven hγ
    obtain ⟨δ, hδ0, -, hfin⟩ := (kst054 w ω Cw hw hun hSec φ hwφ ε hreal hgap).2 χ hχ
    have h1 : 1 < ω 1 := by
      have h := KST046W.exp_le_nat ω χ hχ 1
      simp only [Nat.cast_one, mul_one] at h
      exact lt_of_lt_of_le (Real.one_lt_exp_iff.2 hχ.2.2.1) h
    have hL : 0 < Real.log (ω 1) := Real.log_pos h1
    have hρ0 : 0 < min 1 (δ / Real.log (ω 1)) := lt_min one_pos (div_pos hδ0 hL)
    have hρL : min 1 (δ / Real.log (ω 1)) * Real.log (ω 1) ≤ δ :=
      calc min 1 (δ / Real.log (ω 1)) * Real.log (ω 1)
          ≤ (δ / Real.log (ω 1)) * Real.log (ω 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le
        _ = δ := div_mul_cancel₀ _ hL.ne'
    refine ⟨min 1 (δ / Real.log (ω 1)), hρ0, min_le_left _ _, ?_⟩
    have hbound := KST060S.weightedNormSq₂_mono
      (fun k => (ω k) ^ (min 1 (δ / Real.log (ω 1))))
      (fun k => Real.exp δ * productWeight w (expWeight δ) k)
      (fun k => Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one (hEven.one_le k)).le _)
      (fun k => by
        refine (KST060S.rpow_le ω hSec δ _ hρ0.le hρL k).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos δ).le
        exact le_mul_of_one_le_left (Real.exp_pos _).le (hw.one_le k)) φ
    rw [KST060S.weightedNormSq₂_const_mul] at hbound
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

end NlsGge.ThirdConsultation.KST
end
