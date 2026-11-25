import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST031
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST035Support
import NlsGge.ThirdConsultation.KST.KST035Lift

                                                                                                        
                                                                                                    
                                                                                         
                                                                                                                  
                                                                                                                
                 
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

theorem kst035 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop) :
  (∃ N : ℕ, adaptedCutoffCondition w M N) ∧
  adaptedCutoffCondition w M (adaptedThreshold w M) ∧
  ∀ (v : ℤ → ℝ) (hv : SecondaryWeight v),
    let ω := productWeight w v
    let hω := productOneLe hw.one_le hv.1.1
    letI := weightFact ω hω
    ∀ x ∈ componentBall ω (2*M),
      weightedCoeffs ω (adaptedFourier ω hω (adaptedThreshold w M) x) =
        adaptedCoefficients (adaptedThreshold w M) (weightedPotential ω hω x) ∧
      ‖adaptedFourier ω hω (adaptedThreshold w M) x-x‖ ≤ M/16 := by
  have hC : 1 ≤ Cw := NlsGge.Atomic.KST.slowWeight_Cw_one_le hw
  have hC2 : 1 ≤ Cw ^ 2 := by nlinarith
  have hM0 : 0 < M := by linarith
  have hex : ∃ N : ℕ, adaptedCutoffCondition w M N := by
    set K : ℝ := 16 * M ^ 2 with hK
    have hK0 : 0 < K := by positivity
    set δ1 : ℝ := (M / 16) ^ 2 / 2 / (900 * Cw ^ 2 * (K + 1)) with hδ1
    set δ0 : ℝ := 1 / (60 * Cw ^ 2) with hδ0
    have hδ1pos : 0 < δ1 := by positivity
    have hδ0pos : 0 < δ0 := by positivity
    set δ : ℝ := min δ0 δ1 with hδ
    have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
    have hδ0le : δ0 ≤ 1 / 60 := by
      rw [hδ0]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hδ1' : δ ≤ 1 := (min_le_left _ _).trans (hδ0le.trans (by norm_num))
    have h1 : Tendsto (fun N : ℕ => K / w (N : ℤ) ^ 2) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop (by norm_num) |>.comp hunbounded)
    have h2 : Tendsto (fun N : ℕ => K / Real.sqrt (N : ℝ)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h3 : Tendsto (fun N : ℕ => K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
      simpa using h1.add h2
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h3.eventually (gt_mem_nhds hδpos))
    refine ⟨max N0 (max (diagonalThreshold w M) 1), ?_⟩
    set N := max N0 (max (diagonalThreshold w M) 1) with hNdef
    have hN0N : N0 ≤ N := le_max_left _ _
    have hNd : diagonalThreshold w M ≤ N := (le_max_left _ _).trans (le_max_right _ _)
    have hN1 : 1 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
    have hs : K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ) < δ := hN0 N hN0N
    have hs0 : 0 ≤ K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ) := by positivity
    have hsδ0 : K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ) ≤ δ0 :=
      hs.le.trans (min_le_left _ _)
    have hsδ1 : K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ) ≤ δ1 :=
      hs.le.trans (min_le_right _ _)
    have hs1 : Cw ^ 2 * (K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ)) ≤ 1 / 60 := by
      have : Cw ^ 2 * (K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ)) ≤ Cw ^ 2 * δ0 :=
        mul_le_mul_of_nonneg_left hsδ0 (sq_nonneg _)
      have e : Cw ^ 2 * δ0 = 1 / 60 := by rw [hδ0]; field_simp
      linarith
    have hs2 : 900 * Cw ^ 2 * (K + 1) *
        (K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ)) ^ 2 ≤ (M / 16) ^ 2 / 2 := by
      have hss : (K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ)) ^ 2 ≤ δ1 := by
        have h1' : K / w (N : ℤ) ^ 2 + K / Real.sqrt (N : ℝ) ≤ 1 := hs.le.trans hδ1'
        nlinarith [mul_nonneg hs0 (sub_nonneg.2 h1')]
      have hpos : 0 < 900 * Cw ^ 2 * (K + 1) := by positivity
      have h4 := mul_le_mul_of_nonneg_left hss hpos.le
      have e : 900 * Cw ^ 2 * (K + 1) * δ1 = (M / 16) ^ 2 / 2 := by
        rw [hδ1]; field_simp
      linarith
    refine ⟨hNd, fun v hv φ hφ => ?_⟩
    exact KST035S.rawEnergy_le w Cw M hM hw hunbounded v hv N hN1 hNd hs1 hs2 φ hφ
  have hcond : adaptedCutoffCondition w M (adaptedThreshold w M) := by
    unfold adaptedThreshold
    rw [dif_pos hex]
    exact Nat.find_spec hex
  refine ⟨hex, hcond, fun v hv => ?_⟩
  intro ω hω
  letI := weightFact ω hω
  intro x hx
  have hφx : weightedPotential ω hω x ∈ physicalComponentBall ω (2 * M) :=
    KST033S.wp_mem_ball ω hω x (2 * M) hx
  have hD := hcond.2 v hv _ hφx
  have hM16 : 0 ≤ M / 16 := by positivity
  exact KST035L.lift_spec ω hω x (adaptedThreshold w M) (M / 16) hD hM16

end NlsGge.ThirdConsultation.KST
end
