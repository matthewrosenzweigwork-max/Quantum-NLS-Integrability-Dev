import Mathlib
import NlsGge.Birkhoff.W12Tilt38g

                                                                                                            
                                                                                                           
                                                                                                      
                              
                                                                                                                      
                                                                                                                  
                                                                                              
                           
                                                                                                        
                                                                                                        
                                                                                                                 
                                                                                                         
set_option autoImplicit false
open MeasureTheory Filter Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.T026X
noncomputable section

variable {lower upper : ℝ}

theorem tilt_param (c : BoundedCoefficients lower upper) :
    0 < lower / (2 * upper) ∧ lower / (2 * upper) * upper < lower := by
  have hl : 0 < lower := c.property.1
  have hu : 0 < upper := lt_of_lt_of_le hl c.property.2.1
  refine ⟨by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- Uniform vanishing tails of the B-weight gap integrals along a convergent sequence in E_s
    (conditional on B, O as parameters). -/
theorem bGap_uniform_tail (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs' : s < 3 / 4)
    (u : ℕ → ECarrier38 c s) (hu : ∃ v, Tendsto u atTop (𝓝 v)) :
    (∀ N : ℕ, Summable (fun n : ℤ => gapIntegral38 (bCoef38 c.val) (physOfE38 c s (u N)) n)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N : ℕ,
        |∑' n : ℤ, if K < n.natAbs then gapIntegral38 (bCoef38 c.val) (physOfE38 c s (u N)) n else 0|
          ≤ ε := by
  obtain ⟨v, hv⟩ := hu
  have hs : s ≤ 3 / 4 := hs'.le
  -- bounds along the sequence
  have hW : Tendsto (fun N => ‖B.weightedHomeoE38 O c s (u N)‖) atTop
      (𝓝 ‖B.weightedHomeoE38 O c s v‖) :=
    (((B.weightedHomeoE38 O c s).continuous.tendsto v).comp hv).norm
  have hI : Tendsto (fun N => ‖iotaE38 c s (u N)‖) atTop (𝓝 ‖iotaE38 c s v‖) :=
    (((continuous_iotaE38 c s).tendsto v).comp hv).norm
  obtain ⟨M0, hM0⟩ := hW.bddAbove_range
  obtain ⟨I0, hI0⟩ := hI.bddAbove_range
  set M : ℝ := max M0 0 with hMdef
  have hM : ∀ N, ‖B.weightedHomeoE38 O c s (u N)‖ ≤ M :=
    fun N => (hM0 ⟨N, rfl⟩).trans (le_max_left _ _)
  have hM0' : 0 ≤ M := le_max_right _ _
  set Bd : ℝ := max 1 I0 with hBddef
  have hBd : ∀ N, ‖iotaE38 c s (u N)‖ ≤ Bd := fun N => (hI0 ⟨N, rfl⟩).trans (le_max_right _ _)
  -- gapwise domination of the B-weight gap integrals
  obtain ⟨hδ0, hδ⟩ := tilt_param c
  obtain ⟨C, hC, hdom⟩ := B.EB_gap_dominated_38 c hδ0 hδ Bd (le_max_left _ _)
  have hf : ∀ N n, gapIntegral38 (bCoef38 c.val) (physOfE38 c s (u N)) n ≤
      C * (tailWeight38 c.val n * ‖eCoe38 c s (B.weightedHomeoE38 O c s (u N)) n‖ ^ 2) := by
    intro N n
    have hsob := sobolev_physOfE38 c s 1 (u N)
    have hn : ‖physicalSobolevL2 1 (physOfE38 c s (u N)) hsob‖ ≤ Bd := by
      rw [norm_physicalSobolevL2_physOfE38]; exact hBd N
    have := hdom (physOfE38 c s (u N)) hsob hn n
    rwa [B.Φ_physOfE38 c s (u N), ← B.eCoe_weightedHomeoE38 c s O (u N)] at this
  have hnn : ∀ N n, 0 ≤ gapIntegral38 (bCoef38 c.val) (physOfE38 c s (u N)) n :=
    fun N n => gapIntegral38_bCoef_nonneg c _ n
  have hpt : ∀ N, ∀ t : ℝ, 0 < t → ∀ n : ℤ, t ≤ japaneseBracket n →
      gapIntegral38 (bCoef38 c.val) (physOfE38 c s (u N)) n ≤
        C * (t ^ (2 * s - 3 / 2) * (fullModeWeight c s n *
          ‖eCoe38 c s (B.weightedHomeoE38 O c s (u N)) n‖ ^ 2)) := by
    intro N t ht n htn
    exact (hf N n).trans (mul_le_mul_of_nonneg_left (tailWeight_mul_le38 c s hs t ht n htn _) hC.le)
  refine ⟨fun N => ?_, fun ε hε => ?_⟩
  · -- summability
    have hsum := hasSum_norm_sq_eCarrier38 c s (B.weightedHomeoE38 O c s (u N))
    refine Summable.of_nonneg_of_le (hnn N) (fun n => hpt N 1 one_pos n (japaneseBracket_one_le n))
      ((hsum.summable.mul_left (1 ^ (2 * s - 3 / 2))).mul_left C)
  · -- one K for all N
    have hlim := tendsto_japaneseBracket_rpow38 (2 * s - 3 / 2) (by linarith)
    have h2 : Tendsto (fun K : ℕ => C * (japaneseBracket (K : ℤ) ^ (2 * s - 3 / 2) * M ^ 2))
        atTop (𝓝 0) := by
      simpa using (hlim.mul_const (M ^ 2)).const_mul C
    obtain ⟨K, hK⟩ := (h2.eventually (gt_mem_nhds hε)).exists
    refine ⟨K, fun N => ?_⟩
    set zx := B.weightedHomeoE38 O c s (u N) with hzx
    have hsum := hasSum_norm_sq_eCarrier38 c s zx
    have hKpos := japaneseBracket_pos (K : ℤ)
    have hbound : ‖∑' n : ℤ, if K < n.natAbs then
        gapIntegral38 (bCoef38 c.val) (physOfE38 c s (u N)) n else 0‖ ≤
        C * (japaneseBracket (K : ℤ) ^ (2 * s - 3 / 2) * ‖zx‖ ^ 2) := by
      refine tsum_of_norm_bounded
        (g := fun n => C * (japaneseBracket (K : ℤ) ^ (2 * s - 3 / 2) *
          (fullModeWeight c s n * ‖eCoe38 c s zx n‖ ^ 2)))
        ((hsum.mul_left _).mul_left _) (fun n => ?_)
      by_cases hKn : K < n.natAbs
      · rw [if_pos hKn, Real.norm_eq_abs, abs_of_nonneg (hnn N n)]
        have hmem : n ∉ Finset.Icc (-(K : ℤ)) K := by
          rw [Finset.mem_Icc]
          omega
        exact hpt N _ hKpos n (japaneseBracket_ge_of_not_mem_Icc38 K n hmem)
      · rw [if_neg hKn, norm_zero]
        exact mul_nonneg hC.le (mul_nonneg (Real.rpow_nonneg hKpos.le _)
          (mul_nonneg (fullModeWeight_pos c s n).le (sq_nonneg _)))
    rw [← Real.norm_eq_abs]
    refine hbound.trans (le_trans ?_ hK.le)
    have hz : ‖zx‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM N) 2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg hKpos.le _)) hC.le

end
end NlsGge.ThirdConsultation.T026X
