import NlsGge.Measure.CountableReconstruction
import NlsGge.Measure.CountableSupport
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Atomic.R.R023

                                                                                                      
                                                                                                                               
         
                                                                                                                                   
                                                                                                                                        
                                                                                                                                 
                                                                                                                                               
                                                               
                                                                                                      
set_option autoImplicit false
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.R
noncomputable section

-- coordinateGaussian is hosted by NlsGge.Atomic.R.R023 (Pro shared Ramer block; identical body). De-duplicated 2026-10-30.

theorem coordinate_ae_summable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Summable (fun n : ℤ => NlsGge.Measure.fullWeightRate c.val n *
        Real.rpow (japaneseBracket n) (-2 * s) * ‖x n‖ ^ 2) := by
  obtain ⟨hlow, _, hb⟩ := c.2
  have hq : ∀ n : ℤ, 0 < NlsGge.Measure.fullWeightRate c.val n := fun n =>
    NlsGge.Measure.fullWeightRate_pos lower upper c.val hlow (fun j => (hb j).1) (fun j => (hb j).2) n
  have hw : ∀ n : ℤ, 0 ≤ NlsGge.Measure.fullWeightRate c.val n * Real.rpow (japaneseBracket n) (-2 * s) :=
    fun n => mul_nonneg (hq n).le
      (Real.rpow_nonneg (by unfold japaneseBracket; exact Real.sqrt_nonneg _) _)
  have hdiv : ∀ n : ℤ, NlsGge.Measure.fullWeightRate c.val n * Real.rpow (japaneseBracket n) (-2 * s) /
      NlsGge.Measure.fullWeightRate c.val n = Real.rpow (japaneseBracket n) (-(2 * s)) := fun n => by
    rw [mul_div_cancel_left₀ _ (hq n).ne', show (-2 : ℝ) * s = -(2 * s) by ring]
  have hsum : Summable (fun n : ℤ => NlsGge.Measure.fullWeightRate c.val n *
      Real.rpow (japaneseBracket n) (-2 * s) / NlsGge.Measure.fullWeightRate c.val n) := by
    simp_rw [hdiv]
    exact NlsGge.Measure.summable_japaneseBracket_rpow_neg (2 * s) (by linarith)
  exact NlsGge.Measure.ae_sequenceSummable (NlsGge.Measure.fullWeightRate c.val)
    (fun n : ℤ => NlsGge.Measure.fullWeightRate c.val n * Real.rpow (japaneseBracket n) (-2 * s))
    hq hw hsum

theorem ae_mem_fullWeightedHilbert
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ x : ℤ → ℂ ∂coordinateGaussian c,
      Summable (fun n : ℤ =>
        NlsGge.Measure.fullWeightRate c.val n *
          Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) *
          ‖x n‖ ^ 2) :=
  coordinate_ae_summable c s hs

theorem weighted_coordinate_energy_expectation
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (∫⁻ x : ℤ → ℂ,
      (∑' n : ℤ,
        ENNReal.ofReal
          (NlsGge.Measure.fullWeightRate c.val n *
            Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) *
            ‖x n‖ ^ 2)) ∂coordinateGaussian c) =
      ∑' n : ℤ,
        ENNReal.ofReal
          (Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) := by
  obtain ⟨hlow, _, hb⟩ := c.2
  have hq : ∀ n : ℤ, 0 < NlsGge.Measure.fullWeightRate c.val n := fun n =>
    NlsGge.Measure.fullWeightRate_pos lower upper c.val hlow (fun j => (hb j).1) (fun j => (hb j).2) n
  have hw : ∀ n : ℤ, 0 ≤ NlsGge.Measure.fullWeightRate c.val n *
      Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := fun n =>
    mul_nonneg (hq n).le
      (Real.rpow_nonneg (by unfold NlsGge.Pilot.japaneseBracket; exact Real.sqrt_nonneg _) _)
  have h := NlsGge.Measure.lintegral_sequenceEnergy (NlsGge.Measure.fullWeightRate c.val)
    (fun n : ℤ => NlsGge.Measure.fullWeightRate c.val n *
      Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) hq hw
  have hdiv : ∀ n : ℤ, NlsGge.Measure.fullWeightRate c.val n *
      Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) / NlsGge.Measure.fullWeightRate c.val n =
      Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := fun n =>
    mul_div_cancel_left₀ _ (hq n).ne'
  simp only [hdiv] at h
  exact h

theorem weighted_coordinate_energy_expectation_finite
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (∑' n : ℤ,
      ENNReal.ofReal
        (Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s))) < ⊤ := by
  have hfun : (fun n : ℤ => Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) =
      (fun n : ℤ => Real.rpow (NlsGge.Pilot.japaneseBracket n) (-(2 * s))) := by
    funext n
    rw [show (-2 : ℝ) * s = -(2 * s) by ring]
  have hsum : Summable (fun n : ℤ => Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) := by
    rw [hfun]
    exact NlsGge.Measure.summable_japaneseBracket_rpow_neg (2 * s) (by linarith)
  exact lt_top_iff_ne_top.2 hsum.tsum_ofReal_ne_top

theorem ae_coordinate_realization_identity
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ x : ℤ → ℂ ∂coordinateGaussian c,
      NlsGge.Ramer.coordE c s
        (NlsGge.Measure.fullWeightedSequenceRealization c s x) = x := by
  filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with x hx
  funext n
  exact hx n

end
end NlsGge.ThirdConsultation.R
