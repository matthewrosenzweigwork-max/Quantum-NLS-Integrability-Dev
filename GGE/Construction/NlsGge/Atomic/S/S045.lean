import Mathlib
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                      
                                                                                                                       
                                                                                                                          
                                                                                                             
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open Matrix
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
open NlsGge.Measure
namespace NlsGge.ThirdConsultation.S

theorem relativeBallIntegral_lowCutoff {lo up : ℝ} (c : BoundedCoefficients lo up)
    (M N : ℕ) (hNM : N ≤ M) (R : ℝ) (hR : 0 ≤ R) :
    relativeBallIntegralV6 c N R ≤
      ∏ n ∈ normalizerModes N, R ^ 2 * fullWeightRate c.val n := by
  obtain ⟨hl, -, hb, hu⟩ := boundedCoefficients_bounds38 c
  have hapos : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lo up c.val hl hb hu n
  -- the signed mode set is the image of the Fin enumeration used by freeNormalizer38
  have hmodes : ∀ g : ℤ → ℝ, ∏ n ∈ normalizerModes N, g n =
      ∏ i : Fin (2 * N + 1), g (modeIndex N i) := by
    intro g
    have himg : Finset.univ.image (modeIndex N) = normalizerModes N := by
      ext n
      simp only [Finset.mem_image, Finset.mem_univ, true_and, normalizerModes, Finset.mem_Icc]
      constructor
      · rintro ⟨i, rfl⟩
        have := i.isLt
        unfold modeIndex
        constructor <;> omega
      · intro h
        obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n + (N : ℤ) by omega)
        refine ⟨⟨k, by omega⟩, ?_⟩
        unfold modeIndex
        dsimp only
        omega
    rw [← himg, Finset.prod_image]
    intro i _ j _ h
    exact modeIndex_injective N h
  have hF : 0 < freeNormalizer38 c N := by
    unfold freeNormalizer38
    exact Finset.prod_pos fun i _ => div_pos Real.pi_pos (hapos _)
  have hid : ∏ _i : Fin (2 * N + 1), (Real.pi * R ^ 2) =
      freeNormalizer38 c N *
        ∏ i : Fin (2 * N + 1), R ^ 2 * fullWeightRate c.val (modeIndex N i) := by
    unfold freeNormalizer38
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h := (hapos (modeIndex N i)).ne'
    field_simp
    try ring
  have hI : ∫ z in schurH1Ball N R, Real.exp (-fullEnergy38 c N z) ∂planeVolume N ≤
      ∏ _i : Fin (2 * N + 1), (Real.pi * R ^ 2) := by
    rcases hR.eq_or_lt with h0 | hpos
    · have hempty : schurH1Ball N R = ∅ := by
        ext z
        simp only [schurH1Ball, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        rw [← h0]
        exact norm_nonneg _
      rw [hempty, MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure, ← h0]
      exact Finset.prod_nonneg fun i _ => by positivity
    · have hB : MeasurableSet (schurH1Ball N R) :=
        measurableSet_lt (continuous_planeH1Norm38 N).measurable measurable_const
      have hBR : ∀ z ∈ schurH1Ball N R, ∀ i : Fin (2 * N + 1), ‖z i‖ < R := by
        intro z hz i
        have hz' : ‖planeH1Embedding38 N z‖ < R := hz
        have hsq := planeH1Embedding38_norm_sq N z
        have h1 : (1 + (modeIndex N i : ℝ) ^ 2) * ‖z i‖ ^ 2 ≤
            ∑ j : Fin (2 * N + 1), (1 + (modeIndex N j : ℝ) ^ 2) * ‖z j‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun j : Fin (2 * N + 1) => (1 + (modeIndex N j : ℝ) ^ 2) * ‖z j‖ ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)
        have h2 : ‖z i‖ ^ 2 ≤ (1 + (modeIndex N i : ℝ) ^ 2) * ‖z i‖ ^ 2 := by
          nlinarith [sq_nonneg (modeIndex N i : ℝ), sq_nonneg ‖z i‖]
        have h3 : ‖planeH1Embedding38 N z‖ ^ 2 < R ^ 2 := by
          have := norm_nonneg (planeH1Embedding38 N z)
          nlinarith
        have h4 : ‖z i‖ ^ 2 < R ^ 2 := by linarith
        nlinarith [norm_nonneg (z i)]
      have hvol := ballVolumeBound38 N (schurH1Ball N R) hB (fun z => fullEnergy38 c N z)
        (fun z => fullEnergy38_nonneg c N z) R hpos hBR
      have hmeas : AEStronglyMeasurable (fun z => Real.exp (-fullEnergy38 c N z))
          ((planeVolume N).restrict (schurH1Ball N R)) :=
        ((continuous_fullEnergy38 c N).neg.rexp).aestronglyMeasurable
      have hnn : 0 ≤ᵐ[(planeVolume N).restrict (schurH1Ball N R)]
          (fun z => Real.exp (-fullEnergy38 c N z)) :=
        Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
      have hint := integral_eq_lintegral_of_nonneg_ae hnn hmeas
      have hpi_nonneg : 0 ≤ ∏ _i : Fin (2 * N + 1), (Real.pi * R ^ 2) :=
        Finset.prod_nonneg fun _ _ => by positivity
      have hofReal : ∏ _i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi * R ^ 2) =
          ENNReal.ofReal (∏ _i : Fin (2 * N + 1), (Real.pi * R ^ 2)) :=
        (ENNReal.ofReal_prod_of_nonneg fun _ _ => by positivity).symm
      rw [hint]
      calc (∫⁻ z in schurH1Ball N R, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N).toReal
          ≤ (ENNReal.ofReal (∏ _i : Fin (2 * N + 1), (Real.pi * R ^ 2))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvol.trans_eq hofReal)
        _ = ∏ _i : Fin (2 * N + 1), (Real.pi * R ^ 2) := ENNReal.toReal_ofReal hpi_nonneg
  unfold relativeBallIntegralV6
  rw [div_le_iff₀ hF, hmodes]
  exact (hI.trans_eq hid).trans_eq (mul_comm _ _)

end NlsGge.ThirdConsultation.S
