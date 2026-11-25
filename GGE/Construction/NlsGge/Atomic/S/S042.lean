import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurCanonicalAndGapLocal38V1
import NlsGge.Schur.ActualSchurBallFullEnergy38V1

                                                                                                          
                                                                                                
                                                                                                              
                                                                                                             
                                                                                                    
                                                                                                                    
                                                                                                                
                                                                                         
                                                                                              
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

/-- `rhoAt` is the production loss factor `actualSchurRho38` (same constant, every `n`). -/
theorem rhoAt_eq_actualSchurRho38 (C R : ℝ) (n : ℤ) : rhoAt C R n = actualSchurRho38 C R n := by
  unfold rhoAt actualSchurRho38
  rw [Real.rpow_neg (abs_nonneg _), sq_abs]
  congr 1

theorem fullEnergy_ge_highSchur (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (c : BoundedCoefficients lo up)
      (R : ℝ), 1 ≤ R → ∀ (M N : ℕ), A * R ^ 6 ≤ (M : ℝ) →
      ∀ z : FourierPlane N, z ∈ schurH1Ball N R →
      (∑ i : Fin (2 * N + 1),
        if (modeIndex N i).natAbs ≤ M then 0 else
          rhoAt C R (modeIndex N i) * fullWeightRate c.val (modeIndex N i) *
            ‖actualSchurQnCanonical38 (modeIndex N i)
              (schurRealPair (planeH1Embedding38 N z))‖ ^ 2) ≤ fullEnergy38 c N z := by
  obtain ⟨Kb, Cb, hKb, hCb, hgb⟩ := actualSchurGapEnergyLower38V1 lo up hl hlu
  obtain ⟨K2, hK2, hW2⟩ := fullEnergy38_ge_gapSum_window_uniform
  set T := actualSchurCenterThresholdConstant38 with hT
  refine ⟨Cb, |Kb| + |K2| + |T| + 1, hCb, by positivity, ?_⟩
  intro c R hR M N hM z hz
  obtain ⟨-, -, hb, hu⟩ := boundedCoefficients_bounds38 c
  have hz' : planeH1Norm38 N z < R := hz
  set w := planeH1Embedding38 N z with hw
  have hwR : ‖w‖ ≤ R := hz'.le
  have hw2 : ‖actualH1Conj38 w‖ ≤ R := by rw [actualH1Conj38_norm]; exact hwR
  have hR6 : (0 : ℝ) ≤ R ^ 6 := by positivity
  have hR2 : R ^ 2 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hR3 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  -- every high mode clears all thresholds
  have hbig : ∀ n : ℤ, ¬ n.natAbs ≤ M → (|Kb| + |K2| + |T| + 1) * R ^ 6 < |(n : ℝ)| := by
    intro n hn
    have h1 : (M : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast not_le.mp hn
    rw [Nat.cast_natAbs, Int.cast_abs] at h1
    linarith
  have hthr : ∀ n : ℤ, ¬ n.natAbs ≤ M → ∀ X : ℝ, ∀ k : ℕ, R ^ k ≤ R ^ 6 →
      |X| ≤ |Kb| + |K2| + |T| + 1 → X * R ^ k ≤ |(n : ℝ)| := by
    intro n hn X k hk hX
    have hk0 : (0 : ℝ) ≤ R ^ k := by positivity
    calc X * R ^ k ≤ |X| * R ^ k := mul_le_mul_of_nonneg_right (le_abs_self X) hk0
      _ ≤ (|Kb| + |K2| + |T| + 1) * R ^ 6 :=
          mul_le_mul hX hk hk0 (by positivity)
      _ ≤ |(n : ℝ)| := (hbig n hn).le
  -- termwise comparison with the weighted reflected gap action
  have hterm : ∀ i : Fin (2 * N + 1),
      (if (modeIndex N i).natAbs ≤ M then 0 else
          rhoAt Cb R (modeIndex N i) * fullWeightRate c.val (modeIndex N i) *
            ‖actualSchurQnCanonical38 (modeIndex N i) (schurRealPair w)‖ ^ 2) ≤
        (if (modeIndex N i).natAbs ≤ M then 0 else planeGapAction38 c.val N z (modeIndex N i)) := by
    intro i
    by_cases hi : (modeIndex N i).natAbs ≤ M
    · simp only [hi, if_true, le_refl]
    · simp only [hi, if_false]
      have h1 : Kb * R ^ 3 ≤ |((modeIndex N i : ℤ) : ℝ)| :=
        hthr _ hi Kb 3 hR3 (by linarith [abs_nonneg K2, abs_nonneg T])
      have h2 : T * R ^ 3 ≤ |((modeIndex N i : ℤ) : ℝ)| :=
        hthr _ hi T 3 hR3 (by linarith [abs_nonneg K2, abs_nonneg Kb])
      rw [rhoAt_eq_actualSchurRho38, schurRealPair,
        actualSchurQnCanonical38_eq R hR (modeIndex N i) h2 (w, actualH1Conj38 w) hwR hw2]
      exact hgb c.val hb hu R hR (modeIndex N i) h1 w hwR
  set s := Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ (modeIndex N i).natAbs ≤ M) with hs
  have hsum : SobolevSquareSummable 1 (physicalFourier (planeL2 N z)) := by
    rw [← planeField38_eq_planeL2]
    exact physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable _
  have hnorm : ‖physicalSobolevL2 1 (planeL2 N z) hsum‖ ≤ R := by
    rw [← planeH1Norm38_eq_physicalSobolev N z hsum]; exact hz'.le
  calc _ ≤ ∑ i : Fin (2 * N + 1),
        (if (modeIndex N i).natAbs ≤ M then 0 else planeGapAction38 c.val N z (modeIndex N i)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i ∈ s, planeGapAction38 c.val N z (modeIndex N i) := by
        rw [hs, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : (modeIndex N i).natAbs ≤ M <;> simp [hi]
    _ = ∑ n ∈ s.image (modeIndex N), planeGapAction38 c.val N z n :=
        (Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)).symm
    _ ≤ fullEnergy38 c N z := by
        set S := s.image (modeIndex N) with hS
        have hS' : ∀ m ∈ S.image (fun n => -n), K2 * R ^ 2 ≤ |(m : ℝ)| := by
          intro m hm
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
          have hi' : ¬ (modeIndex N i).natAbs ≤ M := (Finset.mem_filter.mp hi).2
          rw [Int.cast_neg, abs_neg]
          exact hthr _ hi' K2 2 hR2 (by linarith [abs_nonneg Kb, abs_nonneg T])
        have hW := hW2 c N z R hR hsum hnorm (S.image (fun n => -n)) hS'
        rw [Finset.sum_image (fun a _ b _ h => neg_injective h)] at hW
        refine le_trans (le_of_eq ?_) hW
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [planeGapAction38, planeField38_eq_planeL2]

end NlsGge.ThirdConsultation.S
