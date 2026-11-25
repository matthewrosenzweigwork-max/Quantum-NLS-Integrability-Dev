import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Hierarchy.UniformPartitionBound38
import NlsGge.Spectral.ReservedEnergyCoercivity38V1

                                                                                                          
                                                                                         
                                                                                                              
                               
                                                                                                                   
                                                                                                              
                                                                                                           
                                                                                                
                                                                                                                 
                                                                                                                 
                                                                                                             
                                                                                                       
                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

/-- The S-056 shell level is the production shell level. -/
theorem shellLevelV6_eq_shellLevel38 (g R₀ : ℝ) : shellLevelV6 g R₀ = shellLevel38 g R₀ := by
  funext k
  unfold shellLevelV6 shellLevel38
  by_cases h : (k : ℝ) < R₀
  · rw [if_pos h, if_neg (not_le.mpr h)]
  · rw [if_neg h, if_pos (not_lt.mp h)]

theorem relativePartition_le_shellSum (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C A g R₀ : ℝ, 0 < C ∧ 0 < A ∧ 0 < g ∧ 1 ≤ R₀ ∧
      (∀ (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) (R : ℝ),
        R₀ ≤ R → R ≤ planeH1Norm38 N z →
        g * Real.exp (g * R ^ (1 / 4 : ℝ)) ≤ reservedEnergy38 c N z) ∧
      (∀ (c : BoundedCoefficients lo up) (N : ℕ),
        Summable (fun k : ℕ => Real.exp (A * ((k : ℝ) + 2) ^ 9 -
          shiftEps38 lo up * shellLevelV6 g R₀ k)) ∧
        relativePartition38 c N ≤ C * ∑' k : ℕ,
          Real.exp (A * ((k : ℝ) + 2) ^ 9 - shiftEps38 lo up * shellLevelV6 g R₀ k)) := by
  obtain ⟨Cs, hCs, hschur⟩ :=
    actualSchurBallIntegral_fullEnergy38 (3 * lo / 4) up (by linarith) (by linarith)
  obtain ⟨g, R₀, hg, hR₀, hcoer⟩ := reservedEnergy_coercive38 lo up hl hlu
  obtain ⟨C₀, hC₀, hfree⟩ := freeNormalizer_shifted_le38
  have hε := shiftEps38_pos hl hlu
  have hsum := shellSeries_summable38 (C := Cs) (g := g) (ε := shiftEps38 lo up) R₀ hCs.le hg hε
  refine ⟨C₀, Cs, g, R₀, hC₀, hCs, hg, hR₀, hcoer, fun c N => ?_⟩
  rw [shellLevelV6_eq_shellLevel38]
  refine ⟨hsum, ?_⟩
  set S : ℝ := ∑' k : ℕ, Real.exp (Cs * ((k : ℝ) + 2) ^ 9 -
    shiftEps38 lo up * shellLevel38 g R₀ k) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => (Real.exp_pos _).le
  have hD := freeNormalizer38_pos c N
  have hI := integrable_exp_neg_fullEnergy38 c N
  have hdom := shell_lintegral_bound38 c N
    (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi /
      fullWeightRate (shiftedCoefficients38 c).val (modeIndex N i))) Cs g R₀
    (fun R hR => hschur (shiftedCoefficients38 c) R hR N)
    (fun z R h1 h2 => hcoer c N z R h1 h2)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsum,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => div_nonneg Real.pi_pos.le
      (fullWeightRate_pos38 (shiftedCoefficients38 c) _).le)] at hdom
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => div_nonneg Real.pi_pos.le
      (fullWeightRate_pos38 (shiftedCoefficients38 c) _).le),
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)] at hdom
  have hdom' : fullPartition38 c N ≤ freeNormalizer38 (shiftedCoefficients38 c) N * S := by
    have := (ENNReal.ofReal_le_ofReal_iff (by
      have := freeNormalizer38_pos (shiftedCoefficients38 c) N
      positivity)).mp hdom
    exact this
  have h2 := hfree lo up c N
  have h3 : fullPartition38 c N ≤ C₀ * S * freeNormalizer38 c N := by
    calc fullPartition38 c N ≤ freeNormalizer38 (shiftedCoefficients38 c) N * S := hdom'
      _ ≤ (C₀ * freeNormalizer38 c N) * S := mul_le_mul_of_nonneg_right h2 hS0
      _ = _ := by ring
  unfold relativePartition38
  rw [div_le_iff₀ hD]
  exact h3

end NlsGge.ThirdConsultation.S
