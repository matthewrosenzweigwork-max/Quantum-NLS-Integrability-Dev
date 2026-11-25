import Mathlib
import NlsGge.Atomic.I.I040Core
import NlsGge.Atomic.I.I020
import NlsGge.Birkhoff.H02Hierarchy38b

                                                                                                                 
                                                                                  
                                                                                                                    
                                                                                                   
                                                                                                         
                                                                                       
                                                                                                                      
                                                                                  
                                                                                                                
                                                                                                                        
                                                                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I041C

theorem summable_J : Summable (fun n : ℤ => japaneseBracket n ^ (-3 / 2 : ℝ)) := by
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num]
  exact summable_japaneseBracket_rpow_neg (3 / 2) (by norm_num)

theorem J_nonneg (n : ℤ) : 0 ≤ japaneseBracket n ^ (-3 / 2 : ℝ) :=
  Real.rpow_nonneg (japaneseBracket_pos n).le _

theorem lintegral_majorant :
    (∫⁻ g : ℤ → ℂ, ∑' n : ℤ, ENNReal.ofReal
      (‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∂stdGauss38) =
      ∑' n : ℤ, ENNReal.ofReal (japaneseBracket n ^ (-3 / 2 : ℝ)) := by
  have hE : (fun g : ℤ → ℂ => ∑' n : ℤ, ENNReal.ofReal
      (‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ))) =
      sequenceEnergy (fun n : ℤ => japaneseBracket n ^ (-3 / 2 : ℝ)) := by
    funext g
    unfold sequenceEnergy
    exact tsum_congr fun n => by rw [mul_comm]
  rw [hE, lintegral_sequenceEnergy _ _ (fun _ => one_pos) J_nonneg]
  simp only [div_one]

theorem i041_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ (g : ℤ → ℂ) (n : ℤ),
      fullWeightRate c.val n * ‖zFull38 c.val g n‖ ^ 2 = ‖g n‖ ^ 2 ∧
      ∀ m : ℕ, hierRate38 c.val m n * ‖zHier38 c.val m g n‖ ^ 2 = ‖g n‖ ^ 2) ∧
    (∫⁻ g : ℤ → ℂ, ∑' n : ℤ, ENNReal.ofReal
      (‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∂stdGauss38) =
      ∑' n : ℤ, ENNReal.ofReal (japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
    (∫⁻ g : ℤ → ℂ, ∑' n : ℤ, ENNReal.ofReal
      (‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∂stdGauss38) < ⊤ ∧
    ∀ g ∈ Omega1_38 c.val,
      Summable (fun n : ℤ => ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
        |gapRemainderTermE02_38 (weight c.val) (physicalOfSequence (zFull38 c.val g)) n| ≤
          C * ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) ∧
        ∀ m : ℕ, 2 ≤ m →
          |gapRemainderTermE02_38 (partialWeight c.val m)
            (physicalOfSequence (zHier38 c.val m g)) n| ≤
              C * ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) := by
  obtain ⟨hl, hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  have hq : ∀ n : ℤ, 0 < fullWeightRate c.val n := fun n => fullWeightRate_pos lower upper c.val hl hb' hu' n
  have hqm : ∀ (m : ℕ) (n : ℤ), 0 < hierRate38 c.val m n := fun m n => hierRate38_pos lower c.val hl hb' m n
  have hA : ∀ (g : ℤ → ℂ) (n : ℤ),
      fullWeightRate c.val n * ‖zFull38 c.val g n‖ ^ 2 = ‖g n‖ ^ 2 ∧
      ∀ m : ℕ, hierRate38 c.val m n * ‖zHier38 c.val m g n‖ ^ 2 = ‖g n‖ ^ 2 := by
    intro g n
    refine ⟨?_, fun m => ?_⟩
    · rw [norm_sq_zFull38 lower upper c.val hl hb' hu' g n]
      have := (hq n).ne'
      field_simp
    · rw [norm_sq_zHier38 lower upper c.val hl hb' hu' m g n]
      have := (hqm m n).ne'
      field_simp
  have hval := lintegral_majorant
  refine ⟨hA, hval, lt_top_iff_ne_top.2 (by rw [hval]; exact summable_J.tsum_ofReal_ne_top), fun g hg => ?_⟩
  refine ⟨?_, ?_⟩
  · rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num]
    exact hg.2.congr (fun n => mul_comm _ _)
  · obtain ⟨hI, Bd, hBd0, hBdF, hBdH⟩ := NlsGge.ThirdConsultation.I040C.i040_of Bk hB lower upper c g hg
    obtain ⟨hsF, hsH, -⟩ := hI 1 2 (by simp)
    obtain ⟨C0, hC0, hsym⟩ := i020 lower upper hl hlu Bd hBd0
    refine ⟨C0, hC0, fun n => ⟨?_, fun m hm => ?_⟩⟩
    · have hs : SobolevSquareSummable 1 (physicalFourier (physicalOfSequence (zFull38 c.val g))) := by
        simpa using hsF
      have h1 := abs_gapRemainderTerm_le38 (weight c.val) hW (physicalOfSequence (zFull38 c.val g)) n
        (C0 * fullWeightRate c.val n * japaneseBracket n ^ (-3 / 2 : ℝ))
        (fun l hl => (hsym c _ hs hBdF n l hl).1)
      have hz1 : zFull38 c.val g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
        zFull38_mem_seqSobolev38_nat lower upper c.val hl hb' hu' hg 1
      rw [← hB, Bk.action_cleanΦinv38 _ hz1 n] at h1
      rw [← hB]
      refine h1.trans (le_of_eq ?_)
      have := (hA g n).1
      calc C0 * fullWeightRate c.val n * japaneseBracket n ^ (-3 / 2 : ℝ) * ‖zFull38 c.val g n‖ ^ 2
          = C0 * (fullWeightRate c.val n * ‖zFull38 c.val g n‖ ^ 2) * japaneseBracket n ^ (-3 / 2 : ℝ) := by
            ring
        _ = C0 * ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) := by rw [this]
    · have hs : SobolevSquareSummable 1 (physicalFourier (physicalOfSequence (zHier38 c.val m g))) := by
        simpa using hsH m hm
      have h1 := abs_gapRemainderTerm_le38 (partialWeight c.val m) (continuous_partialWeight38 c.val m)
        (physicalOfSequence (zHier38 c.val m g)) n
        (C0 * hierRate38 c.val m n * japaneseBracket n ^ (-3 / 2 : ℝ))
        (fun l hl => (hsym c _ hs (hBdH m hm) n l hl).2 m)
      have hz1 : zHier38 c.val m g ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
        seqSobolev38_mono (by exact_mod_cast (by omega : 1 ≤ m - 1))
          (zHier38_mem_seqSobolev38 lower upper c.val hl hb' hu' hg hm)
      rw [← hB, Bk.action_cleanΦinv38 _ hz1 n] at h1
      rw [← hB]
      refine h1.trans (le_of_eq ?_)
      have := (hA g n).2 m
      calc C0 * hierRate38 c.val m n * japaneseBracket n ^ (-3 / 2 : ℝ) * ‖zHier38 c.val m g n‖ ^ 2
          = C0 * (hierRate38 c.val m n * ‖zHier38 c.val m g n‖ ^ 2) * japaneseBracket n ^ (-3 / 2 : ℝ) := by
            ring
        _ = C0 * ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) := by rw [this]

end NlsGge.ThirdConsultation.I041C
