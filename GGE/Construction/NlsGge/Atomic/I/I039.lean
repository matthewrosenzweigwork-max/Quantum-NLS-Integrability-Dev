import NlsGge.Birkhoff.H02Hierarchy38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.Birkhoff.S04Moments38c
import NlsGge.Sobolev.SourceWeighted

                                                                                             
                                                                                                                
                                                                                                                              
                                                                                                                            
                                                                                                                       
                                                       

set_option autoImplicit false

open NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core MeasureTheory Filter Topology
open scoped ENNReal

namespace NlsGge.ThirdConsultation.I
noncomputable section

abbrev sobolevSeqNorm := NlsGge.Birkhoff.hnorm38

theorem i039 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    MeasurableSet (Omega1_38 c.val) ∧ stdGauss38 (Omega1_38 c.val) = 1 ∧
    (∀ m : ℕ, stdGauss38.map (zHier38 c.val m) = gammaM38 m (coefficient c.val)) ∧
    stdGauss38.map (zFull38 c.val) = fullWeightSequenceGaussian c.val ∧
    ∀ g ∈ Omega1_38 c.val, ∀ (r m₀ : ℕ), max 2 (r + 1) ≤ m₀ →
      SobolevSquareSummable (r : ℝ) (zFull38 c.val g) ∧
      (∀ m : ℕ, m₀ ≤ m → SobolevSquareSummable (r : ℝ) (zHier38 c.val m g)) ∧
      Tendsto (fun k : ℕ => sobolevSeqNorm r
        (fun n : ℤ => zHier38 c.val (m₀ + k) g n - zFull38 c.val g n)) atTop (𝓝 0) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hmeas : MeasurableSet (Omega1_38 c.val) := by
    have hA : ∀ m : ℕ, MeasurableSet {g : ℤ → ℂ | 2 ≤ m →
        Summable (fun n : ℤ => tailRatio38 c.val m n * ‖g n‖ ^ 2)} := by
      intro m
      by_cases hm : 2 ≤ m
      · have hset : {g : ℤ → ℂ | 2 ≤ m →
            Summable (fun n : ℤ => tailRatio38 c.val m n * ‖g n‖ ^ 2)} =
            {g : ℤ → ℂ | Summable (fun n : ℤ => tailRatio38 c.val m n * ‖g n‖ ^ 2)} := by
          ext g
          simp [hm]
        rw [hset]
        exact measurableSet_sequenceSummable _
          (fun n => tailRatio38_nonneg lower upper c.val hl hb' hu' m n)
      · convert MeasurableSet.univ using 1
        ext g
        simp [hm]
    have h1 : MeasurableSet {g : ℤ → ℂ | ∀ m : ℕ, 2 ≤ m →
        Summable (fun n : ℤ => tailRatio38 c.val m n * ‖g n‖ ^ 2)} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter hA
    have h2 : MeasurableSet {g : ℤ → ℂ |
        Summable (fun n : ℤ => japaneseBracket n ^ (-(3 / 2) : ℝ) * ‖g n‖ ^ 2)} :=
      measurableSet_sequenceSummable _ (fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _)
    exact h1.inter h2
  have hprob : stdGauss38 (Omega1_38 c.val) = 1 :=
    (prob_compl_eq_zero_iff hmeas).1 (ae_iff.1 (ae_mem_Omega1_38 lower upper c.val hl hb' hu'))
  have hqH : ∀ m : ℕ, ∀ n : ℤ, 0 < hierRate38 c.val m n := fun m n =>
    hierRate38_pos lower c.val hl hb' m n
  have hqF : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lower upper c.val hl hb' hu' n
  refine ⟨hmeas, hprob, ?_, ?_, ?_⟩
  · intro m
    show (countableComplexGaussian (fun _ => (1 : ℝ))).map (zHier38 c.val m) = _
    unfold zHier38
    rw [← countableComplexGaussian_eq_map_scale38 (hierRate38 c.val m) (hqH m)]
    rfl
  · show (countableComplexGaussian (fun _ => (1 : ℝ))).map (zFull38 c.val) = _
    unfold zFull38
    rw [← countableComplexGaussian_eq_map_scale38 (fullWeightRate c.val) hqF]
    rfl
  · intro g hg r m₀ hm₀
    have hm2 : 2 ≤ m₀ := le_trans (le_max_left _ _) hm₀
    have hr1 : r + 1 ≤ m₀ := le_trans (le_max_right _ _) hm₀
    refine ⟨?_, ?_, ?_⟩
    · exact (mem_seqSobolev38_iff _ _).1 (zFull38_mem_seqSobolev38_nat lower upper c.val hl hb' hu' hg r)
    · intro m hm
      have hmem := zHier38_mem_seqSobolev38 lower upper c.val hl hb' hu' hg (m := m) (by omega)
      have hle : ((r : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : r ≤ m - 1)
      exact (mem_seqSobolev38_iff _ _).1 (seqSobolev38_mono hle hmem)
    · have hsum_eq : ∀ k : ℕ, sobolevSeqNorm r
          (fun n : ℤ => zHier38 c.val (m₀ + k) g n - zFull38 c.val g n) =
          Real.sqrt (∑' n : ℤ, sobolevModeWeight (r : ℝ) n *
            ‖zHier38 c.val (m₀ + k) g n - zFull38 c.val g n‖ ^ 2) := by
        intro k
        have hle : ((r : ℕ) : ℝ) ≤ ((m₀ + k - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : r ≤ m₀ + k - 1)
        have hz : zHier38 c.val (m₀ + k) g ∈ seqSobolev38 (r : ℝ) :=
          seqSobolev38_mono hle (zHier38_mem_seqSobolev38 lower upper c.val hl hb' hu' hg
            (m := m₀ + k) (by omega))
        have hdiff := seqSobolev38_sub hz (zFull38_mem_seqSobolev38_nat lower upper c.val hl hb' hu' hg r)
        have hs := (mem_seqSobolev38_iff _ _).1 hdiff
        unfold sobolevSeqNorm NlsGge.Birkhoff.hnorm38
        rw [NlsGge.Birkhoff.sobEnergy38_eq_tsum r
          (z := fun n : ℤ => zHier38 c.val (m₀ + k) g n - zFull38 c.val g n) hs]
        rfl
      have hshift : Tendsto (fun k : ℕ => m₀ + k) atTop atTop :=
        tendsto_atTop_atTop.2 (fun b => ⟨b, fun k hk => by omega⟩)
      have hT := (tendsto_scale_sobolev38 lower upper c.val hl hb' hu' hg r).comp hshift
      have hS := (Real.continuous_sqrt.tendsto 0).comp hT
      rw [Real.sqrt_zero] at hS
      exact Tendsto.congr (fun k => (hsum_eq k).symm) hS

end
end NlsGge.ThirdConsultation.I
