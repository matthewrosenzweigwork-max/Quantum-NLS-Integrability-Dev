import NlsGge.GK38.RealTypeSpectrumIndex
import NlsGge.GK38.RealTypeSpectrumSigns

/-! # S5: far normalization fixes the integer index for every spectral pair -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem perChar_root_level_sign38 (u : PhysicalL2) (x : ℝ) (n : ℤ)
    (hx : perChar (realSlice u) (x : ℂ) = 0)
    (hp : actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi) :
    discrim (realSlice u) (x : ℂ) = 2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
  rcases perChar_root_eq_level_endpoint38 u x n hx hp with he | he
  · rw [he, discrim_realSlice, (actualGapEndpoint_halfTrace_all_E02_38 u n).1]
  · rw [he, discrim_realSlice, (actualGapEndpoint_halfTrace_all_E02_38 u n).2]

theorem periodicLevelIndex_pair_cos38 (u : PhysicalL2) (n : ℤ) :
    Real.cos ((periodicLevelIndex38 u (2 * n) : ℝ) * Real.pi) = Real.cos ((n : ℝ) * Real.pi) ∧
    Real.cos ((periodicLevelIndex38 u (2 * n + 1) : ℝ) * Real.pi) = Real.cos ((n : ℝ) * Real.pi) := by
  have hsign (k : ℤ) : discrim (realSlice u) (lamSeq (realSlice u) k) =
      2 * (Real.cos ((periodicLevelIndex38 u k : ℝ) * Real.pi) : ℂ) := by
    rw [lamSeq_real_cast38]
    apply perChar_root_level_sign38
    · rw [← lamSeq_real_cast38]; exact (lamSeq_enumeration38 (realSlice u)).1 k
    · exact periodicLevelIndex_spec38 u k
  have hm := hsign (2 * n)
  have hp := hsign (2 * n + 1)
  change discrim (realSlice u) (lamMinus (realSlice u) n) = _ at hm
  change discrim (realSlice u) (lamPlus (realSlice u) n) = _ at hp
  constructor
  · have he := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
      (hm.symm.trans (periodic_real_pair_signs38 u n).1)
    exact_mod_cast he
  · have he := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
      (hp.symm.trans (periodic_real_pair_signs38 u n).2)
    exact_mod_cast he

/-- A far quarter-disc root has the same integer level as its disc center. -/
theorem periodic_far_level_index38 (u : PhysicalL2) (k n : ℤ) (R : ℝ)
    (hR : ∀ x : ℝ, R ≤ |x| → ‖actualQuasimomentumBoundaryE02_38 u x - x‖ ≤ Real.pi / 4)
    (hlarge : R ≤ (n : ℝ) * Real.pi - Real.pi / 4)
    (hdisc : lamSeq (realSlice u) k ∈ ball (countingCenter38 n) (Real.pi / 4)) :
    periodicLevelIndex38 u k = n := by
  let x := (lamSeq (realSlice u) k).re
  obtain ⟨hl, hu⟩ := counting_small_re_bounds38 hdisc
  have hxR : R ≤ |x| := (hlarge.trans hl.le).trans (le_abs_self x)
  have hp : |actualQuasimomentumRealPartE02_38 u x - x| ≤ Real.pi / 4 := by
    have h : |actualQuasimomentumRealPartE02_38 u x - x| ≤
        ‖actualQuasimomentumBoundaryE02_38 u x - (x : ℂ)‖ := by
      simpa only [actualQuasimomentumRealPartE02_38, Complex.sub_re, Complex.ofReal_re] using
        Complex.abs_re_le_norm (actualQuasimomentumBoundaryE02_38 u x - (x : ℂ))
    exact h.trans (hR x hxR)
  have hx : |x - (n : ℝ) * Real.pi| < Real.pi / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hgrid : |(periodicLevelIndex38 u k : ℝ) * Real.pi - (n : ℝ) * Real.pi| < Real.pi / 2 := by
    rw [← periodicLevelIndex_spec38]
    calc |actualQuasimomentumRealPartE02_38 u x - (n : ℝ) * Real.pi|
        = |(actualQuasimomentumRealPartE02_38 u x - x) + (x - (n : ℝ) * Real.pi)| := by congr 1; ring
      _ ≤ |actualQuasimomentumRealPartE02_38 u x - x| + |x - (n : ℝ) * Real.pi| := abs_add_le _ _
      _ < Real.pi / 2 := by linarith
  rw [← sub_mul, abs_mul, abs_of_pos Real.pi_pos] at hgrid
  have hi : |((periodicLevelIndex38 u k - n : ℤ) : ℝ)| < 1 := by
    push_cast
    nlinarith [Real.pi_pos]
  have hi' : |periodicLevelIndex38 u k - n| < 1 := by exact_mod_cast hi
  have h := abs_lt.mp hi'
  omega

theorem periodicLevelIndex_far38 (u : PhysicalL2) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n →
      periodicLevelIndex38 u (2 * n) = n ∧ periodicLevelIndex38 u (2 * n + 1) = n := by
  obtain ⟨R, _hRpos, hR⟩ := actualQuasimomentumBoundaryE02_38_sub_le u (Real.pi / 4) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_gt ((R + Real.pi / 4) / Real.pi)
  let C := canonicalCountingCutoff38 (realSlice u)
  let N := max (C + 1) (K + 1)
  have hCN : C + 1 ≤ N := le_max_left _ _
  have hKN : K + 1 ≤ N := le_max_right _ _
  refine ⟨N, fun n hn => ?_⟩
  have hnC : (C : ℤ) < n := by omega
  have hnK : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (K : ℤ) ≤ n by omega)
  have hlarge : R ≤ (n : ℝ) * Real.pi - Real.pi / 4 := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    nlinarith [Real.pi_pos]
  have hcert : RootCountingAt38 (perChar (realSlice u)) 2 C :=
    (canonicalCountingCutoff_spec38 (realSlice u)).1
  have hminus : lamSeq (realSlice u) (2 * n) ∈ ball (countingCenter38 n) (Real.pi / 4) := by
    rw [lamSeq_eq_candidate38 _ hcert]
    have hk : ¬ periodicCentralIndex38 C (2 * n) := by
      unfold periodicCentralIndex38
      omega
    simpa only [(periodic_index_pair38 n).1] using periodicCandidate_far_mem38 hcert hk
  have hplus : lamSeq (realSlice u) (2 * n + 1) ∈ ball (countingCenter38 n) (Real.pi / 4) := by
    rw [lamSeq_eq_candidate38 _ hcert]
    have hk : ¬ periodicCentralIndex38 C (2 * n + 1) := by
      unfold periodicCentralIndex38
      omega
    simpa only [(periodic_index_pair38 n).2.1] using periodicCandidate_far_mem38 hcert hk
  exact ⟨periodic_far_level_index38 u _ n R hR hlarge hminus,
    periodic_far_level_index38 u _ n R hR hlarge hplus⟩

/-- One normalized far pair removes the integer translation for every index. -/
theorem periodicLevelIndex_pair_eq38 (u : PhysicalL2) (n : ℤ) :
    periodicLevelIndex38 u (2 * n) = n ∧ periodicLevelIndex38 u (2 * n + 1) = n := by
  have hstep := realType_pair_index_steps38 (periodicLevelIndex38 u)
    (periodicLevelIndex_monotone38 u) (periodicLevelIndex_surjective38 u) (periodicLevelIndex_pair_cos38 u)
  obtain ⟨c, hc⟩ := realType_pair_index_translation38 _ hstep
  obtain ⟨N, hN⟩ := periodicLevelIndex_far38 u
  have hfar := (hN (N : ℤ) le_rfl).1
  have he := (hc (N : ℤ)).1
  have hz : c = 0 := by omega
  simpa only [hz, add_zero] using hc n

theorem periodic_same_index_levels38 (u : PhysicalL2) (n : ℤ) :
    actualQuasimomentumRealPartE02_38 u (lamMinus (realSlice u) n).re = (n : ℝ) * Real.pi ∧
    actualQuasimomentumRealPartE02_38 u (lamPlus (realSlice u) n).re = (n : ℝ) * Real.pi := by
  have hm := periodicLevelIndex_spec38 u (2 * n)
  have hp := periodicLevelIndex_spec38 u (2 * n + 1)
  rw [(periodicLevelIndex_pair_eq38 u n).1] at hm
  rw [(periodicLevelIndex_pair_eq38 u n).2] at hp
  exact ⟨hm, hp⟩

end
end NlsGge.GK38
