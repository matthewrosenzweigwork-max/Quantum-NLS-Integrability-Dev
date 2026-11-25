import NlsGge.GK38.RealTypeSpectrumLevels
import NlsGge.GK38.RealTypeSpectrumIndexArithmetic

/-! # S5: the actual monotone surjective integer quasimomentum level map -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem lamSeq_real_cast38 (u : PhysicalL2) (k : ℤ) :
    lamSeq (realSlice u) k = ((lamSeq (realSlice u) k).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact perChar_root_real38 u _ ((lamSeq_enumeration38 (realSlice u)).1 k)

theorem periodic_level_index_exists38 (u : PhysicalL2) (k : ℤ) :
    ∃! n : ℤ, actualQuasimomentumRealPartE02_38 u (lamSeq (realSlice u) k).re = (n : ℝ) * Real.pi := by
  apply perChar_real_root_level38
  rw [← lamSeq_real_cast38]
  exact (lamSeq_enumeration38 (realSlice u)).1 k

def periodicLevelIndex38 (u : PhysicalL2) (k : ℤ) : ℤ :=
  Classical.choose (periodic_level_index_exists38 u k)

theorem periodicLevelIndex_spec38 (u : PhysicalL2) (k : ℤ) :
    actualQuasimomentumRealPartE02_38 u (lamSeq (realSlice u) k).re =
      (periodicLevelIndex38 u k : ℝ) * Real.pi :=
  (Classical.choose_spec (periodic_level_index_exists38 u k)).1

theorem periodicLevelIndex_unique38 (u : PhysicalL2) (k j : ℤ)
    (hj : actualQuasimomentumRealPartE02_38 u (lamSeq (realSlice u) k).re = (j : ℝ) * Real.pi) :
    j = periodicLevelIndex38 u k :=
  gap_level_index_unique38 (hj.symm.trans (periodicLevelIndex_spec38 u k))

theorem periodicLevelIndex_monotone38 (u : PhysicalL2) : Monotone (periodicLevelIndex38 u) := by
  intro k l hkl
  have hlex := lamSeq_mono38 (realSlice u) hkl
  have hreal : (lamSeq (realSlice u) k).re ≤ (lamSeq (realSlice u) l).re := by
    rcases (complexLexLE_iff38 _ _).mp hlex with h | h
    · exact h.le
    · exact h.1.le
  have hp := (monotone_actualQuasimomentumRealPartE02_38 u) hreal
  rw [periodicLevelIndex_spec38, periodicLevelIndex_spec38] at hp
  have hle : (periodicLevelIndex38 u k : ℝ) ≤ (periodicLevelIndex38 u l : ℝ) := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hle

theorem periodicLevelIndex_surjective38 (u : PhysicalL2) : Function.Surjective (periodicLevelIndex38 u) := by
  intro n
  obtain ⟨k, hk⟩ := ((lamSeq_enumeration38 (realSlice u)).2.1
    (actualGapLowerAllE02_38 u n : ℂ)).mp (gap_endpoint_roots38 u n).1
  refine ⟨k, (periodicLevelIndex_unique38 u k n ?_).symm⟩
  rw [hk, Complex.ofReal_re]
  exact (gap_endpoint_levels38 u n).2.1

theorem periodic_level_map_unique38 (u : PhysicalL2) : ∃! J : ℤ → ℤ,
    ∀ k : ℤ, actualQuasimomentumRealPartE02_38 u (lamSeq (realSlice u) k).re = (J k : ℝ) * Real.pi := by
  refine ⟨periodicLevelIndex38 u, periodicLevelIndex_spec38 u, ?_⟩
  intro J hJ
  funext k
  exact periodicLevelIndex_unique38 u k (J k) (hJ k)

end
end NlsGge.GK38
