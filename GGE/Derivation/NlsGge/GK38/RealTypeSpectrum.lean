import NlsGge.GK38.RealTypeSpectrumNormalization

/-! # S5: same-index identification with the existing gap endpoints

GK book I.7. Exhaustive enumeration, normalized levels and real order identify
both endpoints, including coincident endpoints and every negative integer.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicLevelIndex_fiber38 (u : PhysicalL2) (k n : ℤ) :
    periodicLevelIndex38 u k = n ↔ k = 2 * n ∨ k = 2 * n + 1 := by
  constructor
  · intro h
    have hk : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
    rcases hk with hk | hk
    · rw [hk, (periodicLevelIndex_pair_eq38 u (k / 2)).1] at h
      exact Or.inl (by omega)
    · rw [hk, (periodicLevelIndex_pair_eq38 u (k / 2)).2] at h
      exact Or.inr (by omega)
  · rintro (hk | hk)
    · rw [hk]; exact (periodicLevelIndex_pair_eq38 u n).1
    · rw [hk]; exact (periodicLevelIndex_pair_eq38 u n).2

theorem periodic_level_root_pair38 (u : PhysicalL2) (x : ℝ) (n : ℤ)
    (hx : perChar (realSlice u) (x : ℂ) = 0)
    (hp : actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi) :
    (x : ℂ) = lamMinus (realSlice u) n ∨ (x : ℂ) = lamPlus (realSlice u) n := by
  obtain ⟨k, hk⟩ := ((lamSeq_enumeration38 (realSlice u)).2.1 (x : ℂ)).mp hx
  have hj : periodicLevelIndex38 u k = n := by
    apply (periodicLevelIndex_unique38 u k n ?_).symm
    rw [hk, Complex.ofReal_re]
    exact hp
  rcases (periodicLevelIndex_fiber38 u k n).mp hj with hkn | hkn
  · exact Or.inl (by simpa only [hkn, lamMinus] using hk.symm)
  · exact Or.inr (by simpa only [hkn, lamPlus] using hk.symm)

theorem periodic_pair_re_order38 (u : PhysicalL2) (n : ℤ) :
    (lamMinus (realSlice u) n).re ≤ (lamPlus (realSlice u) n).re := by
  rcases (complexLexLE_iff38 _ _).mp (lamMinus_le_lamPlus38 (realSlice u) n) with h | h
  · exact h.le
  · exact h.1.le

theorem lamPlus_real (u : PhysicalL2) (n : ℤ) :
    lamPlus (realSlice u) n = (actualGapUpperAllE02_38 u n : ℂ) ∧
    lamMinus (realSlice u) n = (actualGapLowerAllE02_38 u n : ℂ) := by
  have hm : (lamMinus (realSlice u) n).re ∈
      Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u n).2]
    exact (periodic_same_index_levels38 u n).1
  have hp : (lamPlus (realSlice u) n).re ∈
      Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u n).2]
    exact (periodic_same_index_levels38 u n).2
  have horder := periodic_pair_re_order38 u n
  have hlow := periodic_level_root_pair38 u (actualGapLowerAllE02_38 u n) n
    (gap_endpoint_roots38 u n).1 (gap_endpoint_levels38 u n).2.1
  have hupp := periodic_level_root_pair38 u (actualGapUpperAllE02_38 u n) n
    (gap_endpoint_roots38 u n).2 (gap_endpoint_levels38 u n).2.2
  have hl : (lamMinus (realSlice u) n).re = actualGapLowerAllE02_38 u n := by
    rcases hlow with he | he
    · have h := congrArg Complex.re he
      simpa only [Complex.ofReal_re] using h.symm
    · have h := congrArg Complex.re he
      simp only [Complex.ofReal_re] at h
      linarith [hm.1]
  have hu : (lamPlus (realSlice u) n).re = actualGapUpperAllE02_38 u n := by
    rcases hupp with he | he
    · have h := congrArg Complex.re he
      simp only [Complex.ofReal_re] at h
      linarith [hp.2]
    · have h := congrArg Complex.re he
      simpa only [Complex.ofReal_re] using h.symm
  constructor
  · change lamSeq (realSlice u) (2 * n + 1) = _
    change (lamSeq (realSlice u) (2 * n + 1)).re = _ at hu
    rw [lamSeq_real_cast38, hu]
  · change lamSeq (realSlice u) (2 * n) = _
    change (lamSeq (realSlice u) (2 * n)).re = _ at hl
    rw [lamSeq_real_cast38, hl]

end
end NlsGge.GK38
