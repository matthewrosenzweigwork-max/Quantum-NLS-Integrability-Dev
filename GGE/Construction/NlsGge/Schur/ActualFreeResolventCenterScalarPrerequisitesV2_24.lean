import NlsGge.Schur.FreeResolvent

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual signed spectral center is a point of its closed radius-one disk. -/
theorem spectralCenter_mem_spectralDisk_scalarV2_24 (n : ℤ) :
    spectralCenter n ∈ spectralDisk n := by
  simp [spectralDisk]

/-- At the actual center the resonant coefficient vanishes, and every
nonresonant coefficient has size at most `1/(2π)` by the signed gap of two. -/
theorem freeResolventCoeff_center_norm_le_scalarV2_24 (n : ℤ) (m : Sector n) :
    ‖freeResolventCoeff n (spectralCenter n) m‖ ≤ 1 / (2 * Real.pi) := by
  by_cases hm : m = resonantIndex n
  · simp [freeResolventCoeff, hm]
    positivity
  · have hgap := sector_gap_two n m hm
    have hden :
        (2 : ℝ) * Real.pi ≤
          ‖spectralCenter n - spectralCenter m.val‖ := by
      rw [spectralCenter_distance]
      nlinarith [Real.pi_pos]
    rw [freeResolventCoeff, if_neg hm]
    rw [norm_inv]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity) hden)

/-- The pinned reciprocal coefficient satisfies the actual center-shift
identity on the full signed disk, with zero retained at resonance. -/
theorem freeResolventCoeff_center_shift_identity_scalarV2_24
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m : Sector n) :
    (1 + (z - spectralCenter n) *
        freeResolventCoeff n (spectralCenter n) m) *
      freeResolventCoeff n z m =
        freeResolventCoeff n (spectralCenter n) m := by
  by_cases hm : m = resonantIndex n
  · simp [freeResolventCoeff, hm]
  · have hcenter : spectralCenter n - spectralCenter m.val ≠ 0 :=
      spectral_denominator_ne_zero n (spectralCenter n)
        (spectralCenter_mem_spectralDisk_scalarV2_24 n) m hm
    have hzden : z - spectralCenter m.val ≠ 0 :=
      spectral_denominator_ne_zero n z hz m hm
    simp only [freeResolventCoeff, if_neg hm]
    field_simp [hcenter, hzden]
    ring

end NlsGge.Schur
