import NlsGge.GK38.EigenvalueCompactnessRealKernel
import NlsGge.GK38.RealTypeMultiplicityRealDeriv
import NlsGge.Spectral.ActualPhysicalL2ZsEndpointTraceCriterionV2

/-! # S7: actual unit real eigen-directions at both labelled endpoints -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem endpoint_trace38 (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hx : EndpointAt38 u n x) :
    (monodromyPair (realSlice u) (x : ℂ)).trace =
      2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
  change discrim (realSlice u) (x : ℂ) = _
  rcases hx with rfl | rfl
  · exact (gap_discrim_endpoint_values38 u n).1
  · exact (gap_discrim_endpoint_values38 u n).2

theorem periodic_eigen_direction_exists38 (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hx : EndpointAt38 u n x) : ∃ a : ℂ, EigenDirectionAt38 u x n a := by
  let M := monodromyPair (realSlice u) (x : ℂ)
  have h0 : star (M 0 0) = M 1 1 := by
    change star (monodromyPair (realSlice u) (x : ℂ) 0 0) =
      monodromyPair (realSlice u) (x : ℂ) 1 1
    rw [monodromyPair_realSlice]
    simpa using actualComplexZsDysonTsum_real_entry_star (e02Pot38 u) x 1 0 0
  have h1 : star (M 0 1) = M 1 0 := by
    change star (monodromyPair (realSlice u) (x : ℂ) 0 1) =
      monodromyPair (realSlice u) (x : ℂ) 1 0
    rw [monodromyPair_realSlice]
    simpa using actualComplexZsDysonTsum_real_entry_star (e02Pot38 u) x 1 0 1
  have he : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      M.mulVec v = (Real.cos ((n : ℝ) * Real.pi) : ℂ) • v := by
    have hc : Real.cos ((n : ℝ) * Real.pi) = 1 ∨
        Real.cos ((n : ℝ) * Real.pi) = -1 :=
      abs_eq_abs.mp (by simpa using Real.abs_cos_int_mul_pi n)
    rcases hc with hc | hc
    · have ht : M.trace = 2 := by simpa [M, hc] using endpoint_trace38 u n x hx
      rw [hc]
      obtain ⟨v, hv, he⟩ := (actualPhysicalL2ZsDysonTsum_fixed_vector_iff_trace_two
        u (x : ℂ) 1 (by norm_num)).mpr (by simpa [M, monodromyPair_realSlice] using ht)
      exact ⟨v, hv, by simpa [M, monodromyPair_realSlice] using he⟩
    · have ht : M.trace = -2 := by simpa [M, hc] using endpoint_trace38 u n x hx
      rw [hc]
      obtain ⟨v, hv, he⟩ := (actualPhysicalL2ZsDysonTsum_negative_vector_iff_trace_neg_two
        u (x : ℂ) 1 (by norm_num)).mpr (by simpa [M, monodromyPair_realSlice] using ht)
      exact ⟨v, hv, by simpa [M, monodromyPair_realSlice] using he⟩
  exact real_matrix_unit_eigenvector38 M h0 h1 _ he

end
end NlsGge.GK38
