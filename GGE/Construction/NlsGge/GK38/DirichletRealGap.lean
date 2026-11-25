import NlsGge.GK38.DirichletRealContinuity
import NlsGge.GK38.RealTypeMultiplicityOrders

/-! Actual gap classification for Dirichlet roots from the squared antidiscriminant.
Private source anchor: book I.6 Lemma 6.6 and I.7 Lemma 7.2. -/
set_option autoImplicit false
open Filter Topology Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_cos_level38 (w : ℂ) (hi : (Complex.cos w).im = 0) (hs : 1 ≤ (Complex.cos w).re ^ 2) :
    ∃ n : ℤ, w.re = (n : ℝ) * Real.pi := by
  have hz : Real.sin w.re = 0 := by
    by_cases hy : w.im = 0
    · have hw : w = (w.re : ℂ) := Complex.ext rfl (by simp [hy])
      rw [hw, Complex.cos_ofReal_re] at hs
      nlinarith [Real.sin_sq_add_cos_sq w.re, sq_nonneg (Real.sin w.re)]
    · rw [complex_cos_im_E02_38] at hi
      have hp : Real.sin w.re * Real.sinh w.im = 0 := by linarith
      exact (mul_eq_zero.mp hp).resolve_right (fun h => hy (Real.sinh_eq_zero.mp h))
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
  exact ⟨n, hn.symm⟩

theorem dirichlet_root_halfTrace_sq38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) :
    1 ≤ (actualPhysicalUnitHalfTrace32 u (x : ℂ)).re ^ 2 := by
  have h := dirichlet_perChar_eq_anti_sq38 (realSlice u) (x : ℂ) hx
  rw [perChar_eq] at h
  have hreal := dirichlet_real_characteristic38 u x
  have ha : antiDiscrim (realSlice u) (x : ℂ) =
      ((antiDiscrim (realSlice u) (x : ℂ)).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hreal.2.1)
  rw [ha] at h
  have hr := dirichlet_scalar_square38 _ _ hreal.2.2 h
  rw [discrim_realSlice] at hr
  norm_num [Complex.mul_re] at hr
  nlinarith [sq_nonneg (antiDiscrim (realSlice u) (x : ℂ)).re]

theorem dirichlet_root_some_gap38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) :
    ∃! n : ℤ, x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  have hc := actualQuasimomentumBoundaryE02_38_cos u x
  obtain ⟨n, hn⟩ := dirichlet_cos_level38 (actualQuasimomentumBoundaryE02_38 u x)
    (by rw [hc]; exact actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u x)
    (by rw [hc]; exact dirichlet_root_halfTrace_sq38 u x hx)
  have hmem : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u n).2]
    exact hn
  exact ⟨n, hmem, fun m hm => gap_interval_index_unique38 u hm hmem⟩

end
end NlsGge.GK38
