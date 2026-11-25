import NlsGge.Spectral.ComplexQuadraticSmallRootClosedGraphContinuity36V2
import NlsGge.Spectral.ActualPhysicalMonodromyCouplingContinuity36V2
import NlsGge.Spectral.ActualPhysicalUnitAnalyticSmallBranch33V5
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot
/-- A continuous inside-unit characteristic root exists along the actual
real coupling path of the rough source potential, for every fixed upper-half
plane parameter. All coefficient continuity and boundary exclusion premises
are realized here by actual monodromy theorems. This does not identify its
vacuum value or any logarithm integer, or assert high-energy normalization. -/
theorem actualPhysicalUnitSmallRoot_coupling_continuousExists36V1
    (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    ∃ r : ℝ → ℂ, ContinuousOn r (Set.Icc (0 : ℝ) 1) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        r τ ^ 2 - 2 * actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z * r τ + 1 = 0 ∧
          ‖r τ‖ < 1 := by
  have hex (τ : ℝ) : ∃ w : ℂ,
      w^2 - 2 * actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z * w + 1 = 0 ∧
      ‖w‖ < 1 := by
    obtain ⟨s, l, hs, hl, hsq, he, hn⟩ :=
      exists_actualPhysicalUnitAnalyticSmallBranch33 ((τ : ℂ) • u)
    refine ⟨actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z + s z, ?_, hn z hz⟩
    linear_combination hsq z hz
  choose r hr using hex
  let d : ℝ → ℂ := fun τ => actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z
  have hd : Continuous (fun τ : Set.Icc (0 : ℝ) 1 => d τ) := by
    exact continuousOn_iff_continuous_restrict.mp
      (actualPhysicalUnitHalfTrace_coupling_continuousOn36V2 u z z.im
        hz.le hz.le le_rfl)
  have hb (τ : Set.Icc (0 : ℝ) 1) (v : ℂ)
      (hv : v^2 - 2 * d τ * v + 1 = 0) : ‖v‖ ≠ 1 := by
    intro hn
    obtain ⟨w, hw, he⟩ :=
      (actualPhysicalUnit_eigenmultiplier_iff_quadratic33 ((τ : ℂ) • u) z v).mpr hv
    exact (ne_of_gt hz)
      (actualPhysicalUnitFloquetMultiplier_im_eq_zero33 ((τ : ℂ) • u) z v w hw hn he)
  have hc : Continuous (fun τ : Set.Icc (0 : ℝ) 1 => r τ) :=
    complexQuadraticSmallRoot_continuous36V2
      (fun τ : Set.Icc (0 : ℝ) 1 => d τ)
      (fun τ : Set.Icc (0 : ℝ) 1 => r τ) hd
      (fun τ => (hr τ).1) (fun τ => (hr τ).2) hb
  exact ⟨r, continuousOn_iff_continuous_restrict.mpr hc, fun τ _ => hr τ⟩
end NlsGge.SpectralFoundations
end
