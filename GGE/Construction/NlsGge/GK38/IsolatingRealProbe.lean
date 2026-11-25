import NlsGge.GK38.IsolatingRealSpectral
import NlsGge.GK38.IsolatingPrerequisiteProbe

/-! The FULL free isolating family and a repeated negative pair, with actual
Neumann normalization. These use the complete four-spectrum real certificate. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem isolating_free_gap_endpoints38 (n : ℤ) :
    actualGapLowerAllE02_38 (0 : PhysicalL2) n = (n : ℝ) * Real.pi ∧
      actualGapUpperAllE02_38 (0 : PhysicalL2) n = (n : ℝ) * Real.pi := by
  have hl := congrArg Complex.re (lamPlus_real (0 : PhysicalL2) n).2
  have hu := congrArg Complex.re (lamPlus_real (0 : PhysicalL2) n).1
  simp only [realSlice_zero, lamMinus_zero38, lamPlus_zero38, countingCenter_re38,
    Complex.ofReal_re] at hl hu
  exact ⟨hl.symm, hu.symm⟩

theorem isolating_free_family_probe38 :
    IsolatingFamily38 (0 : PotPair) countingCenter38 (fun _ => Real.pi / 4) := by
  obtain ⟨c, hgeom⟩ := isolating_lattice_geometry_probe38
  have hgap : ∀ n : ℤ, Icc (actualGapLowerAllE02_38 (0 : PhysicalL2) n)
      (actualGapUpperAllE02_38 (0 : PhysicalL2) n) ⊆
      {x : ℝ | (x : ℂ) ∈ ball (countingCenter38 n) (Real.pi / 4)} := by
    intro n x hx
    rw [(isolating_free_gap_endpoints38 n).1, (isolating_free_gap_endpoints38 n).2] at hx
    have he : x = (n : ℝ) * Real.pi := le_antisymm hx.2 hx.1
    change (x : ℂ) ∈ ball (countingCenter38 n) (Real.pi / 4)
    rw [he]
    have hc : (((n : ℝ) * Real.pi : ℝ) : ℂ) = countingCenter38 n := by simp [countingCenter38]
    rw [hc]
    exact mem_ball_self (by positivity)
  have hs := real_spectral_of_gap_circles38 0 countingCenter38 (fun _ => Real.pi / 4) c 0 hgeom hgap
  exact ⟨c, 0, hgeom, by simpa only [realSlice_zero] using hs⟩

theorem isolating_repeated_negative_probe38 :
    (lamMinus 0 (-1) ::ₘ lamPlus 0 (-1) ::ₘ 0) = ({-(Real.pi : ℂ), -(Real.pi : ℂ)} : Multiset ℂ) ∧
      (Lib.zeroMultiset (perChar 0) (ball (countingCenter38 (-1)) (Real.pi / 4))).card = 2 ∧
      neumannChar38 0 (-(Real.pi : ℂ)) = 0 := by
  obtain ⟨c, N, _, hs⟩ := isolating_free_family_probe38
  refine ⟨?_, (hs.1 (-1)).2.2.2.2.2.2.2.2.1, ?_⟩
  · simp only [lamMinus_zero38, lamPlus_zero38, countingCenter38]
    norm_num
  · rw [neumannChar38_zero]
    simp

theorem isolating_nonfree_full_family_probe38 :
    ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, IsolatingFamily38 (realSlice (constL2 1)) C R :=
  real_center_spectral38 (constL2 1)

end
end NlsGge.GK38
