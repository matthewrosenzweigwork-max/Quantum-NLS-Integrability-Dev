import NlsGge.GK38.AbelianDirectionSeries

/-! The source interpolation function multiplies the genuine variation by
sigma_n-z. Earn its counting-circle bound before direction-tail approximation. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem sigma_counting_norm_ratio (n : ℤ) (s : Lib.L2Seq) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, ∀ z : ℂ,
      ‖z‖=N*Real.pi+Real.pi/2 →
      ‖Lib.sigmaOf s n-z‖ ≤ B*‖z-(n : ℂ)*(Real.pi : ℂ)‖ := by
  let B : ℝ := 1+2*‖s n‖/Real.pi
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro N z hz
  let d : ℝ := ‖z-(n : ℂ)*(Real.pi : ℂ)‖
  have hd : Real.pi/2 ≤ d := by
    have h1 := Lib.pi_mul_dd_le hz n
    have h2 := Lib.half_le_circDist N n
    rw [norm_sub_rev] at h1
    dsimp [d]
    nlinarith [Real.pi_pos]
  have hs : ‖s n‖ ≤ (2*‖s n‖/Real.pi)*d := by
    have he : (2*‖s n‖/Real.pi)*d=(2*‖s n‖*d)/Real.pi := by ring
    rw [he]
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [mul_nonneg (norm_nonneg (s n)) (sub_nonneg.mpr hd)]
  have he : Lib.sigmaOf s n-z=((n : ℂ)*(Real.pi : ℂ)-z)+s n := by
    unfold Lib.sigmaOf
    ring
  calc
    _ ≤ d+‖s n‖ := by
      rw [he]
      simpa only [d,norm_sub_rev] using
        (norm_add_le ((n : ℂ)*(Real.pi : ℂ)-z) (s n))
    _ ≤ d+(2*‖s n‖/Real.pi)*d := add_le_add le_rfl hs
    _ = B*d := by dsimp [B];ring

theorem variation_weighted_circle_bound (n : ℤ) (s : Lib.L2Seq) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : Lib.L2Seq, ∀ N : ℕ, ∀ z : ℂ,
      ‖z‖=N*Real.pi+Real.pi/2 →
      ‖p4NumeratorVariation38 n s h z‖*‖Lib.sigmaOf s n-z‖ ≤
        C*‖h‖*‖Complex.sin z‖ := by
  obtain ⟨C,hC,hbound⟩ := variation_counting_circle_bound ‖s‖
  obtain ⟨B,hB,hratio⟩ := sigma_counting_norm_ratio n s
  refine ⟨B*C,mul_pos hB hC,?_⟩
  intro h N z hz
  calc
    _ ≤ ‖p4NumeratorVariation38 n s h z‖*(B*‖z-(n : ℂ)*(Real.pi : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (hratio N z hz) (norm_nonneg _)
    _ = B*(‖p4NumeratorVariation38 n s h z‖*‖z-(n : ℂ)*(Real.pi : ℂ)‖) := by ring
    _ ≤ B*(C*‖h‖*‖Complex.sin z‖) :=
      mul_le_mul_of_nonneg_left (hbound s le_rfl h n N z hz) hB.le
    _ = _ := by ring

end
end NlsGge.GK38.P4NumeratorVariation
