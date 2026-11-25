import NlsGge.GK38.TauGamma
import NlsGge.GK38.Lib.Rouche

/-! Concrete local quotient bounds on each exceptional fixed isolating circle.
Only the spectral circle is compact; the potential space remains complex L2. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem k4aQuotient_local_bound38 (φ₀ : PotPair) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hne : ∀ z ∈ sphere c r, perChar φ₀ z ≠ 0) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ z ∈ sphere c r,
        perChar φ z ≠ 0 ∧ ‖discrim φ z / perChar φ z‖ ≤ B := by
  have hpcont : ContinuousOn (fun p : PotPair × ℂ => perChar p.1 p.2)
      (univ ×ˢ sphere c r) :=
    analyticOnNhd_perChar_joint38.continuousOn.mono (subset_univ _)
  have hdcont : ContinuousOn (fun p : PotPair × ℂ => discrim p.1 p.2)
      (univ ×ˢ sphere c r) :=
    analyticOnNhd_discrim.continuousOn.mono (subset_univ _)
  obtain ⟨m, hm, hmin⟩ := Lib.exists_pos_le_norm_sphere hr
    ((analyticOnNhd_perChar_z φ₀).continuousOn.mono (subset_univ _)) hne
  obtain ⟨M, hM⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn
    ((analyticOnNhd_discrim_z φ₀).continuousOn.mono (subset_univ _))
  have heP := Lib.eventually_forall_sphere_norm_sub_lt
    (F := fun φ z => perChar φ z) hpcont φ₀ (half_pos hm)
  have heD := Lib.eventually_forall_sphere_norm_sub_lt
    (F := fun φ z => discrim φ z) hdcont φ₀ zero_lt_one
  let A : ℝ := max M 0 + 1
  let B : ℝ := A / (m / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := div_nonneg hA (half_pos hm).le
  refine ⟨{φ | (∀ z ∈ sphere c r, ‖perChar φ z - perChar φ₀ z‖ < m / 2) ∧
      (∀ z ∈ sphere c r, ‖discrim φ z - discrim φ₀ z‖ < 1)},
    inter_mem heP heD, B, hB, ?_⟩
  intro φ hφ z hz
  have htriP : ‖perChar φ₀ z‖ ≤ ‖perChar φ z - perChar φ₀ z‖ + ‖perChar φ z‖ := by
    simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le (perChar φ₀ z - perChar φ z) (perChar φ z)
  have hden : m / 2 ≤ ‖perChar φ z‖ := by
    linarith [hmin z hz, hφ.1 z hz]
  have hpos : 0 < ‖perChar φ z‖ := (half_pos hm).trans_le hden
  have htriD : ‖discrim φ z‖ ≤ ‖discrim φ z - discrim φ₀ z‖ + ‖discrim φ₀ z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (discrim φ z - discrim φ₀ z) (discrim φ₀ z)
  have hnum : ‖discrim φ z‖ ≤ A := by
    have hmz := hM z hz
    have hclose := hφ.2 z hz
    dsimp [A]
    linarith [le_max_left M 0]
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [norm_div]
  apply (div_le_iff₀ hpos).mpr
  calc
    _ ≤ A := hnum
    _ = B * (m / 2) := by dsimp [B]; field_simp
    _ ≤ B * ‖perChar φ z‖ := mul_le_mul_of_nonneg_left hden hB

end
end NlsGge.GK38
