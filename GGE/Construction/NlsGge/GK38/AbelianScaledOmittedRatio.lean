import NlsGge.GK38.AbelianHilbert

/-! UNCOMPILED fixed-contour scalar asymptotic. Positive indices suffice for
constructing the full-period Hilbert map. This does not replace the later
SIGNED compact-uniform operator-norm target. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def p6ScaleRatio38 (k : ℕ) (m : ℤ) (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  (((k : ℂ)-(m : ℂ))*(Real.pi : ℂ))/(Lib.sigmaOf s (k : ℤ)-z)

theorem p6ScaleRatio_error_bound38 (k : ℕ) (hk : 0 < k) (m : ℤ)
    (s : Lib.L2Seq) (z : ℂ) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hs : ‖s‖ ≤ A) (hz : ‖z‖ ≤ D)
    (hfar : 2*(A+D) ≤ (k : ℝ)*Real.pi) :
    Lib.sigmaOf s (k : ℤ)-z ≠ 0 ∧
      ‖p6ScaleRatio38 k m s z-1‖ ≤
        2*(A+D+|(m : ℝ)| *Real.pi)/((k : ℝ)*Real.pi) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < (k : ℝ)*Real.pi := mul_pos hkR Real.pi_pos
  have hsn : ‖s (k : ℤ)‖ ≤ A :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) s (k : ℤ)).trans hs
  have hcenter : ‖(k : ℂ)*(Real.pi : ℂ)‖ = (k : ℝ)*Real.pi := by
    rw [norm_mul,Complex.norm_natCast,Complex.norm_of_nonneg Real.pi_pos.le]
  have hid : (Lib.sigmaOf s (k : ℤ)-z)+(z-s (k : ℤ))=
      (k : ℂ)*(Real.pi : ℂ) := by
    dsimp [Lib.sigmaOf]
    push_cast
    ring
  have htri := norm_add_le (Lib.sigmaOf s (k : ℤ)-z) (z-s (k : ℤ))
  rw [hid,hcenter] at htri
  have hzs : ‖z-s (k : ℤ)‖ ≤ D+A := (norm_sub_le _ _).trans (add_le_add hz hsn)
  have hlower : ((k : ℝ)*Real.pi)/2 ≤ ‖Lib.sigmaOf s (k : ℤ)-z‖ := by linarith
  have hdenpos : 0 < ‖Lib.sigmaOf s (k : ℤ)-z‖ := (half_pos hL).trans_le hlower
  have hden : Lib.sigmaOf s (k : ℤ)-z ≠ 0 := norm_pos_iff.mp hdenpos
  have hmcenter : ‖(m : ℂ)*(Real.pi : ℂ)‖ = |(m : ℝ)| *Real.pi := by
    rw [norm_mul,Complex.norm_intCast,Complex.norm_of_nonneg Real.pi_pos.le]
  have hzm : ‖z-(m : ℂ)*(Real.pi : ℂ)‖ ≤ D+|(m : ℝ)| *Real.pi := by
    exact (norm_sub_le _ _).trans (by rw [hmcenter]; exact add_le_add hz le_rfl)
  have hnum : ‖z-(m : ℂ)*(Real.pi : ℂ)-s (k : ℤ)‖ ≤
      A+D+|(m : ℝ)| *Real.pi := by
    have hh := (norm_sub_le (z-(m : ℂ)*(Real.pi : ℂ)) (s (k : ℤ))).trans
      (add_le_add hzm hsn)
    linarith
  have he : p6ScaleRatio38 k m s z-1 =
      (z-(m : ℂ)*(Real.pi : ℂ)-s (k : ℤ))/(Lib.sigmaOf s (k : ℤ)-z) := by
    unfold p6ScaleRatio38
    field_simp [hden]
    dsimp [Lib.sigmaOf]
    push_cast
    ring
  have hM : 0 ≤ A+D+|(m : ℝ)| *Real.pi := by positivity
  refine ⟨hden,?_⟩
  rw [he,norm_div]
  calc
    _ ≤ (A+D+|(m : ℝ)| *Real.pi)/‖Lib.sigmaOf s (k : ℤ)-z‖ :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (A+D+|(m : ℝ)| *Real.pi)/(((k : ℝ)*Real.pi)/2) :=
      div_le_div_of_nonneg_left hM (half_pos hL) hlower
    _ = 2*(A+D+|(m : ℝ)| *Real.pi)/((k : ℝ)*Real.pi) := by ring

theorem p6ScaleRatio_uniform_bounded_set38 (m : ℤ) (s : Lib.L2Seq)
    (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ D →
      Lib.sigmaOf s (k : ℤ)-z ≠ 0 ∧ ‖p6ScaleRatio38 k m s z-1‖ < ε := by
  let A : ℝ := ‖s‖
  let M : ℝ := A+D+|(m : ℝ)| *Real.pi
  have hA : 0 ≤ A := norm_nonneg _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpε : 0 < Real.pi*ε := mul_pos Real.pi_pos hε
  have hfirst : 0 ≤ 2*(A+D)/Real.pi := div_nonneg (by positivity) Real.pi_pos.le
  have hsecond : 0 ≤ 2*M/(Real.pi*ε) := div_nonneg (by positivity) hpε.le
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(A+D)/Real.pi+2*M/(Real.pi*ε)+1)
  refine ⟨N,?_⟩
  intro k hk z hz
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkR : 0 < (k : ℝ) := by linarith
  have hk0 : 0 < k := by exact_mod_cast hkR
  have hfar' : 2*(A+D)/Real.pi < (k : ℝ) := by linarith
  have hfar : 2*(A+D) ≤ (k : ℝ)*Real.pi :=
    ((div_lt_iff₀ Real.pi_pos).mp hfar').le
  have hsmall' : 2*M/(Real.pi*ε) < (k : ℝ) := by linarith
  have hsmall : 2*M/((k : ℝ)*Real.pi) < ε := by
    apply (div_lt_iff₀ (mul_pos hkR Real.pi_pos)).mpr
    have hh := (div_lt_iff₀ hpε).mp hsmall'
    nlinarith
  obtain ⟨hd,he⟩ := p6ScaleRatio_error_bound38 k hk0 m s z A D hA hD le_rfl hz hfar
  exact ⟨hd,he.trans_lt hsmall⟩

end
end NlsGge.GK38
