import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.IsolatingGeometry

/-! The actual certified real-centred circle deformation avoids every complex gap cut.
This is a geometric prerequisite, not a contour-integral identity. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def contourCenter38 (C0 C1 : ℤ → ℂ) (n : ℤ) (t : ℝ) : ℂ :=
  (1 - t) • C0 n + t • C1 n

def contourRadius38 (R0 R1 : ℤ → ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1 - t) * R0 n + t * R1 n

theorem contour_combo_lt38 {x0 x1 y0 y1 t : ℝ}
    (h0 : x0 < y0) (h1 : x1 < y1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) * x0 + t * x1 < (1 - t) * y0 + t * y1 := by
  by_cases hzero : t = 0
  · simpa only [hzero, sub_zero, one_mul, zero_mul, add_zero] using h0
  · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    exact add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left h0.le (sub_nonneg.mpr ht.2))
      (mul_lt_mul_of_pos_left h1 hp)

theorem contour_radius_pos38 (R0 R1 : ℤ → ℝ) (n : ℤ) (t : ℝ)
    (h0 : 0 < R0 n) (h1 : 0 < R1 n) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < contourRadius38 R0 R1 n t := by
  simpa only [contourRadius38, mul_zero, add_zero] using
    contour_combo_lt38 h0 h1 ht

theorem contour_own_ball38 {c0 c1 z : ℂ} {r0 r1 t : ℝ}
    (h0 : z ∈ ball c0 r0) (h1 : z ∈ ball c1 r1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    z ∈ ball ((1 - t) • c0 + t • c1) ((1 - t) * r0 + t * r1) := by
  rw [mem_ball_iff_norm] at h0 h1 ⊢
  have he : z - ((1 - t) • c0 + t • c1) =
      (1 - t) • (z - c0) + t • (z - c1) := by module
  rw [he]
  calc
    _ ≤ ‖(1 - t) • (z - c0)‖ + ‖t • (z - c1)‖ := norm_add_le _ _
    _ = (1 - t) * ‖z - c0‖ + t * ‖z - c1‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2),
        Real.norm_of_nonneg ht.1]
    _ < _ := contour_combo_lt38 h0 h1 ht

theorem contour_left_bound38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (h : IsolatingGeometry38 C R c N) {m n : ℤ} (hmn : m < n) {z : ℂ}
    (hz : z ∈ ball (C m) (R m)) : z.re < (C n).re - R n := by
  have hsep := isolating_geometry_closure_separated38 C R c N h m n (ne_of_lt hmn)
  have hc := h.2.1 hmn
  rw [dist_eq_norm, realType_norm_sub_real38 _ _ (h.1 m).2 (h.1 n).2,
    abs_of_neg (sub_neg.mpr hc)] at hsep
  have hz' : |z.re - (C m).re| < R m :=
    (Complex.abs_re_le_norm (z - C m)).trans_lt (mem_ball_iff_norm.mp hz)
  have hza := (abs_lt.mp hz').2
  linarith

theorem contour_right_bound38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (h : IsolatingGeometry38 C R c N) {m n : ℤ} (hnm : n < m) {z : ℂ}
    (hz : z ∈ ball (C m) (R m)) : (C n).re + R n < z.re := by
  have hsep := isolating_geometry_closure_separated38 C R c N h n m (ne_of_lt hnm)
  have hc := h.2.1 hnm
  rw [dist_eq_norm, realType_norm_sub_real38 _ _ (h.1 n).2 (h.1 m).2,
    abs_of_neg (sub_neg.mpr hc)] at hsep
  have hz' : |z.re - (C m).re| < R m :=
    (Complex.abs_re_le_norm (z - C m)).trans_lt (mem_ball_iff_norm.mp hz)
  have hza := (abs_lt.mp hz').1
  linarith

theorem contour_segment_inside38 (φ : PotPair) (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆
      ball (contourCenter38 C0 C1 n t) (contourRadius38 R0 R1 n t) := by
  obtain ⟨c0, N0, _, hs0⟩ := h0
  obtain ⟨c1, N1, _, hs1⟩ := h1
  intro z hz
  exact contour_own_ball38 ((hs0.1 n).1 hz) ((hs1.1 n).1 hz) ht

theorem contour_sphere_avoids_cuts38 (φ : PotPair) (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ z ∈ sphere (contourCenter38 C0 C1 n t) (contourRadius38 R0 R1 n t),
      z ∉ gapSegments38 φ := by
  intro z hz hcut
  obtain ⟨c0, N0, hg0, hs0⟩ := h0
  obtain ⟨c1, N1, hg1, hs1⟩ := h1
  obtain ⟨m, hzm⟩ := mem_iUnion.mp hcut
  have hb0 := (hs0.1 m).1 hzm
  have hb1 := (hs1.1 m).1 hzm
  have hnorm := mem_sphere_iff_norm.mp hz
  have hre : |z.re - (contourCenter38 C0 C1 n t).re| ≤ contourRadius38 R0 R1 n t := by
    simpa only [Complex.sub_re, hnorm] using Complex.abs_re_le_norm (z - contourCenter38 C0 C1 n t)
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hl0 := contour_left_bound38 C0 R0 c0 N0 hg0 hmn hb0
    have hl1 := contour_left_bound38 C1 R1 c1 N1 hg1 hmn hb1
    have hl := contour_combo_lt38 hl0 hl1 ht
    have hcalc : (1 - t) * z.re + t * z.re = z.re := by ring
    rw [hcalc] at hl
    have hc : (contourCenter38 C0 C1 n t).re =
        (1 - t) * (C0 n).re + t * (C1 n).re := by
      simp only [contourCenter38, Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [abs_le] at hre
    unfold contourRadius38 at hre
    rw [hc] at hre
    nlinarith [hre.1]
  · subst m
    have hb := contour_own_ball38 hb0 hb1 ht
    have hlt := mem_ball_iff_norm.mp hb
    exact (ne_of_lt hlt) hnorm
  · have hr0 := contour_right_bound38 C0 R0 c0 N0 hg0 hnm hb0
    have hr1 := contour_right_bound38 C1 R1 c1 N1 hg1 hnm hb1
    have hr := contour_combo_lt38 hr0 hr1 ht
    have hcalc : (1 - t) * z.re + t * z.re = z.re := by ring
    rw [hcalc] at hr
    have hc : (contourCenter38 C0 C1 n t).re =
        (1 - t) * (C0 n).re + t * (C1 n).re := by
      simp only [contourCenter38, Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [abs_le] at hre
    unfold contourRadius38 at hre
    rw [hc] at hre
    nlinarith [hre.2]

theorem contour_geometry38 (φ : PotPair) (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < contourRadius38 R0 R1 n t ∧
    segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆
      ball (contourCenter38 C0 C1 n t) (contourRadius38 R0 R1 n t) ∧
    (∀ z ∈ sphere (contourCenter38 C0 C1 n t) (contourRadius38 R0 R1 n t),
      z ∉ gapSegments38 φ) := by
  have h0copy := h0
  have h1copy := h1
  obtain ⟨c0, N0, hg0, _⟩ := h0
  obtain ⟨c1, N1, hg1, _⟩ := h1
  exact ⟨contour_radius_pos38 R0 R1 n t (hg0.1 n).1 (hg1.1 n).1 ht,
    contour_segment_inside38 φ C0 C1 R0 R1 h0copy h1copy n t ht,
    contour_sphere_avoids_cuts38 φ C0 C1 R0 R1 h0copy h1copy n t ht⟩

end
end NlsGge.GK38
