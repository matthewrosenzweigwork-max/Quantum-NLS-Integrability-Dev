import QuantumNLS.LOCAL009R22ScalarContour

/-! Elementary geometry of the literal source rectangles. The open band
below contains the contour and disks of the radius used in Cauchy's estimate.
Its constants and estimates are independent of the integer translation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Complex Set Metric
namespace QuantumNLS.LOCAL009R22Geometry
open QuantumNLS.PeriodReconstruction

def band (p a : ℝ) : Set ℂ :=
  {z | 7*a/8 < max |z.re-p| |z.im| ∧ max |z.re-p| |z.im| < 9*a/8}

theorem band_open (p a : ℝ) : IsOpen (band p a) := by
  have hc : Continuous (fun z : ℂ => max |z.re-p| |z.im|) := by fun_prop
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

theorem contour_max {p a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ Gam (p-a) (p+a) a) : max |z.re-p| |z.im| = a := by
  rcases hz with ⟨⟨hl, hr⟩, hi⟩ | ⟨⟨hl, hr⟩, he⟩
  · have hreal : |z.re-p| ≤ a := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |z.im| = a := by rcases hi with hi | hi <;> rw [hi] <;> simp [ha.le]
    rw [him, max_eq_right hreal]
  · have him : |z.im| ≤ a := abs_le.mpr ⟨hl, hr⟩
    have hre : |z.re-p| = a := by
      rcases he with he | he <;> rw [he] <;> simp [ha.le]
    rw [hre, max_eq_left him]

theorem contour_ball_subset_band {p a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ Gam (p-a) (p+a) a) : closedBall z (a/16) ⊆ band p a := by
  intro w hw
  have hn : ‖w-z‖ ≤ a/16 := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hre := Complex.abs_re_le_norm (w-z)
  have him := Complex.abs_im_le_norm (w-z)
  simp only [sub_re, sub_im] at hre him
  have h1 : |w.re-p| ≤ |z.re-p| + ‖w-z‖ := by
    have h := abs_add_le (w.re-z.re) (z.re-p)
    rw [sub_add_sub_cancel] at h
    linarith
  have h2 : |z.re-p| ≤ |w.re-p| + ‖w-z‖ := by
    have h := abs_add_le (z.re-w.re) (w.re-p)
    rw [sub_add_sub_cancel, abs_sub_comm z.re w.re] at h
    linarith
  have h3 : |w.im| ≤ |z.im| + ‖w-z‖ := by
    have h := abs_add_le (w.im-z.im) z.im
    rw [sub_add_cancel] at h
    linarith
  have h4 : |z.im| ≤ |w.im| + ‖w-z‖ := by
    have h := abs_add_le (z.im-w.im) w.im
    rw [sub_add_cancel, abs_sub_comm z.im w.im] at h
    linarith
  have hmax := contour_max ha hz
  have hu : max |w.re-p| |w.im| ≤ a + ‖w-z‖ := by
    apply max_le
    · linarith [le_max_left |z.re-p| |z.im|]
    · linarith [le_max_right |z.re-p| |z.im|]
  have hl : a ≤ max |w.re-p| |w.im| + ‖w-z‖ := by
    rw [← hmax]
    apply max_le
    · linarith [le_max_left |w.re-p| |w.im|]
    · linarith [le_max_right |w.re-p| |w.im|]
  constructor <;> nlinarith

/-- All root clusters, including arbitrarily distant labels, are separated
from the band. The input is the source confinement bound in grid units. -/
theorem band_root_separation {p a q : ℝ} (ha : 0 < a)
    (hq : ∃ k : ℤ, |q - (p + 4*a*k)| ≤ a/4) {z : ℂ} (hz : z ∈ band p a) :
    a/2 ≤ ‖z - (q : ℂ)‖ := by
  rcases hq with ⟨k, hk⟩
  rcases lt_max_iff.mp hz.1 with hre | him
  · have hu : |z.re-p| < 9*a/8 := (le_max_left _ _).trans_lt hz.2
    have hdist : a/2 ≤ |z.re-q| := by
      by_cases hzero : k = 0
      · subst k
        simp only [Int.cast_zero, mul_zero, add_zero] at hk
        have ht := abs_add_le (z.re-q) (q-p)
        rw [sub_add_sub_cancel] at ht
        linarith
      · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
          have hi : (1 : ℤ) ≤ |k| := by
            have hkpos : (0 : ℤ) < |k| := abs_pos.mpr hzero
            omega
          exact_mod_cast hi
        have hlarge : 4*a ≤ |4*a*(k : ℝ)| := by
          rw [abs_mul, abs_of_pos (by positivity : 0 < 4*a)]
          nlinarith
        have ht : |4*a*(k : ℝ)| ≤ |q-(p+4*a*k)| + |z.re-p| + |z.re-q| := by
          have h1 := abs_add_le (q-(p+4*a*k)) (z.re-q)
          have h2 := abs_sub (z.re-p) ((q-(p+4*a*k)) + (z.re-q))
          have heq : (z.re-p) - ((q-(p+4*a*k)) + (z.re-q)) = 4*a*(k : ℝ) := by ring
          rw [heq] at h2
          linarith
        linarith
    exact hdist.trans (by simpa using Complex.abs_re_le_norm (z-(q : ℂ)))
  · have hi : a/2 ≤ |z.im| := by linarith
    exact hi.trans (by simpa using Complex.abs_im_le_norm (z-(q : ℂ)))

theorem source_phase_bound {L : ℝ} (hL : 0 < L) (n : ℤ) {z : ℂ}
    (hz : z ∈ band (2*Real.pi*n/L) (Real.pi/(2*L))) :
    ‖Complex.exp (I * z * L)‖ ≤ 8 := by
  have hi := (le_max_right _ _).trans_lt hz.2
  have hib : -z.im * L < 2 := by
    have h1 := mul_lt_mul_of_pos_right hi hL
    have h2 : 9 * (Real.pi/(2*L)) / 8 * L = 9*Real.pi/16 := by field_simp; ring
    rw [h2] at h1
    nlinarith [neg_le_abs z.im, Real.pi_lt_d2]
  have hexp2 : Real.exp 2 < 8 := by
    have he := Real.exp_one_lt_d9
    have hepos := Real.exp_pos 1
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    rw [heq]
    nlinarith
  rw [Complex.norm_exp]
  have heq : (I * z * (L : ℂ)).re = -z.im * L := by simp
  rw [heq]
  exact ((Real.exp_lt_exp.mpr hib).trans hexp2).le

theorem source_gap_bound {L : ℝ} (hL : 0 < L) (n : ℤ) {z : ℂ}
    (hz : z ∈ band (2*Real.pi*n/L) (Real.pi/(2*L))) :
    1/2 ≤ ‖1 - Complex.exp (I * z * L)‖ := by
  let a := Real.pi/(2*L)
  let p := 2*Real.pi*n/L
  let e := Complex.exp (I*z*L)
  have haL : a*L = Real.pi/2 := by dsimp [a]; field_simp
  have hnorm : ‖e‖ = Real.exp (-z.im*L) := by
    dsimp [e]
    rw [Complex.norm_exp]
    congr 1
    simp
  rcases lt_max_iff.mp hz.1 with hre | him
  · have hu : |z.re-p| < 9*a/8 := (le_max_left _ _).trans_lt hz.2
    let θ := (z.re-p)*L
    have hθ : |θ| = |z.re-p| *L := by dsimp [θ]; rw [abs_mul, abs_of_pos hL]
    have hlo : Real.pi/3 ≤ |θ| := by
      have h := mul_lt_mul_of_pos_right hre hL
      change 7*a/8*L < |z.re-p| *L at h
      rw [← hθ] at h
      nlinarith [Real.pi_pos]
    have hhi : |θ| ≤ Real.pi := by
      have h := mul_lt_mul_of_pos_right hu hL
      rw [← hθ] at h
      nlinarith [Real.pi_pos]
    have hcos : Real.cos θ ≤ 1/2 := by
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ Real.pi/3 by positivity) hhi hlo
      simpa only [Real.cos_abs, Real.cos_pi_div_three] using hc
    have hangle : z.re*L = θ + (n : ℝ)*(2*Real.pi) := by
      dsimp [θ, p]
      field_simp
      ring
    have hreal : e.re ≤ ‖e‖/2 := by
      dsimp [e]
      rw [Complex.exp_re]
      have h1 : (I*z*(L : ℂ)).re = -z.im*L := by simp
      have h2 : (I*z*(L : ℂ)).im = z.re*L := by simp
      rw [h1, h2, hangle, Real.cos_add_int_mul_two_pi]
      rw [hnorm]
      nlinarith [mul_le_mul_of_nonneg_left hcos (Real.exp_pos (-z.im*L)).le]
    have hs : ‖(1 : ℂ)-e‖^2 = 1 + ‖e‖^2 - 2*e.re := by
      simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, one_re, one_im]
      ring
    have hn := norm_nonneg ((1 : ℂ)-e)
    nlinarith [sq_nonneg (‖e‖-1/2)]
  · have himL : 1 < |z.im| *L := by
      have h := mul_lt_mul_of_pos_right him hL
      change 7*a/8*L < |z.im| *L at h
      nlinarith [Real.pi_gt_three]
    by_cases hi : 0 ≤ z.im
    · rw [abs_of_nonneg hi] at himL
      have he : 2 < Real.exp (z.im*L) :=
        Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr himL)
      have hn : ‖e‖ < 1/2 := by
        rw [hnorm, neg_mul, Real.exp_neg]
        exact (inv_lt_iff_one_lt_mul₀ (Real.exp_pos _)).mpr (by linarith)
      have h := norm_sub_norm_le (1 : ℂ) e
      simp only [norm_one] at h
      linarith
    · have hneg : z.im < 0 := lt_of_not_ge hi
      rw [abs_of_neg hneg] at himL
      have he : 2 < ‖e‖ := by
        rw [hnorm]
        exact Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr himL)
      have h := norm_sub_norm_le e (1 : ℂ)
      rw [norm_one, norm_sub_rev] at h
      linarith

end QuantumNLS.LOCAL009R22Geometry
#print axioms QuantumNLS.LOCAL009R22Geometry.band_open
#print axioms QuantumNLS.LOCAL009R22Geometry.contour_ball_subset_band
#print axioms QuantumNLS.LOCAL009R22Geometry.band_root_separation
#print axioms QuantumNLS.LOCAL009R22Geometry.source_phase_bound
#print axioms QuantumNLS.LOCAL009R22Geometry.source_gap_bound
