import Mathlib
import NlsGge.Atomic.LIB.LIB079

/- M-008 SUPPORT E2a (proof development, AUTHOR; not reviewed).  Polygonal connectedness of the cut isolating disc
   `D.domain = ball \ segment` of a `DiscWithSegment` (hypothesis-free), needed to build a primitive of `omega` on it. -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- Signed coordinate transverse to the line through the segment. -/
def lineCoord (D : DiscWithSegment) (z : ℂ) : ℝ := (star D.axis * (z - D.midpoint)).im

theorem lineCoord_comb (D : DiscWithSegment) {a b : ℝ} (hab : a + b = 1) (x y : ℂ) :
    lineCoord D (a • x + b • y) = a * lineCoord D x + b * lineCoord D y := by
  unfold lineCoord
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  have h : star D.axis * (a • x + b • y - D.midpoint) =
      (a : ℂ) * (star D.axis * (x - D.midpoint)) + (b : ℂ) * (star D.axis * (y - D.midpoint)) := by
    simp only [Complex.real_smul]
    linear_combination (star D.axis * D.midpoint) * hab'
  rw [h, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]

theorem lineCoord_seg (D : DiscWithSegment) {z : ℂ} (hz : z ∈ segment ℝ D.a D.b) :
    lineCoord D z = 0 := by
  obtain ⟨-, -, -, hseg⟩ := disc_segment_coordinates D
  rw [hseg] at hz
  obtain ⟨t, -, rfl⟩ := hz
  unfold lineCoord
  have : star D.axis * (D.midpoint + D.axis * (t : ℂ) - D.midpoint) = (t : ℂ) := by
    linear_combination (t : ℂ) * star_axis_mul D
  rw [this, Complex.ofReal_im]

theorem mem_domain_of_lineCoord_ne (D : DiscWithSegment) {z : ℂ}
    (hz : z ∈ ball D.center D.radius) (h : lineCoord D z ≠ 0) : z ∈ D.domain :=
  ⟨hz, fun hs => h (lineCoord_seg D hs)⟩

theorem segment_subset_domain_of_lineCoord (D : DiscWithSegment) {x y : ℂ}
    (hx : x ∈ D.domain) (hy : y ∈ ball D.center D.radius)
    (h : (0 ≤ lineCoord D x ∧ 0 < lineCoord D y) ∨ (lineCoord D x ≤ 0 ∧ lineCoord D y < 0)) :
    segment ℝ x y ⊆ D.domain := by
  rintro p ⟨a, b, ha, hb, hab, rfl⟩
  have hball : a • x + b • y ∈ ball D.center D.radius :=
    (convex_ball D.center D.radius) hx.1 hy ha hb hab
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have ha1 : a = 1 := by linarith
    rw [← hb0, ha1]; simpa using hx
  · refine mem_domain_of_lineCoord_ne D hball ?_
    rw [lineCoord_comb D hab]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : 0 < a * lineCoord D x + b * lineCoord D y := by
        have := mul_nonneg ha h1
        have := mul_pos hbpos h2
        linarith
      exact this.ne'
    · have : a * lineCoord D x + b * lineCoord D y < 0 := by
        have := mul_nonpos_of_nonneg_of_nonpos ha h1
        have := mul_neg_of_pos_of_neg hbpos h2
        linarith
      exact this.ne

theorem domain_polygonal (D : DiscWithSegment) :
    ∀ z ∈ D.domain, ∀ w ∈ D.domain,
      Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ D.domain) z w := by
  obtain ⟨-, -, hu, hseg⟩ := disc_segment_coordinates D
  have hL : 0 ≤ D.halfLength := by unfold DiscWithSegment.halfLength; positivity
  have hstar := star_axis_mul D
  set u := D.axis with hu_def
  set m := D.midpoint with hm_def
  set L := D.halfLength with hL_def
  set P0 : ℂ := m + u * ((-L : ℝ) : ℂ) with hP0
  have hP0seg : P0 ∈ segment ℝ D.a D.b := by
    rw [hseg]; exact ⟨-L, ⟨le_refl _, by linarith⟩, rfl⟩
  have hP0ball : P0 ∈ ball D.center D.radius := D.contained hP0seg
  set r0 : ℝ := D.radius - dist P0 D.center with hr0
  have hr0pos : 0 < r0 := by have := mem_ball.1 hP0ball; rw [hr0]; linarith
  have hsub : ball P0 r0 ⊆ ball D.center D.radius := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z P0 D.center
    rw [hr0] at hz; linarith
  have hu1 : ‖u‖ = 1 := hu
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu1; simp at hu1
  -- three base points
  set uu : ℂ := P0 + Complex.I * u * ((r0 / 2 : ℝ) : ℂ) with huu
  set ll : ℂ := P0 - Complex.I * u * ((r0 / 2 : ℝ) : ℂ) with hll
  set q : ℂ := P0 - u * ((r0 / 2 : ℝ) : ℂ) with hq
  have hdist : ∀ v : ℂ, ‖v‖ = 1 → dist (P0 + v * ((r0 / 2 : ℝ) : ℂ)) P0 < r0 := by
    intro v hv
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, hv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr0pos)]
    linarith
  have hnI : ‖Complex.I * u‖ = 1 := by rw [norm_mul, hu1]; simp
  have huuball : uu ∈ ball D.center D.radius := hsub (mem_ball.2 (hdist _ hnI))
  have hllball : ll ∈ ball D.center D.radius := by
    refine hsub (mem_ball.2 ?_)
    have : ll = P0 + (-(Complex.I * u)) * ((r0 / 2 : ℝ) : ℂ) := by rw [hll]; ring
    rw [this]; exact hdist _ (by rw [norm_neg]; exact hnI)
  have hqball : q ∈ ball D.center D.radius := by
    refine hsub (mem_ball.2 ?_)
    have : q = P0 + (-u) * ((r0 / 2 : ℝ) : ℂ) := by rw [hq]; ring
    rw [this]; exact hdist _ (by rw [norm_neg]; exact hu1)
  have hcoord : ∀ s : ℂ, lineCoord D (P0 + u * s) = s.im := by
    intro s
    unfold lineCoord
    have : star D.axis * (P0 + u * s - D.midpoint) = ((-L : ℝ) : ℂ) + s := by
      simp only [hP0]
      linear_combination (((-L : ℝ) : ℂ) + s) * hstar
    rw [this, Complex.add_im, Complex.ofReal_im, zero_add]
  have hluu : lineCoord D uu = r0 / 2 := by
    have : uu = P0 + u * (Complex.I * ((r0 / 2 : ℝ) : ℂ)) := by rw [huu]; ring
    rw [this, hcoord]; simp
  have hlll : lineCoord D ll = -(r0 / 2) := by
    have : ll = P0 + u * (-(Complex.I * ((r0 / 2 : ℝ) : ℂ))) := by rw [hll]; ring
    rw [this, hcoord]; simp
  have hlq : lineCoord D q = 0 := by
    have : q = P0 + u * (-((r0 / 2 : ℝ) : ℂ)) := by rw [hq]; ring
    rw [this, hcoord]; simp
  have huudom : uu ∈ D.domain := mem_domain_of_lineCoord_ne D huuball (by rw [hluu]; positivity)
  have hlldom : ll ∈ D.domain := mem_domain_of_lineCoord_ne D hllball (by rw [hlll]; simp; positivity)
  have hqdom : q ∈ D.domain := by
    refine ⟨hqball, fun hs => ?_⟩
    rw [hseg] at hs
    obtain ⟨t, ht, hteq⟩ := hs
    have h1 : u * ((t : ℂ) - ((-L - r0 / 2 : ℝ) : ℂ)) = 0 := by
      have : m + u * (t : ℂ) = P0 - u * ((r0 / 2 : ℝ) : ℂ) := hteq
      simp only [hP0] at this
      push_cast at this ⊢
      linear_combination this
    rcases mul_eq_zero.1 h1 with h | h
    · exact hu0 h
    · have h2 : t = -L - r0 / 2 := by
        have := sub_eq_zero.1 h
        exact_mod_cast this
      have := ht.1
      linarith
  have hsym : ∀ a b : ℂ, segment ℝ a b ⊆ D.domain → segment ℝ b a ⊆ D.domain := by
    intro a b h; rwa [segment_symm]
  have hq_uu : segment ℝ q uu ⊆ D.domain :=
    segment_subset_domain_of_lineCoord D hqdom huuball (Or.inl ⟨hlq.ge, by rw [hluu]; positivity⟩)
  have hq_ll : segment ℝ q ll ⊆ D.domain :=
    segment_subset_domain_of_lineCoord D hqdom hllball
      (Or.inr ⟨hlq.le, by rw [hlll]; linarith⟩)
  have hreach : ∀ z ∈ D.domain,
      Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ D.domain) z uu := by
    intro z hz
    by_cases hz0 : 0 ≤ lineCoord D z
    · exact Relation.ReflTransGen.single
        (segment_subset_domain_of_lineCoord D hz huuball (Or.inl ⟨hz0, by rw [hluu]; positivity⟩))
    · have hz0 := not_le.1 hz0
      have h1 : Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ D.domain) z ll :=
        Relation.ReflTransGen.single
          (segment_subset_domain_of_lineCoord D hz hllball (Or.inr ⟨hz0.le, by rw [hlll]; linarith⟩))
      have h2 : Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ D.domain) ll q :=
        Relation.ReflTransGen.single (hsym _ _ hq_ll)
      exact (h1.trans h2).trans (Relation.ReflTransGen.single hq_uu)
  intro z hz w hw
  have hrev : ∀ {x y : ℂ}, Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ D.domain) x y →
      Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ D.domain) y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact (Relation.ReflTransGen.single (r := fun a b : ℂ => segment ℝ a b ⊆ D.domain)
        (hsym _ _ hbc)).trans ih
  exact (hreach z hz).trans (hrev (hreach w hw))

end
end NlsGge.ThirdConsultation.MContour
