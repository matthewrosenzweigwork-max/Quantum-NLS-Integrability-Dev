import QuantumNLS.Prop018Period
import QuantumNLS.PeriodTwoTerm

/-!
LOCAL-009 round 22, scalar GP-17 residue constituent. Repaired from archived draft; no inverse estimate is assumed or asserted.

The frozen GP-17 rectangle residue lemma evaluates the contour of each real
root resolvent. Summing gives the exact occupation count. A second lemma records
the contour-length bound needed to integrate a future uniform second-order
integrand estimate. Neither lemma asserts that the transfer inverse expression
already has that estimate.
-/

set_option autoImplicit false
noncomputable section

open Complex Set Interval

namespace QuantumNLS.LOCAL009R22Residues

open QuantumNLS.LabelExactPeriod QuantumNLS.PeriodReconstruction
  QuantumNLS.PeriodTwoTerm QuantumNLS.Prop018Period

private lemma inv_continuousAt_of_ne {q z : ℂ} (hz : z ≠ q) :
    ContinuousAt (fun w : ℂ => (w - q)⁻¹) z :=
  (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hz)

private lemma rect_inv_zero_left {a b h q : ℝ} (hab : a < b)
    (hq : q < a) :
    rectIntegral (fun z => (z - (q : ℂ))⁻¹) a b h = 0 := by
  have hF : ∀ z : ℂ, 0 < (z - (q : ℂ)).re →
      HasDerivAt (fun w : ℂ => Complex.log (w - (q : ℂ)))
        ((z - (q : ℂ))⁻¹) z := by
    intro z hz
    have hd := ((hasDerivAt_id z).sub_const (q : ℂ)).clog (Or.inl hz)
    simpa [id_eq, one_div] using hd
  have hreal_bottom : ∀ x ∈ uIcc a b,
      0 < ((x : ℂ) + ((-h : ℝ) : ℂ) * I - (q : ℂ)).re := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    rcases hx with ⟨hxa, hxb⟩
    simp
    linarith
  have hreal_top : ∀ x ∈ uIcc a b,
      0 < ((x : ℂ) + h * I - (q : ℂ)).re := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    rcases hx with ⟨hxa, hxb⟩
    simp
    linarith
  have hreal_right : ∀ y ∈ uIcc (-h) h,
      0 < ((b : ℂ) + y * I - (q : ℂ)).re := by
    intro y hy
    simp
    linarith
  have hreal_left : ∀ y ∈ uIcc (-h) h,
      0 < ((a : ℂ) + y * I - (q : ℂ)).re := by
    intro y hy
    simp
    linarith
  have hcont_bottom : ∀ x ∈ uIcc a b,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹)
        ((x : ℂ) + ((-h : ℝ) : ℂ) * I) := by
    intro x hx
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_bottom x hx
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  have hcont_top : ∀ x ∈ uIcc a b,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹) ((x : ℂ) + h * I) := by
    intro x hx
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_top x hx
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  have hcont_right : ∀ y ∈ uIcc (-h) h,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹) ((b : ℂ) + y * I) := by
    intro y hy
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_right y hy
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  have hcont_left : ∀ y ∈ uIcc (-h) h,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹) ((a : ℂ) + y * I) := by
    intro y hy
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_left y hy
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  rw [rect_eq_of_primitives
    (F := fun z : ℂ => Complex.log (z - (q : ℂ)))
    (G := fun z : ℂ => Complex.log (z - (q : ℂ)))
    (fun x hx => hF _ (hreal_bottom x hx))
    (fun x hx => hF _ (hreal_top x hx))
    (fun y hy => hF _ (hreal_right y hy))
    (fun y hy => hF _ (hreal_left y hy))
    hcont_bottom hcont_top hcont_right hcont_left]
  ring

private lemma rect_inv_zero_right {a b h q : ℝ} (hab : a < b)
    (hq : b < q) :
    rectIntegral (fun z => (z - (q : ℂ))⁻¹) a b h = 0 := by
  have hF : ∀ z : ℂ, 0 < (-(z - (q : ℂ))).re →
      HasDerivAt (fun w : ℂ => Complex.log (-(w - (q : ℂ))))
        ((z - (q : ℂ))⁻¹) z := by
    intro z hz
    have h1 : HasDerivAt (fun w : ℂ => -(w - (q : ℂ))) (-1) z :=
      ((hasDerivAt_id z).sub_const (q : ℂ)).neg
    have hd := h1.clog (Or.inl hz)
    refine hd.congr_deriv ?_
    rw [neg_div_neg_eq, one_div]
  have hreal_bottom : ∀ x ∈ uIcc a b,
      0 < (-( (x : ℂ) + ((-h : ℝ) : ℂ) * I - (q : ℂ))).re := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    rcases hx with ⟨hxa, hxb⟩
    simp
    linarith
  have hreal_top : ∀ x ∈ uIcc a b,
      0 < (-( (x : ℂ) + h * I - (q : ℂ))).re := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    rcases hx with ⟨hxa, hxb⟩
    simp
    linarith
  have hreal_right : ∀ y ∈ uIcc (-h) h,
      0 < (-((b : ℂ) + y * I - (q : ℂ))).re := by
    intro y hy
    simp
    linarith
  have hreal_left : ∀ y ∈ uIcc (-h) h,
      0 < (-((a : ℂ) + y * I - (q : ℂ))).re := by
    intro y hy
    simp
    linarith
  have hcont_bottom : ∀ x ∈ uIcc a b,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹)
        ((x : ℂ) + ((-h : ℝ) : ℂ) * I) := by
    intro x hx
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_bottom x hx
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  have hcont_top : ∀ x ∈ uIcc a b,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹) ((x : ℂ) + h * I) := by
    intro x hx
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_top x hx
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  have hcont_right : ∀ y ∈ uIcc (-h) h,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹) ((b : ℂ) + y * I) := by
    intro y hy
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_right y hy
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  have hcont_left : ∀ y ∈ uIcc (-h) h,
      ContinuousAt (fun z : ℂ => (z - (q : ℂ))⁻¹) ((a : ℂ) + y * I) := by
    intro y hy
    apply inv_continuousAt_of_ne
    intro he
    have he' := congrArg Complex.re he
    have hpos := hreal_left y hy
    norm_num [Complex.mul_re, Complex.mul_im] at he' hpos
    linarith
  rw [rect_eq_of_primitives
    (F := fun z : ℂ => Complex.log (-(z - (q : ℂ))))
    (G := fun z : ℂ => Complex.log (-(z - (q : ℂ))))
    (fun x hx => hF _ (hreal_bottom x hx))
    (fun x hx => hF _ (hreal_top x hx))
    (fun y hy => hF _ (hreal_right y hy))
    (fun y hy => hF _ (hreal_left y hy))
    hcont_bottom hcont_top hcont_right hcont_left]
  ring

/-- The reciprocal contour has one unit residue for a real pole inside and zero outside. -/
theorem reciprocal_rect_residue {a b h q : ℝ} (hab : a < b) (hh : 0 < h)
    (hqa : q ≠ a) (hqb : q ≠ b) :
    rectIntegral (fun z => (z - (q : ℂ))⁻¹) a b h =
      if a < q ∧ q < b then 2 * Real.pi * I else 0 := by
  by_cases hin : a < q ∧ q < b
  · simp only [hin, and_self, ↓reduceIte]
    have hw : |((q : ℂ).im)| < h := by simpa using hh
    simpa using (QuantumNLS.Prop018Period.rect_inv
      (a := a) (b := b) (h := h) (w := (q : ℂ)) hin.1 hin.2 hw)
  · simp only [hin, ↓reduceIte]
    rcases lt_or_gt_of_ne hqa with hleft | hright
    · exact rect_inv_zero_left hab hleft
    · have hright' : b < q := by
        rcases lt_or_gt_of_ne hqb with hlt | hgt
        · exact (hin ⟨hright, hlt⟩).elim
        · exact hgt
      exact rect_inv_zero_right hab hright'

/-- The exact scalar GP-17 count for the finite root Cauchy sum. -/
theorem root_cauchy_contour_count {N : ℕ} {a b h ε : ℝ}
    (hab : a < b) (hh : 0 < h) (q : Fin N → ℝ)
    (hqa : ∀ j, q j ≠ a) (hqb : ∀ j, q j ≠ b) :
    rectIntegral (fun z => (ε : ℂ) * ∑ j, (z - (q j : ℂ))⁻¹) a b h =
      (ε : ℂ) * (2 * Real.pi * I) *
        (Finset.univ.filter (fun j => a < q j ∧ q j < b)).card := by
  have hcont_bottom : ∀ j ∈ (Finset.univ : Finset (Fin N)), ∀ x ∈ uIcc a b,
      ContinuousAt (fun z : ℂ => (z - (q j : ℂ))⁻¹)
        ((x : ℂ) + ((-h : ℝ) : ℂ) * I) := by
    intro j _ x hx
    apply inv_continuousAt_of_ne
    intro he
    have him := congrArg Complex.im he
    simp at him
    exact (ne_of_gt hh) (by linarith)
  have hcont_top : ∀ j ∈ (Finset.univ : Finset (Fin N)), ∀ x ∈ uIcc a b,
      ContinuousAt (fun z : ℂ => (z - (q j : ℂ))⁻¹) ((x : ℂ) + h * I) := by
    intro j _ x hx
    apply inv_continuousAt_of_ne
    intro he
    have him := congrArg Complex.im he
    simp at him
    exact (ne_of_gt hh) (by linarith)
  have hcont_right : ∀ j ∈ (Finset.univ : Finset (Fin N)), ∀ y ∈ uIcc (-h) h,
      ContinuousAt (fun z : ℂ => (z - (q j : ℂ))⁻¹) ((b : ℂ) + y * I) := by
    intro j _ y hy
    apply inv_continuousAt_of_ne
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    exact hqb j hre.symm
  have hcont_left : ∀ j ∈ (Finset.univ : Finset (Fin N)), ∀ y ∈ uIcc (-h) h,
      ContinuousAt (fun z : ℂ => (z - (q j : ℂ))⁻¹) ((a : ℂ) + y * I) := by
    intro j _ y hy
    apply inv_continuousAt_of_ne
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    exact hqa j hre.symm
  rw [QuantumNLS.PeriodTwoTerm.rectIntegral_const_mul,
    rectIntegral_sum Finset.univ hcont_bottom hcont_top hcont_right hcont_left]
  rw [Finset.sum_congr rfl (fun j _ => reciprocal_rect_residue hab hh (hqa j) (hqb j))]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A uniform scalar integrand error contributes at most perimeter times its bound. -/
theorem contour_error_from_uniform_bound {a b h C : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (F G : ℂ → ℂ)
    (hpoint : ∀ z ∈ Gam a b h, ‖F z - G z‖ ≤ C) :
    ‖rectIntegral (fun z => F z - G z) a b h‖ ≤ (2 * (b - a) + 4 * h) * C := by
  apply QuantumNLS.PeriodTwoTerm.norm_rectIntegral_le hab hh
  intro z hz
  exact hpoint z hz

#print axioms reciprocal_rect_residue
#print axioms root_cauchy_contour_count
#print axioms contour_error_from_uniform_bound

end QuantumNLS.LOCAL009R22Residues
