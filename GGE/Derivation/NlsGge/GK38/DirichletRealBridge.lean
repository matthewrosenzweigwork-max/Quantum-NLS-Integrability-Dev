import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletRealAlgebra
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.Spectral.ActualRealParameterDysonConjugationV3

/-! Real-slice structure and the actual antidiscriminant at Dirichlet roots.
Private source anchor: book I.6 Lemma 6.6. -/
set_option autoImplicit false
open Set MeasureTheory
namespace NlsGge.GK38
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations

abbrev DirichletTime38 := Icc (0 : ℝ) 1

def dirichletState38 (u : PhysicalL2) (z : ℂ) (t : DirichletTime38) : Fin 2 → ℂ :=
  (fundPair (realSlice u) z t).mulVec ![1, 1]

theorem dirichletState_eq_actual38 (u : PhysicalL2) (z : ℂ) (t : DirichletTime38) :
    dirichletState38 u z t = actualPhysicalFloquetState33 u z ![1, 1] t := by
  unfold dirichletState38 actualPhysicalFloquetState33
  rw [fundPair_realSlice]

theorem fundPair_real_entry_star38 (u : PhysicalL2) (x : ℝ)
    (t : DirichletTime38) (i j : Fin 2) :
    star (fundPair (realSlice u) (x : ℂ) t i j) =
      fundPair (realSlice u) (x : ℂ) t i.rev j.rev := by
  rw [fundPair_realSlice]
  exact actualComplexZsDysonTsum_real_entry_star _ x t i j

theorem monodromyPair_real_entry_star38 (u : PhysicalL2) (x : ℝ) (i j : Fin 2) :
    star (monodromyPair (realSlice u) (x : ℂ) i j) =
      monodromyPair (realSlice u) (x : ℂ) i.rev j.rev := by
  rw [monodromyPair_eq_fundPair]
  exact fundPair_real_entry_star38 u x _ i j

theorem dirichletState_real_star38 (u : PhysicalL2) (x : ℝ) (t : DirichletTime38) :
    star (dirichletState38 u (x : ℂ) t 0) = dirichletState38 u (x : ℂ) t 1 := by
  simp only [dirichletState38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, star_add,
    fundPair_real_entry_star38]
  change fundPair (realSlice u) (x : ℂ) t 1 1 + fundPair (realSlice u) (x : ℂ) t 1 0 =
    fundPair (realSlice u) (x : ℂ) t 1 0 + fundPair (realSlice u) (x : ℂ) t 1 1
  ring

theorem dirichletState_first_ne_zero38 (u : PhysicalL2) (x : ℝ) (t : DirichletTime38) :
    dirichletState38 u (x : ℂ) t 0 ≠ 0 := by
  intro hz
  have h1 : dirichletState38 u (x : ℂ) t 1 = 0 := by
    rw [← dirichletState_real_star38, hz, star_zero]
  have hd : (fundPair (realSlice u) (x : ℂ) t).det = 1 := by
    rw [fundPair_realSlice]
    exact actualPhysicalL2ZsDysonTsum_det_one u (x : ℂ) t ⟨t.property.1, t.property.2.trans (by norm_num)⟩
  have hv : (![1, 1] : Fin 2 → ℂ) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (by rw [hd]; norm_num) (by
      funext i
      fin_cases i <;> assumption)
  have hh := congrArg (fun v => v 0) hv
  simpa using hh

/-- The determinant and actual Dirichlet boundary give the squared identity. -/
theorem dirichlet_perChar_eq_anti_sq38 (φ : PotPair) (z : ℂ)
    (hz : dirichletChar φ z = 0) : perChar φ z = antiDiscrim φ z ^ 2 := by
  have hb := (dirichletChar_zero_iff_boundary38 φ z).mp hz
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hb
  have hd := det_monodromyPair φ z
  rw [Matrix.det_fin_two] at hd
  rw [perChar_eq, discrim_eq, antiDiscrim]
  linear_combination 4 * hd +
    (monodromyPair φ z 0 0 - monodromyPair φ z 1 1 -
      monodromyPair φ z 0 1 + monodromyPair φ z 1 0) * hb

/-- Full trace and antidiscriminant are real for every real spectral parameter. -/
theorem dirichlet_real_characteristic38 (u : PhysicalL2) (x : ℝ) :
    (dirichletChar (realSlice u) (x : ℂ)).im = 0 ∧
      (antiDiscrim (realSlice u) (x : ℂ)).im = 0 ∧
      (discrim (realSlice u) (x : ℂ)).im = 0 := by
  have h00 := monodromyPair_real_entry_star38 u x 0 0
  have h01 := monodromyPair_real_entry_star38 u x 0 1
  change star (monodromyPair (realSlice u) (x : ℂ) 0 0) = monodromyPair (realSlice u) (x : ℂ) 1 1 at h00
  change star (monodromyPair (realSlice u) (x : ℂ) 0 1) = monodromyPair (realSlice u) (x : ℂ) 1 0 at h01
  have hr00 := congrArg Complex.re h00
  have hr01 := congrArg Complex.re h01
  have hi00 := congrArg Complex.im h00
  have hi01 := congrArg Complex.im h01
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hr00 hr01 hi00 hi01
  refine ⟨?_, ?_, ?_⟩
  · rw [dirichletChar_eq]
    exact dirichlet_scalar_im_zero38 _ _ _ _ hr00 hr01
  · simp only [antiDiscrim, Complex.add_im]
    linarith
  · simp only [discrim_eq, Complex.add_im]
    linarith

/-- Real part of the actual antidiscriminant at the actual real D1 label. -/
def deltaMu (u : PhysicalL2) (n : ℤ) : ℝ :=
  (antiDiscrim (realSlice u) (gkMu u n : ℂ)).re

theorem antiDiscrim_eq_deltaMu38 (u : PhysicalL2) (n : ℤ) :
    antiDiscrim (realSlice u) (gkMu u n : ℂ) = (deltaMu u n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (dirichlet_real_characteristic38 u (gkMu u n)).2.1

theorem deltaMu_squared38 (u : PhysicalL2) (n : ℤ) :
    (discrim (realSlice u) (gkMu u n : ℂ)).re ^ 2 - 4 = deltaMu u n ^ 2 := by
  have h := dirichlet_perChar_eq_anti_sq38 (realSlice u) (gkMu u n : ℂ) (gkMu_root38 u n)
  rw [perChar_eq, antiDiscrim_eq_deltaMu38] at h
  have hi := (dirichlet_real_characteristic38 u (gkMu u n)).2.2
  exact dirichlet_scalar_square38 _ _ hi h

end
end NlsGge.GK38
