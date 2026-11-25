import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.PairAsymptoticsScalar

/-! # D1: the concrete Dirichlet characteristic

Book Theorem 5.1 and equation (5.1). Dirichlet means equal components at
both endpoints; the free characteristic is positive sine. -/
set_option autoImplicit false
open Filter Topology Set
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

def dirichletChar (φ : PotPair) (z : ℂ) : ℂ :=
  (Matrix.mulVec (monodromyPair φ z) ![1, 1] 1 -
    Matrix.mulVec (monodromyPair φ z) ![1, 1] 0) / (2 * Complex.I)

theorem dirichlet_denominator_ne_zero38 : (2 : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (by norm_num) Complex.I_ne_zero

theorem dirichletChar_eq (φ : PotPair) (z : ℂ) : dirichletChar φ z =
    (monodromyPair φ z 1 0 + monodromyPair φ z 1 1 -
      monodromyPair φ z 0 0 - monodromyPair φ z 0 1) / (2 * Complex.I) := by
  simp only [dirichletChar, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
  congr 1
  ring

theorem analyticOnNhd_dirichletChar :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => dirichletChar p.1 p.2) univ := by
  have h := (((analyticOnNhd_monodromyPair 1 0).add (analyticOnNhd_monodromyPair 1 1)).sub
    (analyticOnNhd_monodromyPair 0 0)).sub (analyticOnNhd_monodromyPair 0 1)
  simpa only [dirichletChar_eq, Pi.add_apply, Pi.sub_apply] using h.div_const (c := 2 * Complex.I)

theorem analyticOnNhd_dirichletChar_z (φ : PotPair) :
    AnalyticOnNhd ℂ (dirichletChar φ) univ := fun z _ =>
  AnalyticAt.comp (analyticOnNhd_dirichletChar (φ, z) (mem_univ _))
    ((analyticAt_const (v := φ)).prod analyticAt_id)

theorem dirichletChar_zero (z : ℂ) : dirichletChar 0 z = Complex.sin z := by
  rw [dirichletChar_eq, monodromyPair_zero_potential]
  simp only [freeE, mul_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add, sub_zero]
  rw [Complex.sin]
  have hp : Complex.exp (-z * Complex.I) = Complex.exp (-(Complex.I * z)) := by congr 1; ring
  have hm : Complex.exp (z * Complex.I) = Complex.exp (Complex.I * z) := by congr 1; ring
  rw [hp, hm]
  field_simp
  simp [Complex.I_sq]

/-- The zero equation is precisely equality of the transported endpoint components. -/
theorem dirichletChar_zero_iff_boundary38 (φ : PotPair) (z : ℂ) :
    dirichletChar φ z = 0 ↔
      Matrix.mulVec (monodromyPair φ z) ![1, 1] 0 =
        Matrix.mulVec (monodromyPair φ z) ![1, 1] 1 := by
  rw [dirichletChar, div_eq_zero_iff]
  simp only [dirichlet_denominator_ne_zero38, or_false, sub_eq_zero]
  exact eq_comm

/-- An equivalent boundary condition on an arbitrary nonzero equal-component vector. -/
theorem dirichletChar_zero_iff_vector38 (φ : PotPair) (z : ℂ) :
    dirichletChar φ z = 0 ↔ ∃ v : Fin 2 → ℂ,
      v ≠ 0 ∧ v 0 = v 1 ∧ Matrix.mulVec (monodromyPair φ z) v 0 =
        Matrix.mulVec (monodromyPair φ z) v 1 := by
  rw [dirichletChar_zero_iff_boundary38]
  constructor
  · intro h
    refine ⟨![1, 1], ?_, by simp, h⟩
    intro hz
    have hh := congrArg (fun v => v 0) hz
    simpa using hh
  · rintro ⟨v, hv, hsame, hrow⟩
    have hv0 : v 0 ≠ 0 := by
      intro hz
      apply hv
      ext i
      fin_cases i <;> simp [hz, ← hsame]
    apply mul_left_cancel₀ hv0
    calc v 0 * Matrix.mulVec (monodromyPair φ z) ![1, 1] 0 =
        Matrix.mulVec (monodromyPair φ z) v 0 := by
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← hsame]
          ring
      _ = Matrix.mulVec (monodromyPair φ z) v 1 := hrow
      _ = v 0 * Matrix.mulVec (monodromyPair φ z) ![1, 1] 1 := by
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← hsame]
          ring

end
end NlsGge.GK38
