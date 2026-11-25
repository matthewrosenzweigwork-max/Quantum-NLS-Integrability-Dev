import NlsGge.GK38.DirichletChar
import NlsGge.GK38.PairVolterraProbe

/-! # D1: a nonfree nilpotent constant-potential regression

At a=z=1 the constant coefficient is nilpotent. Its fundamental matrix is
proved from the actual Volterra equation; no nonzero-frequency formula is used. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open NlsGge.Pilot NlsGge.SpectralFoundations
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

def dirichletNilpotentFund38 (t : ℝ) : PairMat38 :=
  1 + t • zsCoefficientComplex (fun _ => 1) 1 0

theorem dirichlet_nilpotent_square38 :
    zsCoefficientComplex (fun _ => 1) 1 0 * zsCoefficientComplex (fun _ => 1) 1 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zsCoefficientComplex, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

theorem dirichlet_nilpotent_entry_hasDeriv38 (i j : Fin 2) (x : ℝ) :
    HasDerivAt (fun y : ℝ => dirichletNilpotentFund38 y i j)
      ((zsCoefficientComplex (fun _ => 1) 1 0 * dirichletNilpotentFund38 x) i j) x := by
  have he : zsCoefficientComplex (fun _ => 1) 1 0 * dirichletNilpotentFund38 x =
      zsCoefficientComplex (fun _ => 1) 1 0 := by
    simp [dirichletNilpotentFund38, mul_add, dirichlet_nilpotent_square38]
  rw [he]
  have h := ((hasDerivAt_id x).smul_const (zsCoefficientComplex (fun _ => 1) 1 0 i j)).const_add
    ((1 : PairMat38) i j)
  simpa only [dirichletNilpotentFund38, Matrix.add_apply, Matrix.smul_apply, one_smul, id_eq] using! h

theorem continuous_dirichletNilpotentFund38 : Continuous dirichletNilpotentFund38 := by
  unfold dirichletNilpotentFund38
  fun_prop

def dirichletNilpotentCont38 : PairCont38 :=
  ⟨fun t => dirichletNilpotentFund38 t,
    continuous_dirichletNilpotentFund38.comp continuous_subtype_val⟩

theorem dirichlet_nilpotent_entry_deriv38 (i j : Fin 2) (x : ℝ) :
    HasDerivAt (fun y : ℝ => freeE 1 (-y) i i * dirichletNilpotentFund38 y i j)
      ((freeE 1 (-x) * constPc 1 * dirichletNilpotentFund38 x) i j) x := by
  have hGe := dirichlet_nilpotent_entry_hasDeriv38 i j x
  fin_cases i
  · have hE : HasDerivAt (fun y : ℝ => freeE 1 (-y) 0 0)
        (Complex.I * freeE 1 (-x) 0 0) x := by
      have h := hasDerivAt_cexp_mul Complex.I x
      convert h using 1 <;> simp [freeE]
    refine (hE.mul hGe).congr_deriv ?_
    fin_cases j <;> simp [zsCoefficientComplex, constPc, Matrix.mul_apply,
      Fin.sum_univ_two, freeE, dirichletNilpotentFund38, Complex.real_smul] <;> ring
  · have hE : HasDerivAt (fun y : ℝ => freeE 1 (-y) 1 1)
        (-Complex.I * freeE 1 (-x) 1 1) x := by
      have h := hasDerivAt_cexp_mul (-Complex.I) x
      convert h using 1 <;> simp [freeE]
    refine (hE.mul hGe).congr_deriv ?_
    fin_cases j <;> simp [zsCoefficientComplex, constPc, Matrix.mul_apply,
      Fin.sum_univ_two, freeE, dirichletNilpotentFund38, Complex.real_smul] <;> ring

/-- Integrability and differentiability establish the book Volterra equation at the nilpotent point. -/
theorem dirichlet_nilpotent_integral_eq38 (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    dirichletNilpotentCont38 t i j = freeE 1 t i j +
      ∫ s in (0 : ℝ)..t, (freeE 1 (t - s) * potCoeff38 (realSlice (constL2 1)) s *
        ext38 dirichletNilpotentCont38 s) i j := by
  let G := dirichletNilpotentCont38
  have hfac : (∫ s in (0 : ℝ)..t, (freeE 1 (t - s) * potCoeff38 (realSlice (constL2 1)) s *
        ext38 G s) i j) =
      freeE 1 t i i * ∫ s in (0 : ℝ)..t, (freeE 1 (-s) * potCoeff38 (realSlice (constL2 1)) s *
        ext38 G s) i j := by
    have h := congrArg (fun M => M i j) (volterraFun_eq (realSlice (constL2 1)) 1 G t)
    simpa only [volterraFun, volterraKer, ext38, Matrix.of_apply, freeE_mul_apply] using h
  have hae : (∫ s in (0 : ℝ)..t, (freeE 1 (-s) * potCoeff38 (realSlice (constL2 1)) s *
        ext38 G s) i j) =
      ∫ s in (0 : ℝ)..t, (freeE 1 (-s) * constPc 1 * dirichletNilpotentFund38 s) i j := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [potCoeff38_realSlice_const_ae 1] with s hs hsI
    rw [uIoc_of_le t.2.1] at hsI
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hsI.1.le, hsI.2.trans t.2.2⟩
    rw [hs, ext38_of_mem _ hs1]
    rfl
  have hc : Continuous (fun s : ℝ => (freeE 1 (-s) * constPc 1 * dirichletNilpotentFund38 s) i j) := by
    have h1 := (continuous_freeE 1).comp continuous_neg
    have h3 : Continuous (fun s : ℝ => freeE 1 (-s) * constPc 1 * dirichletNilpotentFund38 s) :=
      (h1.mul continuous_const).mul continuous_dirichletNilpotentFund38
    exact (continuous_apply j).comp ((continuous_apply i).comp h3)
  have hftc : (∫ s in (0 : ℝ)..t, (freeE 1 (-s) * constPc 1 * dirichletNilpotentFund38 s) i j) =
      freeE 1 (-t) i i * dirichletNilpotentFund38 t i j - (1 : PairMat38) i j := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => freeE 1 (-y) i i * dirichletNilpotentFund38 y i j)
      (fun x _ => dirichlet_nilpotent_entry_deriv38 i j x) (hc.intervalIntegrable _ _)]
    simp [dirichletNilpotentFund38, freeE_zero]
  rw [hfac, hae, hftc]
  have hu := freeE_mul_freeE_neg 1 t i
  have he := freeE_apply_eq 1 t i j
  change dirichletNilpotentFund38 t i j = _
  rw [he]
  linear_combination (-(dirichletNilpotentFund38 t i j)) * hu

theorem fundPair_dirichlet_nilpotent38 (t : Icc (0 : ℝ) 1) :
    fundPair (realSlice (constL2 1)) 1 t = dirichletNilpotentFund38 t := by
  have hG := fundCont_unique (realSlice (constL2 1)) 1 dirichletNilpotentCont38
    dirichlet_nilpotent_integral_eq38
  rw [fundPair_eq, ← hG]
  rfl

theorem dirichlet_nonfree_constant_root38 : dirichletChar (realSlice (constL2 1)) 1 = 0 := by
  rw [dirichletChar_eq, monodromyPair_eq_fundPair, fundPair_dirichlet_nilpotent38]
  norm_num [dirichletNilpotentFund38, zsCoefficientComplex, Complex.real_smul]

end
end NlsGge.GK38
