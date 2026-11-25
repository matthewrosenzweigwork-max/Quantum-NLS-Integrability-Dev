import NlsGge.GK38.GradEigenFloquet
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem periodic_eigen_trace (M : PairMat38) (c : ℂ) (a : PairVec38)
    (hc : c^2 = 1) (hd : M 0 0*M 1 1-M 0 1*M 1 0=1)
    (ha : a ≠ 0) (he : Matrix.mulVec M a = c • a) : M 0 0+M 1 1=2*c := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul] at h0 h1
  have hc0 : c ≠ 0 := by intro hz; rw [hz] at hc; norm_num at hc
  have he0 : c*(M 0 0+M 1 1-2*c)*a 0=0 := by
    linear_combination -(M 1 1-c)*h0+M 0 1*h1+a 0*hd-a 0*hc
  have he1 : c*(M 0 0+M 1 1-2*c)*a 1=0 := by
    linear_combination M 1 0*h0-(M 0 0-c)*h1+a 1*hd-a 1*hc
  have hs : M 0 0+M 1 1-2*c=0 := by
    by_cases ha0 : a 0=0
    · have ha1 : a 1 ≠ 0 := by
        intro hz
        apply ha
        ext i
        fin_cases i <;> assumption
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he1).resolve_right ha1)).resolve_left hc0
    · exact (mul_eq_zero.mp ((mul_eq_zero.mp he0).resolve_right ha0)).resolve_left hc0
  exact sub_eq_zero.mp hs

theorem periodic_eigen_chart01 (M : PairMat38) (c : ℂ) (a : PairVec38)
    (ha : a ≠ 0) (he : Matrix.mulVec M a=c • a) (hb : M 0 1 ≠ 0) :
    a 0 ≠ 0 ∧ a = a 0 • (![1,(c-M 0 0)/M 0 1] : PairVec38) := by
  have h0 := congrFun he 0
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul] at h0
  have ha0 : a 0 ≠ 0 := by
    intro hz
    have ha1 : a 1=0 := by
      rw [hz,mul_zero,zero_add,mul_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hb
    apply ha
    ext i
    fin_cases i <;> assumption
  refine ⟨ha0,?_⟩
  ext i
  fin_cases i
  · simp
  · simp
    field_simp
    linear_combination h0

theorem periodic_eigen_chart10 (M : PairMat38) (c : ℂ) (a : PairVec38)
    (ha : a ≠ 0) (he : Matrix.mulVec M a=c • a) (hb : M 1 0 ≠ 0) :
    a 1 ≠ 0 ∧ a = a 1 • (![(c-M 1 1)/M 1 0,1] : PairVec38) := by
  have h1 := congrFun he 1
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul] at h1
  have ha1 : a 1 ≠ 0 := by
    intro hz
    have ha0 : a 0=0 := by
      rw [hz,mul_zero,add_zero,mul_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left hb
    apply ha
    ext i
    fin_cases i <;> assumption
  refine ⟨ha1,?_⟩
  ext i
  fin_cases i
  · simp
    field_simp
    linear_combination h1
  · simp

theorem periodic_diagonal_scalar (M : PairMat38) (c : ℂ)
    (hc : c^2=1) (hd : M 0 0*M 1 1-M 0 1*M 1 0=1)
    (hs : M 0 0+M 1 1=2*c) (h01 : M 0 1=0) (h10 : M 1 0=0) :
    M = c • (1 : PairMat38) := by
  have hsq : (M 0 0-c)^2=0 := by
    rw [h01,h10] at hd
    linear_combination M 0 0*hs-hd+hc
  have h00 : M 0 0=c := sub_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hsq)
  have h11 : M 1 1=c := by linear_combination hs-h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00,h01,h10,h11]

theorem periodic_spectral_scalar_algebra (F : PairMat38) (c : ℂ) :
    ((c • (1 : PairMat38)) * (F.adjugate * spectralCoeff38 * F)) 0 0 +
      ((c • (1 : PairMat38)) * (F.adjugate * spectralCoeff38 * F)) 1 1 = 0 := by
  simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.adjugate_fin_two,
    spectralCoeff38,Fin.sum_univ_two]
  ring

theorem periodic_spectral_chart01_algebra (M F : PairMat38) (r : ℂ)
    (hs : 2*M 0 1*r=M 1 1-M 0 0) (hp : M 0 1*r*r= -M 1 0) :
    (M * (F.adjugate * spectralCoeff38 * F)) 0 0 +
      (M * (F.adjugate * spectralCoeff38 * F)) 1 1 =
      (2*Complex.I*M 0 1) * (F 0 0+r*F 0 1) * (F 1 0+r*F 1 1) := by
  simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.adjugate_fin_two,
    spectralCoeff38,Fin.sum_univ_two]
  linear_combination (-Complex.I*(F 0 0*F 1 1+F 0 1*F 1 0))*hs -
    (2*Complex.I*F 0 1*F 1 1)*hp

theorem periodic_spectral_chart10_algebra (M F : PairMat38) (r : ℂ)
    (hs : 2*M 1 0*r=M 0 0-M 1 1) (hp : M 1 0*r*r= -M 0 1) :
    (M * (F.adjugate * spectralCoeff38 * F)) 0 0 +
      (M * (F.adjugate * spectralCoeff38 * F)) 1 1 =
      (-2*Complex.I*M 1 0) * (r*F 0 0+F 0 1) * (r*F 1 0+F 1 1) := by
  simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.adjugate_fin_two,
    spectralCoeff38,Fin.sum_univ_two]
  linear_combination (Complex.I*(F 0 0*F 1 1+F 0 1*F 1 0))*hs +
    (2*Complex.I*F 0 0*F 1 0)*hp

end
end NlsGge.GK38.GradEigen38
