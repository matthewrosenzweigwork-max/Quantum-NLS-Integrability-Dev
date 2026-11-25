import NlsGge.GK38.GradFundamentalL2Fund

/-! # K1: matrix, column-star and cyclic forms of the independent kernels.
GK Chapter I, Proposition3.1 and Corollary3.2. No determinant or derivative
hypothesis is needed for these finite polynomial identities.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

def k1SwapMat38 : PairMat38 := !![0, 1; 1, 0]
def spectralCoeff38 : PairMat38 := !![-Complex.I, 0; 0, Complex.I]

/-- Both components of the column-star fundamental kernel are explicit matrices. -/
theorem fundamentalScaledKernel38_components (φ : PotPair) (z : ℂ)
    (t : Set.Icc (0 : ℝ) 1) (s : ℝ) (i j : Fin 2) :
    fundamentalScaledKernel38 φ z t s i j =
      ![(fundPair φ z t * !![
          -(fundColumn38 φ z s 0 1 * fundColumn38 φ z s 1 1),
          -(fundColumn38 φ z s 1 1) ^ 2;
          (fundColumn38 φ z s 0 1) ^ 2,
          fundColumn38 φ z s 0 1 * fundColumn38 φ z s 1 1]) i j,
        (fundPair φ z t * !![
          -(fundColumn38 φ z s 0 0 * fundColumn38 φ z s 1 0),
          -(fundColumn38 φ z s 1 0) ^ 2;
          (fundColumn38 φ z s 0 0) ^ 2,
          fundColumn38 φ z s 0 0 * fundColumn38 φ z s 1 0]) i j] := by
  ext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [fundamentalScaledKernel38, starProd38, Matrix.mul_apply, Fin.sum_univ_two] <;> ring <;> simp

theorem gradDiscrim38_cyclic (φ : PotPair) (z : ℂ) (s : ℝ) :
    gradDiscrim38 φ z s =
      ![Complex.I * (ext38 (fundContP φ z) s * monodromyPair φ z *
          (ext38 (fundContP φ z) s).adjugate) 1 0,
        -Complex.I * (ext38 (fundContP φ z) s * monodromyPair φ z *
          (ext38 (fundContP φ z) s).adjugate) 0 1] := by
  ext k
  fin_cases k <;> simp [gradDiscrim38, fundColumn38, starProd38, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two] <;> ring <;> simp

/-- The swap matrix is to the left of monodromy in the antitrace cyclic formula. -/
theorem gradAntiDiscrim38_cyclic (φ : PotPair) (z : ℂ) (s : ℝ) :
    gradAntiDiscrim38 φ z s =
      ![Complex.I * (ext38 (fundContP φ z) s * k1SwapMat38 * monodromyPair φ z *
          (ext38 (fundContP φ z) s).adjugate) 1 0,
        -Complex.I * (ext38 (fundContP φ z) s * k1SwapMat38 * monodromyPair φ z *
          (ext38 (fundContP φ z) s).adjugate) 0 1] := by
  ext k
  fin_cases k <;> simp [gradAntiDiscrim38, fundColumn38, starProd38, k1SwapMat38,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring <;> simp

end
end NlsGge.GK38
