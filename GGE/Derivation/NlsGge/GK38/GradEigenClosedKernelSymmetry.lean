import NlsGge.GK38.GradEigenClosedKernelAlgebra
import NlsGge.GK38.GradEigenClosedMonodromy
import NlsGge.GK38.GradEigenClosedDerivative
import NlsGge.GK38.GradEigenKernelInjective
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem realSymmetric_add (g k : PairKernelCont38) (hg : realSymmetric g) (hk : realSymmetric k) :
    realSymmetric (g+k) := by
  intro t
  change g t 1+k t 1=star (g t 0+k t 0)
  rw [star_add,hg,hk]

theorem realSymmetric_sub (g k : PairKernelCont38) (hg : realSymmetric g) (hk : realSymmetric k) :
    realSymmetric (g-k) := by
  intro t
  change g t 1-k t 1=star (g t 0-k t 0)
  rw [star_sub,hg,hk]

theorem realSymmetric_smul (c : ℂ) (g : PairKernelCont38)
    (hc : star c=c) (hg : realSymmetric g) : realSymmetric (c • g) := by
  intro t
  change c*g t 1=star (c*g t 0)
  rw [star_mul,hc,hg]
  ring

theorem realSymmetric_square (g : PairKernelCont38) (hg : realSymmetric g) :
    realSymmetric (square g) := by
  intro t
  change g t 0*g t 0=star (g t 1*g t 1)
  rw [hg,star_mul,star_star]

theorem realSymmetric_normalizedSquare (g : PairKernelCont38) (hg : realSymmetric g) :
    realSymmetric (normalizedSquare g) := by
  apply realSymmetric_smul _ _ _ (realSymmetric_square g hg)
  rw [← Complex.ofReal_inv]
  simp

theorem realSymmetric_gradAnti (u : PhysicalL2) (x : ℝ) :
    realSymmetric (gradAntiDiscrimCont38 (realSlice u) (x : ℂ)) := by
  intro t
  have hs (i j : Fin 2) :
      star (ext38 (fundContP (realSlice u) (x : ℂ)) (t : ℝ) i j)=
        ext38 (fundContP (realSlice u) (x : ℂ)) (t : ℝ) i.rev j.rev := by
    rw [ext38_of_mem _ t.2]
    exact fundPair_real_entry_star38 u x t i j
  have h0 : (0 : Fin 2).rev=1 := rfl
  have h1 : (1 : Fin 2).rev=0 := rfl
  have hI : star Complex.I= -Complex.I := by simp
  change gradAntiDiscrim38 (realSlice u) (x : ℂ) (t : ℝ) 1=
    star (gradAntiDiscrim38 (realSlice u) (x : ℂ) (t : ℝ) 0)
  simp only [gradAntiDiscrim38,starProd38,fundColumn38,Pi.smul_apply,smul_eq_mul,
    Pi.add_apply,Pi.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    star_mul,star_add,star_sub,star_neg,hI,monodromyPair_real_entry_star38,hs]
  simp only [h0,h1]
  ring

theorem realSymmetric_closedKernel1 (u : PhysicalL2) (n : ℤ) : realSymmetric (closedKernel1 u n) :=
  realSymmetric_sub _ _ (realSymmetric_normalizedSquare _ (dirState_real_symmetry u n))
    (realSymmetric_normalizedSquare _ (neuState_real_symmetry u n))

theorem realSymmetric_closedKernel2 (u : PhysicalL2) (n : ℤ) : realSymmetric (closedKernel2 u n) := by
  apply realSymmetric_add
  · apply realSymmetric_smul _ _ _ (realSymmetric_normalizedSquare _ (dirState_real_symmetry u n))
    apply Complex.ext
    · simp
    · change -(spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ)).im=
        (spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ)).im
      rw [spectralAnti_real]
      simp
  · exact realSymmetric_gradAnti u (gkMu u n)

end
end NlsGge.GK38.GradEigen38
