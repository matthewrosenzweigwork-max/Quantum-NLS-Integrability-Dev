import NlsGge.GK38.DirichletChar
import NlsGge.Spectral.ActualPhysicalFloquetCurrentPrimitive33V3

/-! Concrete Dirichlet reality from the actual period-one Green current.
Private source anchors: book I.6 Lemma 6.6, I.7 Lemma 7.2. -/
set_option autoImplicit false
open MeasureTheory
namespace NlsGge.GK38
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations

/-- Every actual Dirichlet root is real, including low-index roots. -/
theorem dirichletChar_root_real38 (u : PhysicalL2) (z : ℂ)
    (hz : dirichletChar (realSlice u) z = 0) : z.im = 0 := by
  have hb := (dirichletChar_zero_iff_boundary38 (realSlice u) z).mp hz
  rw [monodromyPair_realSlice] at hb
  have hstate : actualPhysicalFloquetState33 u z ![1, 1] 1 0 =
      actualPhysicalFloquetState33 u z ![1, 1] 1 1 := hb
  have hc : actualZsIndefiniteCurrent33 (actualPhysicalFloquetState33 u z ![1, 1] 1) = 0 := by
    simp only [actualZsIndefiniteCurrent33, hstate, sub_self]
  have hp := actualPhysicalFloquetCurrent_primitive33 u z ![1, 1] 1 (by norm_num)
  rw [hc] at hp
  have hzero : (∫ s in (0 : ℝ)..1, ((2*z.im : ℝ) : ℂ) *
      (actualPhysicalFloquetState33 u z ![1, 1] s 0 * star (actualPhysicalFloquetState33 u z ![1, 1] s 0) +
       actualPhysicalFloquetState33 u z ![1, 1] s 1 * star (actualPhysicalFloquetState33 u z ![1, 1] s 1))) = 0 := by
    simpa [actualZsIndefiniteCurrent33] using hp.symm
  rw [intervalIntegral.integral_const_mul] at hzero
  have he (s : ℝ) :
      actualPhysicalFloquetState33 u z ![1, 1] s 0 * star (actualPhysicalFloquetState33 u z ![1, 1] s 0) +
      actualPhysicalFloquetState33 u z ![1, 1] s 1 * star (actualPhysicalFloquetState33 u z ![1, 1] s 1) =
      ((‖actualPhysicalFloquetState33 u z ![1, 1] s 0‖ ^ 2 +
        ‖actualPhysicalFloquetState33 u z ![1, 1] s 1‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow]
  simp_rw [he] at hzero
  rw [intervalIntegral.integral_ofReal] at hzero
  have hv : (![1, 1] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have hh := congrArg (fun v => v 0) h
    simpa using hh
  have hpos := actualPhysicalFloquet_energy_integral_pos33 u z ![1, 1] hv
  have hnonzero : ((∫ s in (0 : ℝ)..1,
      ‖actualPhysicalFloquetState33 u z ![1, 1] s 0‖ ^ 2 +
      ‖actualPhysicalFloquetState33 u z ![1, 1] s 1‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hzr : ((2*z.im : ℝ) : ℂ) = 0 := (mul_eq_zero.mp hzero).resolve_right hnonzero
  have hreal : 2*z.im = 0 := by exact_mod_cast hzr
  nlinarith

/-- Reality is established before exposing a real-valued root sequence. -/
theorem muSeq_real38 (u : PhysicalL2) (n : ℤ) : (muSeq (realSlice u) n).im = 0 :=
  dirichletChar_root_real38 u _ (muSeq_root38 (realSlice u) n)

/-- The actual D1 label's real part, after its reality proof. -/
def gkMu (u : PhysicalL2) (n : ℤ) : ℝ := (muSeq (realSlice u) n).re

theorem muSeq_eq_gkMu38 (u : PhysicalL2) (n : ℤ) :
    muSeq (realSlice u) n = (gkMu u n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using muSeq_real38 u n

theorem gkMu_root38 (u : PhysicalL2) (n : ℤ) :
    dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 := by
  rw [← muSeq_eq_gkMu38]
  exact muSeq_root38 (realSlice u) n

end
end NlsGge.GK38
