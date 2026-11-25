import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.Basic.NNReal.Defs

/-!
Two small scalar bridges isolated from the exhausted local-Picard assembly:
entrywise continuity of the actual complex spectral coefficient, and the
real coercion of the NNReal Picard radius constant.  Neither declaration
asserts matrix-valued continuity or an ODE solution.
-/

open scoped NNReal

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

theorem continuousOn_zsCoefficientComplex_entry
    (u : ℝ → ℂ) (z : ℂ) (δ : ℝ) (hδ : δ ≤ 2)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => zsCoefficientComplex u z t i j)
      (Set.Icc (0 : ℝ) δ) := by
  have huδ : ContinuousOn u (Set.Icc (0 : ℝ) δ) :=
    hu.mono (fun t ht => ⟨ht.1, le_trans ht.2 hδ⟩)
  fin_cases i <;> fin_cases j
  · simpa [zsCoefficientComplex] using
      (continuousOn_const : ContinuousOn
        (fun _ : ℝ => (-Complex.I * z)) (Set.Icc (0 : ℝ) δ))
  · refine ContinuousOn.congr
      ((continuousOn_const : ContinuousOn
        (fun _ : ℝ => Complex.I) (Set.Icc (0 : ℝ) δ)).mul huδ) ?_
    intro t ht
    simp [zsCoefficientComplex, Pi.mul_apply]
  · refine ContinuousOn.congr
      ((continuousOn_const : ContinuousOn
        (fun _ : ℝ => -Complex.I) (Set.Icc (0 : ℝ) δ)).mul huδ.star) ?_
    intro t ht
    simp [zsCoefficientComplex, Pi.mul_apply, neg_mul]
  · simpa [zsCoefficientComplex] using
      (continuousOn_const : ContinuousOn
        (fun _ : ℝ => Complex.I * z) (Set.Icc (0 : ℝ) δ))

theorem coe_zsPicardRadiusConstant
    (Kcoeff : ℝ≥0) (C : ℝ) (hKcoeff : (Kcoeff : ℝ) = 2 * C) :
    ((Kcoeff * Real.toNNReal (2 : ℝ) : ℝ≥0) : ℝ) = C * 4 := by
  rw [NNReal.coe_mul]
  rw [hKcoeff]
  rw [Real.coe_toNNReal 2 (by norm_num)]
  ring

end NlsGge.SpectralFoundations
