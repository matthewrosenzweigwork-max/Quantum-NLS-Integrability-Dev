import NlsGge.Spectral.ComplexZsGlobalSolutionOnIccAfterFiniteGluingV6
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance liouvilleMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance liouvilleMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

/-- Liouville's determinant identity for the actual complex-parameter ZS system
on its proved closed interval. -/
theorem determinant_eq_one_of_normalized_actual_complexZs_solution_Icc
    (u : ℝ → ℂ) (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF0 : F 0 = 1)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
        (Set.Icc (0 : ℝ) 2) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 2, Matrix.det (F t) = 1 := by
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 2) := by
    intro t ht
    exact (hF t ht).continuousWithinAt
  have hdetcont : ContinuousOn (fun t : ℝ => Matrix.det (F t))
      (Set.Icc (0 : ℝ) 2) :=
    (continuous_id.matrix_det).comp_continuousOn hFcont
  have hdetRight : ∀ t ∈ Set.Ico (0 : ℝ) 2,
      HasDerivWithinAt (fun x : ℝ => Matrix.det (F x)) 0 (Set.Ici t) t := by
    intro t ht
    have hFt := hF t ⟨ht.1, ht.2.le⟩
    change HasDerivWithinAt
      (fun x : ℝ => fun i : Fin 2 => fun j : Fin 2 => F x i j)
      (fun i : Fin 2 => fun j : Fin 2 =>
        (zsCoefficientComplex u z t * F t) i j)
      (Set.Icc (0 : ℝ) 2) t at hFt
    have hEntry (i j : Fin 2) :
        HasDerivWithinAt (fun x : ℝ => F x i j)
          ((zsCoefficientComplex u z t * F t) i j)
          (Set.Icc (0 : ℝ) 2) t := by
      exact (hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hFt i) j)
    have h00 := (hEntry 0 0).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    have h01 := (hEntry 0 1).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    have h10 := (hEntry 1 0).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    have h11 := (hEntry 1 1).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    have hdetEntry : HasDerivWithinAt
        (fun x : ℝ => F x 0 0 * F x 1 1 - F x 0 1 * F x 1 0)
        (((zsCoefficientComplex u z t * F t) 0 0) * F t 1 1 +
            F t 0 0 * ((zsCoefficientComplex u z t * F t) 1 1) -
          (((zsCoefficientComplex u z t * F t) 0 1) * F t 1 0 +
            F t 0 1 * ((zsCoefficientComplex u z t * F t) 1 0)))
        (Set.Ici t) t := by
      exact (h00.mul h11).sub (h01.mul h10)
    have hderivZero :
        (((zsCoefficientComplex u z t * F t) 0 0) * F t 1 1 +
            F t 0 0 * ((zsCoefficientComplex u z t * F t) 1 1) -
          (((zsCoefficientComplex u z t * F t) 0 1) * F t 1 0 +
            F t 0 1 * ((zsCoefficientComplex u z t * F t) 1 0))) = 0 := by
      simp [zsCoefficientComplex, Matrix.mul_apply]
      ring
    have hdetEntry' := hdetEntry.congr
      (fun x _ => Matrix.det_fin_two (F x))
      (Matrix.det_fin_two (F t))
    have hdetEntry'' := hdetEntry'.congr_deriv hderivZero
    simpa using hdetEntry''
  have hconst := constant_of_has_deriv_right_zero hdetcont hdetRight
  intro t ht
  have hval := hconst t ht
  simpa [hF0] using hval

end NlsGge.SpectralFoundations

end
