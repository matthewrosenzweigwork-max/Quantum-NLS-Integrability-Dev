import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Concrete definitions taken from the paper's self-adjoint periodic ZS operator.
This file intentionally does not assert existence of a fundamental solution or
define quasimomentum, gap endpoints, or gap height. Those are outstanding E02
proof obligations, not fields to assume in an interface.
-/

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The coefficient matrix obtained by solving `L_u ψ = spectralParam ψ` for `ψ'`. -/
def zsCoefficient (u : ℝ → ℂ) (spectralParam : ℝ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-Complex.I * (spectralParam : ℂ)), (Complex.I * u x);
    (-Complex.I * star (u x)), (Complex.I * (spectralParam : ℂ))]

/-- A global fundamental solution of the concrete ZS first-order system. -/
def IsZsFundamentalSolution (u : ℝ → ℂ) (spectralParam : ℝ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  F 0 = 1 ∧ ∀ x : ℝ,
    HasDerivAt F (zsCoefficient u spectralParam x * F x) x

/-- Monodromy over the specified period; period one and period two stay distinct. -/
def zsMonodromy (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (period : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := F period

/-- The full (unhalved) trace of monodromy over the specified period. -/
def zsFullTrace (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (period : ℝ) : ℂ :=
  Matrix.trace (zsMonodromy F period)

/-- The exact free-field fundamental matrix, offered as a concrete test object. -/
def freeZsFundamental (spectralParam x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * (spectralParam : ℂ) * (x : ℂ)), 0;
    0, Complex.exp (Complex.I * (spectralParam : ℂ) * (x : ℂ))]

/-- The coefficient matrix has the trace-zero normalization of the source system. -/
theorem trace_zsCoefficient (u : ℝ → ℂ) (spectralParam x : ℝ) :
    Matrix.trace (zsCoefficient u spectralParam x) = 0 := by
  simp [zsCoefficient, Matrix.trace]

end NlsGge.SpectralFoundations
