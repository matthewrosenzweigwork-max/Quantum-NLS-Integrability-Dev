import NlsGge.Spectral.GenericRoughMatrixDysonFactorial32V1
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
/-- Scalar homogeneity of each actual-defined ordered matrix Dyson term.
No integrability is assumed to hide a limit: this is finite-order algebra
and the unconditional bounded scalar map identity for the totalized integral. -/
theorem genericRoughMatrixDysonTerm_scalarHomogeneity36V2
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    ∀ (n : ℕ) (t : ℝ),
      genericRoughMatrixDysonTerm32 (fun s => c • B s) n t =
        c^n • genericRoughMatrixDysonTerm32 B n t := by
  intro n
  induction n with
  | zero =>
    intro t
    simp [genericRoughMatrixDysonTerm32]
  | succ n ih =>
    intro t
    ext i j
    change (∫ s in (0 : ℝ)..t,
      ((c • B s) * genericRoughMatrixDysonTerm32 (fun s => c • B s) n s) i j) =
      c^(n+1) * ∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B n s) i j
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [ih s]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, pow_succ]
    <;> ring
end NlsGge.SpectralFoundations
end
