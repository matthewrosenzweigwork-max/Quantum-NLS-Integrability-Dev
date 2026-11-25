import Mathlib
import NlsGge.Spectral.ActualComplexZsDysonVolterraWithinODEV3

/-!
# Zero-curvature (Lax) algebra for the Zakharov-Shabat pair of `i u_t = -u_xx + 2|u|^2 u` (B1)

Pointwise matrix algebra only.  With `A = zsA z u` (the project's ZS coefficient,
`zsCoefficientComplex`, which is the first-order form of `L_u ψ = z ψ`,
`L_u = i σ₃ ∂ₓ + [[0,u],[ū,0]]`, v2 l.120-123) and `V = zsV z u ux`, the zero-curvature
combination `V_x - [A, V]` has off-diagonal entries `-u_xx + 2|u|²u` and `conj` of it, and
so `A_t = V_x - [A,V]` (that is, `A_t = zsVx - [A,V]` with `A_t = !![0, i u_t; -i ū_t, 0]`)
holds exactly when `i u_t = -u_xx + 2|u|²u` (v2 `eq:nls`, coefficient 2 included).
Time-independent in `z`: the spectral parameter `z` is a free complex number.

This file is the normalization test of `campaign/GWP_PLAN.md` §2 (risk R9).
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate
open NlsGge.SpectralFoundations

namespace NlsGge.NLS38

/-- ZS coefficient matrix `U = [[-i z, i u],[-i ū, i z]]` (= `zsCoefficientComplex` at `(u,z)`). -/
def zsA (z u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(Complex.I * z), Complex.I * u; -(Complex.I * conj u), Complex.I * z]

/-- Time-component of the Lax pair. -/
def zsV (z u ux : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(2 * Complex.I * z ^ 2) - Complex.I * (u * conj u), 2 * Complex.I * z * u - ux;
     -(2 * Complex.I * z * conj u) - conj ux, 2 * Complex.I * z ^ 2 + Complex.I * (u * conj u)]

/-- The `x`-derivative of `zsV z (U x) (Ux x)` (with `V` regarded as a function of `x`). -/
def zsVx (z u ux uxx : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(Complex.I * (ux * conj u + u * conj ux)), 2 * Complex.I * z * ux - uxx;
     -(2 * Complex.I * z * conj ux) - conj uxx, Complex.I * (ux * conj u + u * conj ux)]

/-- `zsA` is the project's complex ZS coefficient. -/
theorem zsA_eq_zsCoefficientComplex (U : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    zsA z (U x) = zsCoefficientComplex U z x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsA, zsCoefficientComplex]

/-- The curvature `V_x - [A, V]` before the PDE is imposed: off-diagonal entries are
`-u_xx + 2|u|²u` and its conjugate; the diagonal vanishes identically. -/
theorem zs_curvature_explicit (z u ux uxx : ℂ) :
    zsVx z u ux uxx - (zsA z u * zsV z u ux - zsV z u ux * zsA z u) =
      !![0, -uxx + 2 * (u * conj u) * u;
         -conj uxx + 2 * (conj u * u) * conj u, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsVx, zsA, zsV, Matrix.sub_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Zero curvature: `A_t = V_x - [A, V]` iff `i u_t = -u_xx + 2|u|²u`. This direction is the
one used by Lax isospectrality (B3). -/
theorem zs_zero_curvature (z u ux uxx ut : ℂ)
    (hpde : Complex.I * ut = -uxx + 2 * (u * conj u) * u) :
    !![0, Complex.I * ut; -(Complex.I * conj ut), 0] =
      zsVx z u ux uxx - (zsA z u * zsV z u ux - zsV z u ux * zsA z u) := by
  rw [zs_curvature_explicit]
  have hc : -(Complex.I * conj ut) = -conj uxx + 2 * (conj u * u) * conj u := by
    have h := congrArg conj hpde
    simp only [map_mul, map_add, map_neg, map_ofNat, Complex.conj_I, Complex.conj_conj] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hpde, hc]

/-- Converse: if the zero-curvature identity holds then the PDE holds (the matrix identity
is equivalent to `eq:nls`, so the coefficient 2 is forced). -/
theorem zs_pde_of_zero_curvature (z u ux uxx ut : ℂ)
    (h : !![0, Complex.I * ut; -(Complex.I * conj ut), 0] =
      zsVx z u ux uxx - (zsA z u * zsV z u ux - zsV z u ux * zsA z u)) :
    Complex.I * ut = -uxx + 2 * (u * conj u) * u := by
  rw [zs_curvature_explicit] at h
  have := congrFun (congrFun h 0) 1
  simpa using this

/-- Normalization probe (negative): with the coefficient `3` instead of `2` the zero-curvature
identity fails (`u = 1`, `u_x = u_xx = 0`, `i u_t = 3`). -/
theorem zs_zero_curvature_fails_coeff3 :
    ¬ ∀ (z u ux uxx ut : ℂ),
      Complex.I * ut = -uxx + 3 * (u * conj u) * u →
      !![0, Complex.I * ut; -(Complex.I * conj ut), 0] =
        zsVx z u ux uxx - (zsA z u * zsV z u ux - zsV z u ux * zsA z u) := by
  intro h
  have := h 0 1 0 0 (-3 * Complex.I) (by
    simp [mul_comm]
    ring_nf; simp)
  have h2 := zs_pde_of_zero_curvature 0 1 0 0 (-3 * Complex.I) this
  simp at h2
  ring_nf at h2
  simp at h2

/-- Link with the actual half trace: the project's Dyson sum (the object inside
`actualPhysicalUnitHalfTrace32`, `tr(Ψ(1))/2`) solves exactly `Ψ' = zsA z (u t) * Ψ` on
`[0,2]`, the ODE whose Lax deformation `zs_zero_curvature` controls. -/
theorem hasDerivWithinAt_dyson_zsA (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    HasDerivWithinAt (fun x : ℝ => actualComplexZsDysonTsum u z x)
      (zsA z (u t) * actualComplexZsDysonTsum u z t) (Set.Icc (0 : ℝ) 2) t := by
  rw [zsA_eq_zsCoefficientComplex]
  exact hasDerivWithinAt_actualComplexZsDysonTsum_of_continuousOn u z hu t ht

end NlsGge.NLS38
