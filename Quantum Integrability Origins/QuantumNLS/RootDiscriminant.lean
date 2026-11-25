import Mathlib
import QuantumNLS.LinearFundamental

/-!
# R-7E0532E7 `thm:root-spectral-density`: properties of the discriminant `Δ_u(t) = tr M(L,t)` (continuous-representative class)

Consumes the realized DEF-013 objects `SpatialTransfer.spatialTransfer` / `discriminant` and `LinearFundamental`
(existence + uniqueness of the fundamental solution for continuous `u`) read-only.

* `spatialTransfer_symm`: for REAL `t`, `M(x,t) = P conj(M(x,t)) P` (`P` the swap): `M₁₁ = conj M₀₀`, `M₁₀ = conj M₀₁`
  (both fundamental solutions of the same equation, uniqueness); hence **`Δ_u(t)` is real** (`discriminant_im_eq_zero`,
  `discriminant_eq_two_re`).
* `det_spatialTransfer`: `det M(x,z) = 1` for every `z ∈ ℂ` (trace-free coefficient; Liouville/Abel formula by entries).
* consequently `|M₀₀|² - |M₀₁|² = 1` for real `t` (`norm_sq_sub_eq_one`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootDiscriminant

/-- `m ↦ P conj(m) P`, `P` the swap matrix: `(cswap m)_{ij} = conj m_{(1-i)(1-j)}`. -/
def cswap : Mat2 →ₗ[ℝ] Mat2 where
  toFun m := Matrix.of fun i j => conj (m i.rev j.rev)
  map_add' a b := by ext i j; simp
  map_smul' r m := by ext i j; simp

def cswapCLM : Mat2 →L[ℝ] Mat2 := LinearMap.toContinuousLinearMap cswap

theorem cswapCLM_apply (m : Mat2) (i j : Fin 2) : cswapCLM m i j = conj (m i.rev j.rev) := rfl

theorem cswap_one : cswapCLM (1 : Mat2) = 1 := by
  ext i j
  rw [cswapCLM_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-- For real `t` the coefficient is invariant under `m ↦ P conj(m) P`. -/
theorem cswap_mul_coef (κ : ℝ) (u : ℝ → ℂ) (t : ℝ) (x : ℝ) (Y : Mat2) :
    cswapCLM (balCoef κ u (t : ℂ) x * Y) = balCoef κ u (t : ℂ) x * cswapCLM Y := by
  ext i j
  rw [cswapCLM_apply]
  fin_cases i <;> fin_cases j <;>
    simp [balCoef, coef, Matrix.mul_apply, Fin.sum_univ_two, cswapCLM_apply, map_ofNat] <;> ring

/-- **`M(x,t) = P conj(M(x,t)) P` for real `t`** (uniqueness of the fundamental solution). -/
theorem spatialTransfer_symm (κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (t : ℝ) :
    (fun x => cswapCLM (spatialTransfer κ u (t : ℂ) x)) = spatialTransfer κ u (t : ℂ) := by
  have hM := spatialTransfer_spec' κ hu (t : ℂ)
  refine IsFundamental.unique (continuous_coef _ _ hu (t : ℂ)) ⟨?_, fun x => ?_⟩ hM
  · show cswapCLM (spatialTransfer κ u (t : ℂ) 0) = 1
    rw [hM.1, cswap_one]
  · have := cswapCLM.hasFDerivAt.comp_hasDerivAt x (hM.2 x)
    exact this.congr_deriv (cswap_mul_coef κ u t x (spatialTransfer κ u (t : ℂ) x))

theorem spatialTransfer_symm_apply (κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (t : ℝ) (x : ℝ) (i j : Fin 2) :
    spatialTransfer κ u (t : ℂ) x i j = conj (spatialTransfer κ u (t : ℂ) x i.rev j.rev) := by
  have := congrFun (spatialTransfer_symm κ hu t) x
  calc spatialTransfer κ u (t : ℂ) x i j = (cswapCLM (spatialTransfer κ u (t : ℂ) x)) i j := by
        rw [this]
    _ = _ := cswapCLM_apply _ _ _

/-- **`Δ_u(t)` is real for real `t`.** -/
theorem discriminant_eq_two_re (L κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (t : ℝ) :
    discriminant L κ u (t : ℂ) = (((2 * (spatialTransfer κ u (t : ℂ) L 0 0).re : ℝ)) : ℂ) := by
  have h11 := spatialTransfer_symm_apply κ hu t L 1 1
  unfold discriminant
  rw [Matrix.trace_fin_two]
  have hr1 : (1 : Fin 2).rev = 0 := rfl
  have hr0 : (0 : Fin 2).rev = 1 := rfl
  simp only [hr1, hr0] at h11
  rw [h11]
  apply Complex.ext <;> simp <;> ring

theorem discriminant_im_eq_zero (L κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (t : ℝ) :
    (discriminant L κ u (t : ℂ)).im = 0 := by
  rw [discriminant_eq_two_re L κ hu t]; simp

/-- Real-valued discriminant on the real axis. -/
def discReal (L κ : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℝ := (discriminant L κ u (t : ℂ)).re

theorem discriminant_eq_discReal (L κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (t : ℝ) :
    discriminant L κ u (t : ℂ) = (discReal L κ u t : ℂ) := by
  apply Complex.ext
  · simp [discReal]
  · simp [discriminant_im_eq_zero L κ hu t]

/-! ### Determinant one -/

/-- Entry map as a complex continuous linear functional. -/
def entryCLM (i j : Fin 2) : Mat2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)

theorem hasDerivAt_entry {M : ℝ → Mat2} {M' : Mat2} {x : ℝ} (h : HasDerivAt M M' x) (i j : Fin 2) :
    HasDerivAt (fun y => M y i j) (M' i j) x :=
  ((entryCLM i j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x h

/-- **`det M(x,z) = 1`** for every `z ∈ ℂ` (the coefficient matrix has trace zero). -/
theorem det_spatialTransfer (κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) (x : ℝ) :
    (spatialTransfer κ u z x).det = 1 := by
  have hM := spatialTransfer_spec' κ hu z
  set M := spatialTransfer κ u z with hMdef
  have e : ∀ y i j, HasDerivAt (fun s => M s i j) ((balCoef κ u z y * M y) i j) y :=
    fun y i j => hasDerivAt_entry (hM.2 y) i j
  have hg : ∀ y, HasDerivAt (fun s => (M s).det) 0 y := by
    intro y
    have h1 := ((e y 0 0).mul (e y 1 1)).sub ((e y 0 1).mul (e y 1 0))
    have hfun : (fun s => (M s).det) = fun s => M s 0 0 * M s 1 1 - M s 0 1 * M s 1 0 := by
      funext s; rw [Matrix.det_fin_two]
    rw [hfun]
    refine h1.congr_deriv ?_
    simp only [balCoef, coef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hconst := is_const_of_deriv_eq_zero (f := fun s => (M s).det)
    (fun y => (hg y).differentiableAt) (fun y => (hg y).deriv) x 0
  rw [hconst, hM.1]
  simp

/-- For real `t`: `|M₀₀|² - |M₀₁|² = 1` (J-unitarity in the form `det = p p̄ - q q̄`). -/
theorem norm_sq_sub_eq_one (κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (t : ℝ) (x : ℝ) :
    ‖spatialTransfer κ u (t : ℂ) x 0 0‖ ^ 2 - ‖spatialTransfer κ u (t : ℂ) x 0 1‖ ^ 2 = 1 := by
  have hd := det_spatialTransfer κ hu (t : ℂ) x
  rw [Matrix.det_fin_two] at hd
  have h11 := spatialTransfer_symm_apply κ hu t x 1 1
  have h10 := spatialTransfer_symm_apply κ hu t x 1 0
  have hr1 : (1 : Fin 2).rev = 0 := rfl
  have hr0 : (0 : Fin 2).rev = 1 := rfl
  simp only [hr1, hr0] at h11 h10
  rw [h11, h10] at hd
  have : ((‖spatialTransfer κ u (t : ℂ) x 0 0‖ ^ 2 - ‖spatialTransfer κ u (t : ℂ) x 0 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hd, Complex.mul_conj, Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  exact_mod_cast this

#print axioms discriminant_eq_two_re
#print axioms det_spatialTransfer
#print axioms norm_sq_sub_eq_one

end QuantumNLS.RootDiscriminant
