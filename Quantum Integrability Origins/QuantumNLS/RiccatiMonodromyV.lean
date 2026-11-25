import Mathlib
import QuantumNLS.SpatialTransfer
import QuantumNLS.LinearFundamental
import QuantumNLS.RiccatiFloquet
import QuantumNLS.RiccatiMonodromy

/-!
# R-3FEAD88B step A: monodromy trace for independent profiles (classical, continuous level)

Generalisation of `QuantumNLS.RiccatiMonodromy.trace_monodromy`: the two entries of the
coefficient matrix are independent continuous profiles `u` and `v`:

`A(x) = [[-iz/2, κ v(x)], [u(x), iz/2]]`   (`coefV κ u v z`).

If `r` solves `r' = iz r + u - κ v r²` on `ℝ` and is `L`-periodic, then for every fundamental
matrix `Mu` of `A` on `[0, L]`, `tr Mu(L) = m + m⁻¹` with
`m = ψ(L) = exp(-izL/2 + κ ∫₀ᴸ v r)`.

Specialisation `u = f`, `v = conj f` recovers the frozen theorem `RiccatiMonodromy.trace_monodromy`
(`trace_monodromy_eq_classical` below).

Scope: continuous `u`, `v`, pointwise `C¹` Riccati solution `r`. No sorry, admit, native_decide
or custom axioms. Frozen modules are imported, not edited.
-/

namespace QuantumNLS.RiccatiMonodromyV

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open Complex Set Filter Topology ComplexConjugate
open QuantumNLS.SpatialTransfer
open QuantumNLS.RiccatiMonodromy (eZero eOne companion eq_zero_of_linear_ode det_fundamental_one)

/-- Coefficient matrix with independent profiles: `[[-iz/2, κ v(x)], [u(x), iz/2]]`. -/
noncomputable def coefV (κ : ℝ) (u v : ℝ → ℂ) (z : ℂ) (x : ℝ) : Mat2 :=
  !![-(Complex.I * z) / 2, (κ : ℂ) * v x; u x, Complex.I * z / 2]

/-- Log-derivative of the companion component: `g = -iz/2 + κ (v · r)`. -/
noncomputable def gcoefV (κ : ℝ) (v r : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  -(Complex.I * z) / 2 + (κ : ℂ) * (v x * r x)

/-- Companion component `ψ(x) = exp(∫₀ˣ g)` for independent `v`. -/
noncomputable def psiV (κ : ℝ) (v r : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (∫ s in (0 : ℝ)..x, gcoefV κ v r z s)

theorem continuous_coefV (κ : ℝ) {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v) (z : ℂ) :
    Continuous (coefV κ u v z) := by
  unfold coefV
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem gcoefV_continuous (κ : ℝ) {v r : ℝ → ℂ} (z : ℂ) (hv : Continuous v) (hr : Continuous r) :
    Continuous (gcoefV κ v r z) := by
  unfold gcoefV
  exact continuous_const.add (continuous_const.mul (hv.mul hr))

theorem psiV_hasDerivAt (κ : ℝ) {v r : ℝ → ℂ} {z : ℂ} (hg : Continuous (gcoefV κ v r z))
    (x : ℝ) : HasDerivAt (psiV κ v r z) (gcoefV κ v r z x * psiV κ v r z x) x := by
  have h := (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.cexp
  exact h.congr_deriv (by simp only [psiV]; ring)

theorem psiV_zero (κ : ℝ) (v r : ℝ → ℂ) (z : ℂ) : psiV κ v r z 0 = 1 := by
  simp [psiV]

/-- The companion field `W(x) = ψ(x) • [[1,0],[r x,0]]` solves `W' = A W` for `A = coefV κ u v z`. -/
theorem companion_hasDerivAtV {κ : ℝ} {u v r : ℝ → ℂ} {z : ℂ} (hv : Continuous v)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + u x - (κ : ℂ) * v x * r x ^ 2) x)
    (x : ℝ) :
    HasDerivAt (fun y => psiV κ v r z y • companion r y)
      (coefV κ u v z x * (psiV κ v r z x • companion r x)) x := by
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun y => (hr y).continuousAt
  have hg := gcoefV_continuous κ z hv hrc
  have hp := psiV_hasDerivAt κ hg x
  have hC : HasDerivAt (fun y => eZero + r y • eOne)
      ((Complex.I * z * r x + u x - (κ : ℂ) * v x * r x ^ 2) • eOne) x :=
    ((hr x).smul_const eOne).const_add eZero
  refine (hp.smul hC).congr_deriv ?_
  unfold companion gcoefV coefV
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eZero, eOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply] <;>
    ring

/-- **Monodromy trace for independent profiles.** For continuous `u`, `v`, a pointwise `C¹`,
`L`-periodic solution `r` of `r' = iz r + u - κ v r²`, and any fundamental matrix `Mu` of
`coefV κ u v z`, `tr Mu(L) = m + m⁻¹` with `m = ψ(L) = exp(-izL/2 + κ ∫₀ᴸ v r)`. -/
theorem trace_monodromyV {L κ : ℝ} (hL : 0 < L) {u v r : ℝ → ℂ} {z : ℂ} (hu : Continuous u)
    (hv : Continuous v)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + u x - (κ : ℂ) * v x * r x ^ 2) x)
    (hper : r L = r 0) {Mu : ℝ → Mat2} (hMu : IsFundamental (coefV κ u v z) Mu) :
    (Mu L).trace = psiV κ v r z L + (psiV κ v r z L)⁻¹ := by
  obtain ⟨hM0, hMd⟩ := hMu
  have hA : Continuous (coefV κ u v z) := continuous_coefV κ hu hv z
  have htr : ∀ x, coefV κ u v z x 0 0 + coefV κ u v z x 1 1 = 0 := fun x => by
    simp [coefV] <;> ring
  have hdet : (Mu L).det = 1 := det_fundamental_one htr hMd hM0 L
  -- `D = Mu · [[1,0],[r 0,0]] - ψ · companion` solves the linear ODE with `D 0 = 0`
  have hD : ∀ y, HasDerivAt (fun y => Mu y * companion r 0 - psiV κ v r z y • companion r y)
      (coefV κ u v z y * (Mu y * companion r 0 - psiV κ v r z y • companion r y)) y := by
    intro y
    have h1 : HasDerivAt (fun y => Mu y * companion r 0)
        (coefV κ u v z y * Mu y * companion r 0) y := (hMd y).mul_const _
    refine ((h1.sub (companion_hasDerivAtV hv hr y))).congr_deriv ?_
    simp only [mul_sub, mul_assoc]
  have hD0 : Mu 0 * companion r 0 - psiV κ v r z 0 • companion r 0 = 0 := by
    rw [hM0, psiV_zero, one_mul, one_smul, sub_self]
  have hDL := eq_zero_of_linear_ode hA hL.le hD hD0 L ⟨hL.le, le_rfl⟩
  have hcomp : companion r L = companion r 0 := by
    unfold companion; rw [hper]
  rw [hcomp] at hDL
  have hEq : Mu L * companion r 0 = psiV κ v r z L • companion r 0 := sub_eq_zero.1 hDL
  have hmv : Matrix.mulVec (Mu L - psiV κ v r z L • (1 : Mat2)) ![1, r 0] = 0 := by
    funext i
    have h := congrFun (congrFun hEq i) 0
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, companion, eZero, eOne, Matrix.mul_apply,
        Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
      linear_combination h
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, companion, eZero, eOne, Matrix.mul_apply,
        Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
      linear_combination h
  have hv0 : (![1, r 0] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have heig : (Mu L - psiV κ v r z L • (1 : Mat2)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨![1, r 0], hv0, hmv⟩
  have hm : psiV κ v r z L ≠ 0 := by
    unfold psiV
    exact Complex.exp_ne_zero _
  exact QuantumNLS.RiccatiFloquet.trace_eq_of_det_one_eigen (Mu L) hdet (psiV κ v r z L) hm heig

/-- Bridge: the unbalanced coefficient is the independent-profile coefficient with `v = conj u`. -/
theorem unbalCoef_eq_coefV (κ : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    unbalCoef κ f z = coefV κ f (fun x => conj (f x)) z := by
  funext x
  unfold unbalCoef coef coefV
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Recovery of the frozen classical theorem: with `u = f`, `v = conj f` the monodromy trace of
`RiccatiMonodromy` is obtained from `trace_monodromyV`. -/
theorem trace_monodromy_eq_classical {L κ : ℝ} (hL : 0 < L) {f r : ℝ → ℂ} {z : ℂ}
    (hf : Continuous f)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + f x - (κ : ℂ) * conj (f x) * r x ^ 2) x)
    (hper : r L = r 0) {Mu : ℝ → Mat2} (hMu : IsFundamental (unbalCoef κ f z) Mu) :
    (Mu L).trace = QuantumNLS.RiccatiMonodromy.psi κ f r z L
      + (QuantumNLS.RiccatiMonodromy.psi κ f r z L)⁻¹ := by
  have hMu' : IsFundamental (coefV κ f (fun x => conj (f x)) z) Mu := by
    rw [← unbalCoef_eq_coefV]
    exact hMu
  exact trace_monodromyV hL hf (Complex.continuous_conj.comp hf) hr hper hMu'

end QuantumNLS.RiccatiMonodromyV

#print axioms QuantumNLS.RiccatiMonodromyV.continuous_coefV
#print axioms QuantumNLS.RiccatiMonodromyV.companion_hasDerivAtV
#print axioms QuantumNLS.RiccatiMonodromyV.trace_monodromyV
#print axioms QuantumNLS.RiccatiMonodromyV.unbalCoef_eq_coefV
#print axioms QuantumNLS.RiccatiMonodromyV.trace_monodromy_eq_classical
