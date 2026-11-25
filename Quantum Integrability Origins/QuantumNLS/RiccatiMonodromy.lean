import Mathlib
import QuantumNLS.LinearFundamental
import QuantumNLS.RiccatiFloquet

/-!
# R-3FEAD88B item (a): monodromy eigenvalue of the Riccati transfer (classical, continuous level)

Coefficient matrix (unbalanced convention, `unbalCoef κ f z = coef κ 1 f z`):
`A(x) = [[-iz/2, κ conj(f x)], [f x, iz/2]]`.

If `r` solves the Riccati equation `r' = iz r + f - κ conj(f) r²` on `ℝ` and is `L`-periodic,
then `ψ(x) = exp(∫₀ˣ (-iz/2 + κ conj(f) r))` is a monodromy eigenvalue: the companion vector
`(1, r(0))` satisfies `M(L) v = ψ(L) v` for the fundamental matrix `M` of `A`. Since `det M(L) = 1`
(trace-free `A`, Liouville), `tr M(L) = ψ(L) + ψ(L)⁻¹`.

Scope: continuous profile `f`, pointwise `C¹` Riccati solution `r`. The L² / H^S identification
of the Riccati solution is NOT in this module. No sorry, admit, native_decide or custom axioms.
-/

namespace QuantumNLS.RiccatiMonodromy

open Complex Set Filter Topology ComplexConjugate
open QuantumNLS.SpatialTransfer

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Log-derivative of the companion component: `g = -iz/2 + κ (conj f · r)`. -/
noncomputable def gcoef (κ : ℝ) (f r : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  -(Complex.I * z) / 2 + (κ : ℂ) * (conj (f x) * r x)

/-- Companion component `ψ(x) = exp(∫₀ˣ g)`. -/
noncomputable def psi (κ : ℝ) (f r : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (∫ s in (0 : ℝ)..x, gcoef κ f r z s)

/-- The constant matrix `[[1,0],[0,0]]`. -/
def eZero : Mat2 := !![1, 0; 0, 0]

/-- The constant matrix `[[0,0],[1,0]]`. -/
def eOne : Mat2 := !![0, 0; 1, 0]

/-- Companion matrix `[[1,0],[r x,0]] = eZero + r x • eOne`. -/
def companion (r : ℝ → ℂ) (x : ℝ) : Mat2 := eZero + r x • eOne

theorem gcoef_continuous (κ : ℝ) {f r : ℝ → ℂ} (z : ℂ) (hf : Continuous f) (hr : Continuous r) :
    Continuous (gcoef κ f r z) := by
  unfold gcoef
  exact continuous_const.add (continuous_const.mul ((Complex.continuous_conj.comp hf).mul hr))

theorem psi_hasDerivAt (κ : ℝ) {f r : ℝ → ℂ} {z : ℂ} (hg : Continuous (gcoef κ f r z)) (x : ℝ) :
    HasDerivAt (psi κ f r z) (gcoef κ f r z x * psi κ f r z x) x := by
  have h := (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.cexp
  exact h.congr_deriv (by simp only [psi]; ring)

theorem psi_zero (κ : ℝ) (f r : ℝ → ℂ) (z : ℂ) : psi κ f r z 0 = 1 := by
  simp [psi]

/-- The companion vector field: `W(x) = ψ(x) • [[1,0],[r x,0]]` solves `W' = A W`. -/
theorem companion_hasDerivAt {κ : ℝ} {f r : ℝ → ℂ} {z : ℂ} (hf : Continuous f)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + f x - (κ : ℂ) * conj (f x) * r x ^ 2) x)
    (x : ℝ) :
    HasDerivAt (fun y => psi κ f r z y • companion r y)
      (unbalCoef κ f z x * (psi κ f r z x • companion r x)) x := by
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun y => (hr y).continuousAt
  have hg := gcoef_continuous κ z hf hrc
  have hp := psi_hasDerivAt κ hg x
  have hC : HasDerivAt (fun y => eZero + r y • eOne)
      ((Complex.I * z * r x + f x - (κ : ℂ) * conj (f x) * r x ^ 2) • eOne) x :=
    ((hr x).smul_const eOne).const_add eZero
  refine (hp.smul hC).congr_deriv ?_
  unfold companion gcoef unbalCoef coef
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eZero, eOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply] <;>
    ring

/-- Gronwall uniqueness for the linear matrix ODE on `[0, L]` with zero initial value. -/
theorem eq_zero_of_linear_ode {A : ℝ → Mat2} (hA : Continuous A) {D : ℝ → Mat2} {L : ℝ}
    (hL : 0 ≤ L) (hD : ∀ x, HasDerivAt D (A x * D x) x) (h0 : D 0 = 0) :
    ∀ x ∈ Icc 0 L, D x = 0 := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
    hA.continuousOn
  have key := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := fun x => A x * D x) (K := K) (a := 0) (b := L)
    (fun y _ => (hD y).continuousAt.continuousWithinAt)
    (fun y _ => (hD y).hasDerivWithinAt) h0
    (fun y hy => by
      have hy' : y ∈ Icc 0 L := ⟨hy.1, hy.2.le⟩
      calc ‖A y * D y‖ ≤ ‖A y‖ * ‖D y‖ := norm_mul_le _ _
        _ ≤ K * ‖D y‖ := mul_le_mul_of_nonneg_right (hK y hy') (norm_nonneg _))
  exact fun x hx => key x hx

/-- Entrywise derivative of a matrix-valued derivative. -/
theorem entry_hasDerivAt {F : ℝ → Mat2} {F' : Mat2} {x : ℝ} (h : HasDerivAt F F' x)
    (i j : Fin 2) : HasDerivAt (fun y => F y i j) (F' i j) x := by
  have hc := (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x h
  convert hc using 1
  all_goals first | rfl | simp

/-- Liouville for a trace-free coefficient: a fundamental matrix has determinant one. -/
theorem det_fundamental_one {A M : ℝ → Mat2} (htr : ∀ x, A x 0 0 + A x 1 1 = 0)
    (hM : ∀ x, HasDerivAt M (A x * M x) x) (h0 : M 0 = 1) (x : ℝ) : (M x).det = 1 := by
  have hfun : (fun y => (M y).det)
      = fun y => M y 0 0 * M y 1 1 - M y 0 1 * M y 1 0 :=
    funext fun y => Matrix.det_fin_two _
  have hd : ∀ y, HasDerivAt (fun y => (M y).det) 0 y := by
    intro y
    rw [hfun]
    have e := ((entry_hasDerivAt (hM y) 0 0).mul (entry_hasDerivAt (hM y) 1 1)).sub
      ((entry_hasDerivAt (hM y) 0 1).mul (entry_hasDerivAt (hM y) 1 0))
    refine e.congr_deriv ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (M y 0 0 * M y 1 1 - M y 0 1 * M y 1 0) * htr y
  have hconst := is_const_of_deriv_eq_zero (f := fun y => (M y).det)
    (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x 0
  simpa [h0] using hconst

/-- Linear identity `ψ(L) = exp(-izL/2 + κ J)` with `J = ∫₀ᴸ conj(f) r`. -/
theorem psi_eq_exp {κ : ℝ} {f r : ℝ → ℂ} {z : ℂ} (L : ℝ) (hf : Continuous f)
    (hr : Continuous r) :
    psi κ f r z L = Complex.exp (-(Complex.I * z * L / 2)
      + (κ : ℂ) * ∫ s in (0 : ℝ)..L, conj (f s) * r s) := by
  have hcont : Continuous (fun s => conj (f s) * r s) := (Complex.continuous_conj.comp hf).mul hr
  have h1 : ∫ s in (0 : ℝ)..L, (-(Complex.I * z) / 2 + (κ : ℂ) * (conj (f s) * r s))
      = (∫ s in (0 : ℝ)..L, -(Complex.I * z) / 2)
        + (κ : ℂ) * ∫ s in (0 : ℝ)..L, conj (f s) * r s := by
    have hI1 : Continuous (fun _ : ℝ => -(Complex.I * z) / 2) := continuous_const
    have hI2 : Continuous (fun s : ℝ => (κ : ℂ) * (conj (f s) * r s)) :=
      continuous_const.mul hcont
    rw [intervalIntegral.integral_add (hI1.intervalIntegrable 0 L) (hI2.intervalIntegrable 0 L),
      intervalIntegral.integral_const_mul]
  unfold psi gcoef
  rw [h1, intervalIntegral.integral_const]
  congr 1
  simp only [sub_zero, Complex.real_smul]
  ring

/-- **Monodromy eigenvalue and trace.** For a continuous profile `f`, a pointwise `C¹`,
`L`-periodic Riccati solution `r`, and any fundamental matrix `Mu` of the unbalanced coefficient,
`tr Mu(L) = m + m⁻¹` with `m = ψ(L) = exp(-izL/2 + κ ∫₀ᴸ conj(f) r)`. -/
theorem trace_monodromy {L κ : ℝ} (hL : 0 < L) {f r : ℝ → ℂ} {z : ℂ} (hf : Continuous f)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + f x - (κ : ℂ) * conj (f x) * r x ^ 2) x)
    (hper : r L = r 0) {Mu : ℝ → Mat2} (hMu : IsFundamental (unbalCoef κ f z) Mu) :
    (Mu L).trace = psi κ f r z L + (psi κ f r z L)⁻¹ := by
  obtain ⟨hM0, hMd⟩ := hMu
  have hA : Continuous (unbalCoef κ f z) := continuous_coef κ 1 hf z
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun y => (hr y).continuousAt
  have htr : ∀ x, unbalCoef κ f z x 0 0 + unbalCoef κ f z x 1 1 = 0 := fun x => by
    simp [unbalCoef, coef]; ring
  have hdet : (Mu L).det = 1 := det_fundamental_one htr hMd hM0 L
  -- the difference `D = Mu · [[1,0],[r 0,0]] - ψ · companion` solves the linear ODE with `D 0 = 0`
  have hD : ∀ y, HasDerivAt (fun y => Mu y * companion r 0 - psi κ f r z y • companion r y)
      (unbalCoef κ f z y * (Mu y * companion r 0 - psi κ f r z y • companion r y)) y := by
    intro y
    have h1 : HasDerivAt (fun y => Mu y * companion r 0)
        (unbalCoef κ f z y * Mu y * companion r 0) y := (hMd y).mul_const _
    refine ((h1.sub (companion_hasDerivAt hf hr y))).congr_deriv ?_
    simp only [mul_sub, mul_assoc]
  have hD0 : Mu 0 * companion r 0 - psi κ f r z 0 • companion r 0 = 0 := by
    rw [hM0, psi_zero, one_mul, one_smul, sub_self]
  have hDL := eq_zero_of_linear_ode hA hL.le hD hD0 L ⟨hL.le, le_rfl⟩
  have hcomp : companion r L = companion r 0 := by
    unfold companion; rw [hper]
  rw [hcomp] at hDL
  have hEq : Mu L * companion r 0 = psi κ f r z L • companion r 0 := sub_eq_zero.1 hDL
  have hmv : Matrix.mulVec (Mu L - psi κ f r z L • (1 : Mat2)) ![1, r 0] = 0 := by
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
  have heig : (Mu L - psi κ f r z L • (1 : Mat2)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨![1, r 0], hv0, hmv⟩
  have hm : psi κ f r z L ≠ 0 := by
    unfold psi
    exact Complex.exp_ne_zero _
  exact QuantumNLS.RiccatiFloquet.trace_eq_of_det_one_eigen (Mu L) hdet (psi κ f r z L) hm heig

/-- **Trace equals the discriminant for a continuous profile.** For `κ > 0`, the physical
discriminant `Δ = tr M(L)` of `SpatialTransfer` equals `m + m⁻¹` with the monodromy multiplier
`m = exp(-izL/2 + κ ∫₀ᴸ conj(f) r)`. -/
theorem discriminant_monodromy {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {f r : ℝ → ℂ} {z : ℂ}
    (hf : Continuous f)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + f x - (κ : ℂ) * conj (f x) * r x ^ 2) x)
    (hper : r L = r 0) :
    QuantumNLS.SpatialTransfer.discriminant L κ f z
      = psi κ f r z L + (psi κ f r z L)⁻¹ := by
  obtain ⟨Mu, hMu, hdisc⟩ := QuantumNLS.LinearFundamental.discriminant_eq_unbalanced L κ hκ hf z
  rw [hdisc]
  exact trace_monodromy hL hf hr hper hMu

end QuantumNLS.RiccatiMonodromy

#print axioms QuantumNLS.RiccatiMonodromy.psi_hasDerivAt
#print axioms QuantumNLS.RiccatiMonodromy.companion_hasDerivAt
#print axioms QuantumNLS.RiccatiMonodromy.eq_zero_of_linear_ode
#print axioms QuantumNLS.RiccatiMonodromy.det_fundamental_one
#print axioms QuantumNLS.RiccatiMonodromy.psi_eq_exp
#print axioms QuantumNLS.RiccatiMonodromy.trace_monodromy
#print axioms QuantumNLS.RiccatiMonodromy.discriminant_monodromy
