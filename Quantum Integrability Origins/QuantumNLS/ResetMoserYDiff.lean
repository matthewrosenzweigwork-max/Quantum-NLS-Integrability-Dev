import QuantumNLS.ResetMoserAngular

/-!
# `thm:reset-moser` (LOCAL-017), stage 4a: the derivative of the Neumann solution `Y = Ycov(D, b)` and its operator bound

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "The inverse of the associated real operator
exists by the Neumann series, uniformly in `t` and `z`. Consequently `Y_t` is analytic in `z`, continuous in `t`, and
`‖Y_t(z)‖ ≤ C‖z‖³`, `‖DY_t(z)‖ ≤ C‖z‖²` (eq:reset-Y-bounds)". Here the differentiation and the bound for a general pair of
differentiable families `D : K → Form` (`‖D‖ < 1`) and `b : K → Cov`; the bound is explicit and uniform:

* `norm_ringInverse_apply_le`: `‖(1 + J⁻¹D)⁻¹ v‖ ≤ 2‖v‖`;
* `hasFDerivAt_Ycov`: if `D, b` are Fréchet differentiable at `z` with derivatives `D', b'` and `‖D z‖ < 1`, then
  `z ↦ Ycov (D z) (b z)` is Fréchet differentiable at `z` with derivative `L`,
  `L h = −(1 + J⁻¹D_z)⁻¹ ( (J⁻¹ D'h) Y + J⁻¹ b'h )`, `Y = Ycov (D z) (b z)`, and
  `‖L h‖ ≤ (‖D'‖ ‖b z‖ + ‖b'‖) ‖h‖`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket

theorem Ycov_eq {D : Form} (hD : ‖D‖ < 1) (b : Cov) :
    Ycov D b = -((Ring.inverse (1 + Nop D)) (Jw.symm b)) := rfl

theorem mul_inverse_apply {D : Form} (hD : ‖D‖ < 1) (v : K) :
    (1 + Nop D) ((Ring.inverse (1 + Nop D)) v) = v := by
  have hN : ‖Nop D‖ < 1 := by have := norm_Nop_le D; linarith
  have h1 : ((1 + Nop D) * Ring.inverse (1 + Nop D)) = 1 := Ring.mul_inverse_cancel _ (isUnit_one_add hN)
  have := congrArg (fun T => T v) h1
  simpa using this

theorem norm_ringInverse_apply_le {D : Form} (hD : ‖D‖ < 1) (v : K) :
    ‖(Ring.inverse (1 + Nop D)) v‖ ≤ 2 * ‖v‖ := by
  set w := (Ring.inverse (1 + Nop D)) v with hw
  have h1 : (1 + Nop D) w = v := mul_inverse_apply hD v
  have h2 : w = v - Nop D w := by
    have : (1 + Nop D) w = w + Nop D w := by simp
    rw [this] at h1
    rw [← h1]; abel
  have h3 : ‖Nop D w‖ ≤ ‖D‖ / 2 * ‖w‖ :=
    ((Nop D).le_opNorm w).trans (mul_le_mul_of_nonneg_right (norm_Nop_le D) (norm_nonneg _))
  have h4 : ‖w‖ ≤ ‖v‖ + ‖Nop D w‖ := by
    calc ‖w‖ = ‖v - Nop D w‖ := by rw [← h2]
      _ ≤ ‖v‖ + ‖Nop D w‖ := norm_sub_le _ _
  nlinarith [norm_nonneg w, norm_nonneg D]

/-- **Differentiation of the Neumann solution.** -/
theorem hasFDerivAt_Ycov {D : K → Form} {b : K → Cov} {D' : K →L[ℝ] Form} {b' : K →L[ℝ] Cov} {z : K}
    (hD : HasFDerivAt D D' z) (hb : HasFDerivAt b b' z) (hsm : ‖D z‖ < 1) :
    ∃ L : K →L[ℝ] K, HasFDerivAt (fun w => Ycov (D w) (b w)) L z ∧
      ∀ h, L h = -((Ring.inverse (1 + Nop (D z))) (Nop (D' h) (Ycov (D z) (b z)) + Jw.symm (b' h))) := by
  have hN0 : ‖Nop (D z)‖ < 1 := by have := norm_Nop_le (D z); linarith
  have hu : IsUnit (1 + Nop (D z)) := isUnit_one_add hN0
  let NopCLM : Form →L[ℝ] (K →L[ℝ] K) := (ContinuousLinearMap.compL ℝ K Cov K) (Jw.symm : Cov →L[ℝ] K)
  have hNop : ∀ E : Form, NopCLM E = Nop E := fun E => rfl
  have hN : HasFDerivAt (fun w => 1 + Nop (D w)) (NopCLM.comp D') z :=
    ((NopCLM.hasFDerivAt.comp z hD).const_add 1)
  have hinv0 := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have e : ((hu.unit : (K →L[ℝ] K)ˣ) : K →L[ℝ] K) = 1 + Nop (D z) := hu.unit_spec
  rw [e] at hinv0
  have hcomp := hinv0.comp z hN
  have hu' : HasFDerivAt (fun w => Jw.symm (b w)) ((Jw.symm : Cov →L[ℝ] K).comp b') z :=
    (Jw.symm : Cov →L[ℝ] K).hasFDerivAt.comp z hb
  have happ := hcomp.clm_apply hu'
  have einv : ((↑(hu.unit⁻¹) : K →L[ℝ] K)) = Ring.inverse (1 + Nop (D z)) := by
    have := Ring.inverse_unit hu.unit
    rw [e] at this
    exact this.symm
  refine ⟨_, happ.neg, fun h => ?_⟩
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mulLeftRight_apply, Function.comp_apply, hNop, einv]
  rw [Ycov_eq (by exact hsm)]
  simp only [map_add, map_neg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.coe_mul]
  simp only [neg_smul, one_smul, ContinuousLinearEquiv.coe_coe]
  abel

theorem norm_Ycov_deriv_le {D : K → Form} {b : K → Cov} {D' : K →L[ℝ] Form} {b' : K →L[ℝ] Cov} {z : K}
    (hsm : ‖D z‖ < 1) (h : K) :
    ‖-((Ring.inverse (1 + Nop (D z))) (Nop (D' h) (Ycov (D z) (b z)) + Jw.symm (b' h)))‖ ≤
      (‖D'‖ * ‖b z‖ + ‖b'‖) * ‖h‖ := by
  rw [norm_neg]
  refine (norm_ringInverse_apply_le hsm _).trans ?_
  have hY : ‖Ycov (D z) (b z)‖ ≤ ‖b z‖ := norm_Ycov_le hsm (b z)
  have h1 : ‖Nop (D' h) (Ycov (D z) (b z))‖ ≤ ‖D'‖ * ‖h‖ / 2 * ‖b z‖ := by
    calc ‖Nop (D' h) (Ycov (D z) (b z))‖ ≤ ‖Nop (D' h)‖ * ‖Ycov (D z) (b z)‖ := (Nop (D' h)).le_opNorm _
      _ ≤ (‖D' h‖ / 2) * ‖b z‖ := mul_le_mul (norm_Nop_le _) hY (norm_nonneg _) (by positivity)
      _ ≤ ‖D'‖ * ‖h‖ / 2 * ‖b z‖ := by
          gcongr
          exact D'.le_opNorm h
  have h2 : ‖Jw.symm (b' h)‖ ≤ ‖b'‖ * ‖h‖ / 2 :=
    (norm_Jw_symm_le _).trans (by have := b'.le_opNorm h; linarith)
  have h3 := norm_add_le (Nop (D' h) (Ycov (D z) (b z))) (Jw.symm (b' h))
  nlinarith

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.norm_ringInverse_apply_le
#print axioms QuantumNLS.ResetMoser.hasFDerivAt_Ycov
#print axioms QuantumNLS.ResetMoser.norm_Ycov_deriv_le
