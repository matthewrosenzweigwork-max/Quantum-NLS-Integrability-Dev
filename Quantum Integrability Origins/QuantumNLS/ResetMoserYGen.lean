import QuantumNLS.ResetMoserYDiff

/-!
# `thm:reset-moser` (LOCAL-017), stage 4b: the Neumann solution `Y = Ycov(D, b)` over an arbitrary real normed parameter space

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "`Y_t` is analytic in `z`, continuous in `t`, and
`‖Y_t(z)‖ ≤ C‖z‖³`, `‖DY_t(z)‖ ≤ C‖z‖²`".  The frozen `ResetMoserYDiff` differentiates `z ↦ Ycov (D z) (b z)` for parameters `z ∈ K`;
the nonautonomous flow of the next stages needs the parameter `(z, t) ∈ K × ℝ`.  Here the same statements for an arbitrary real
normed space `X` of parameters:
* `hasFDerivAt_YcovX` and `norm_Ycov_derivX_le` (explicit derivative and the uniform operator bound);
* `analyticAt_YcovX` (analytic dependence of `Ycov (D x) (b x)` on analytic data, by analyticity of `Ring.inverse` at units).
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

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasFDerivAt_YcovX {D : X → Form} {b : X → Cov} {D' : X →L[ℝ] Form} {b' : X →L[ℝ] Cov} {z : X}
    (hD : HasFDerivAt D D' z) (hb : HasFDerivAt b b' z) (hsm : ‖D z‖ < 1) :
    ∃ L : X →L[ℝ] K, HasFDerivAt (fun w => Ycov (D w) (b w)) L z ∧
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

theorem norm_Ycov_derivX_le {D : X → Form} {b : X → Cov} {D' : X →L[ℝ] Form} {b' : X →L[ℝ] Cov} {z : X}
    (hsm : ‖D z‖ < 1) (h : X) :
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

theorem analyticAt_YcovX {D : X → Form} {b : X → Cov} {z : X}
    (hD : AnalyticAt ℝ D z) (hb : AnalyticAt ℝ b z) (hsm : ‖D z‖ < 1) :
    AnalyticAt ℝ (fun w => Ycov (D w) (b w)) z := by
  have hN0 : ‖Nop (D z)‖ < 1 := by have := norm_Nop_le (D z); linarith
  have hu : IsUnit (1 + Nop (D z)) := isUnit_one_add hN0
  let NopCLM : Form →L[ℝ] (K →L[ℝ] K) := (ContinuousLinearMap.compL ℝ K Cov K) (Jw.symm : Cov →L[ℝ] K)
  have h1 : AnalyticAt ℝ (fun w => 1 + Nop (D w)) z :=
    analyticAt_const.add ((NopCLM.analyticAt _).comp hD)
  have hinv : AnalyticAt ℝ (Ring.inverse : (K →L[ℝ] K) → (K →L[ℝ] K)) (1 + Nop (D z)) := by
    have := analyticAt_inverse (𝕜 := ℝ) hu.unit
    rwa [hu.unit_spec] at this
  have h2 : AnalyticAt ℝ (fun w => Ring.inverse (1 + Nop (D w))) z :=
    AnalyticAt.comp_of_eq (g := Ring.inverse) (f := fun w => 1 + Nop (D w)) hinv h1 rfl
  have h3 : AnalyticAt ℝ (fun w => Jw.symm (b w)) z :=
    ((Jw.symm : Cov →L[ℝ] K).analyticAt _).comp hb
  have hap : AnalyticAt ℝ (fun p : (K →L[ℝ] K) × K => p.1 p.2) (Ring.inverse (1 + Nop (D z)), Jw.symm (b z)) :=
    (ContinuousLinearMap.id ℝ (K →L[ℝ] K)).analyticAt_bilinear _
  exact (AnalyticAt.comp_of_eq (g := fun p : (K →L[ℝ] K) × K => p.1 p.2)
    (f := fun w => (Ring.inverse (1 + Nop (D w)), Jw.symm (b w))) hap (h2.prod h3) rfl).neg

theorem contDiffAt_YcovX {D : X → Form} {b : X → Cov} {z : X}
    (hD : AnalyticAt ℝ D z) (hb : AnalyticAt ℝ b z) (hsm : ‖D z‖ < 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun w => Ycov (D w) (b w)) z :=
  (analyticAt_YcovX hD hb hsm).contDiffAt

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.hasFDerivAt_YcovX
#print axioms QuantumNLS.ResetMoser.norm_Ycov_derivX_le
#print axioms QuantumNLS.ResetMoser.analyticAt_YcovX
#print axioms QuantumNLS.ResetMoser.contDiffAt_YcovX
