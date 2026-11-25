import QuantumNLS.ResetMoserCone
import QuantumNLS.ResetMoserFlowGlobal

/-!
# `thm:reset-moser` (LOCAL-017), stage 2b-iii: the Hamiltonian flows `φ_j` of `Hyp` as `FlowOn` flows on every ball `B_ρ`, `ρ ≤ R`

Source: `symplectic_correction.tex`, proof of `thm:reset-moser`, "The periods of a radial primitive" (the loop `s ↦ φ_j^s(z)` and its
variation) and the Hypothesis "their Hamiltonian flows exist on `B_R` and have time `2π` equal to the identity".

* `Hyp.Xn_contDiffAt`: the Hamiltonian field `X_j = Ycov(Ω − ω, −dq_j)` is `C¹` (indeed `C²`) at every point of `B_R`
  (analyticity of `Ω`, `Ring.inverse` is smooth at units, `q_j` is smooth);
* `Hyp.flowOn`: for `0 < ρ ≤ R`, `φ_j` is a `FlowOn` flow of `X_j` on `B_ρ` (the balls are invariant by conservation of the norm
  `Hyp.norm_flow`);
* the consequences of `ResetMoserFlowGlobal` for `φ_j`: `Hyp.diffAt_flow`, `Hyp.variational_flow`, `Hyp.fderiv_group_flow`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow

theorem contDiff_q (n : ℤ) : ContDiff ℝ ⊤ (q n) := by
  have : q n = fun z : K => ‖evalR n z‖ ^ 2 := rfl
  rw [this]
  exact (contDiff_norm_sq ℝ).comp (evalR n).contDiff

theorem contDiff_fderiv_q (n : ℤ) : ContDiff ℝ 1 (fderiv ℝ (q n)) :=
  (contDiff_q n).fderiv_right (m := 1) (by norm_num)

theorem Hyp.Xn_contDiffAt (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j : ℤ) :
    ContDiffAt ℝ 1 (Xn S.Ω j) z := by
  have hD : ContDiffAt ℝ 1 (fun w => S.Ω w - omegaF) z :=
    ((S.Ω_contDiffAt hz).of_le (by norm_num)).sub contDiffAt_const
  have hNclm : ContDiff ℝ 1 (fun D : Form => Nop D) :=
    ((ContinuousLinearMap.compL ℝ K Cov K) (Jw.symm : Cov →L[ℝ] K)).contDiff
  have hN : ContDiffAt ℝ 1 (fun w => Nop (S.Ω w - omegaF)) z := hNclm.contDiffAt.comp z hD
  have h1 : ContDiffAt ℝ 1 (fun w => 1 + Nop (S.Ω w - omegaF)) z := contDiffAt_const.add hN
  have hu : IsUnit (1 + Nop (S.Ω z - omegaF)) := by
    have hlt := S.Ω_lt z hz
    have := norm_Nop_le (S.Ω z - omegaF)
    exact isUnit_one_add (by linarith)
  have h2 : ContDiffAt ℝ 1 (fun w => Ring.inverse (1 + Nop (S.Ω w - omegaF))) z := by
    have := contDiffAt_ringInverse ℝ (n := 1) hu.unit
    rw [IsUnit.unit_spec] at this
    exact this.comp z h1
  have hb : ContDiffAt ℝ 1 (fun w => -(fderiv ℝ (q j) w)) z := (contDiff_fderiv_q j).contDiffAt.neg
  have h3 : ContDiffAt ℝ 1 (fun w => Jw.symm (-(fderiv ℝ (q j) w))) z := Jw.symm.contDiff.contDiffAt.comp z hb
  exact (h2.clm_apply h3).neg

theorem Hyp.flowOn (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) (j : ℤ) :
    FlowOn (Xn S.Ω j) (S.φ j) (ball (0 : K) ρ) where
  isOpen := isOpen_ball
  cd := fun z hz => (S.Xn_contDiffAt (ball_subset_ball hρ hz) j).contDiffWithinAt
  deriv := fun v hv t => S.φ_deriv j v (ball_subset_ball hρ hv) t
  mem := fun v hv t => by
    have hvR := ball_subset_ball hρ hv
    rw [mem_ball_zero_iff] at hv ⊢
    rw [S.norm_flow hvR j t]
    exact hv
  zero := fun v _ => S.φ_zero j v

theorem Hyp.diffAt_flow (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) (t : ℝ) :
    DifferentiableAt ℝ (S.φ j t) z :=
  diffAt (S.flowOn hρ j) hz t

theorem Hyp.fderiv_group_flow (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ)
    (s t : ℝ) :
    fderiv ℝ (S.φ j (s + t)) z = (fderiv ℝ (S.φ j t) (S.φ j s z)).comp (fderiv ℝ (S.φ j s) z) :=
  fderiv_group (S.flowOn hρ j) hz s t

theorem Hyp.variational_flow (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) (s : ℝ) :
    HasDerivAt (fun r => fderiv ℝ (S.φ j r) z)
      ((fderiv ℝ (Xn S.Ω j) (S.φ j s z)).comp (fderiv ℝ (S.φ j s) z)) s :=
  variational (S.flowOn hρ j) hz s

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Hyp.Xn_contDiffAt
#print axioms QuantumNLS.ResetMoser.Hyp.flowOn
#print axioms QuantumNLS.ResetMoser.Hyp.variational_flow
