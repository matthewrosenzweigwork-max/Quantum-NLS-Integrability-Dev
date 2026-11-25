import QuantumNLS.ResetMoserCone

/-!
# `thm:reset-moser` (LOCAL-017), stage 4-prep: shrinking the radius of the hypotheses

Source: `symplectic_correction.tex`, `thm:reset-moser` ("on a smaller ball `B_r`") and the proof's "All balls below may be decreased a fixed number of times".
The Haar primitive (`LOCAL017Haar.reset_moser_hann`) supplies `hann` on `B_ρ` with `ρ ≤ S.R`; the Moser argument is then run for the restricted datum.

`Hyp.restrict S ρ`: the datum `S` with radius `R := ρ` (`0 < ρ ≤ S.R`): same `Ω`, same flows `φ`; the flows stay in `B_ρ` because they preserve the norm
(`Hyp.norm_flow`). `restrict_Loc`: a local-bounds bundle for `S` on radius `ρ` is one for the restriction.
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

/-- The hypotheses of `thm:reset-moser` on the smaller ball `B_ρ`. -/
def Hyp.restrict (S : Hyp) (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ S.R) : Hyp where
  R := ρ
  R_pos := hρ
  Ω := S.Ω
  Ω_alt := S.Ω_alt
  Ω_analytic := fun z hz => S.Ω_analytic z (ball_subset_ball hρR hz)
  Ω_closed := fun z hz => S.Ω_closed z (ball_subset_ball hρR hz)
  Ω_quad := by
    obtain ⟨C, hC⟩ := S.Ω_quad
    exact ⟨C, fun z hz => hC z (ball_subset_ball hρR hz)⟩
  Ω_lt := fun z hz => S.Ω_lt z (ball_subset_ball hρR hz)
  φ := S.φ
  φ_zero := S.φ_zero
  φ_mem := fun n z hz t => by
    have h := S.norm_flow (ball_subset_ball hρR hz) n t
    rw [mem_ball_zero_iff] at hz ⊢
    rw [h]; exact hz
  φ_deriv := fun n z hz t => S.φ_deriv n z (ball_subset_ball hρR hz) t
  φ_period := fun n z hz => S.φ_period n z (ball_subset_ball hρR hz)
  poisson := fun m n z hz => S.poisson m n z (ball_subset_ball hρR hz)

theorem Hyp.restrict_Ω (S : Hyp) (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ S.R) : (S.restrict ρ hρ hρR).Ω = S.Ω := rfl

theorem Hyp.restrict_R (S : Hyp) (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ S.R) : (S.restrict ρ hρ hρR).R = ρ := rfl

theorem Hyp.restrict_φ (S : Hyp) (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ S.R) : (S.restrict ρ hρ hρR).φ = S.φ := rfl

theorem Hyp.restrict_Xn (S : Hyp) (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ S.R) (n : ℤ) :
    Xn (S.restrict ρ hρ hρR).Ω n = Xn S.Ω n := rfl

theorem Hyp.restrict_Loc (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) :
    Loc (S.restrict ρ hL.ρpos hL.ρR) ρ M where
  ρpos := hL.ρpos
  ρR := le_rfl
  M0 := hL.M0
  b2 := hL.b2
  b1 := hL.b1
  b0 := hL.b0

theorem Hyp.restrict_betaR (S : Hyp) (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ S.R) :
    betaR (S.restrict ρ hρ hρR) = betaR S := rfl

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Hyp.restrict
#print axioms QuantumNLS.ResetMoser.Hyp.restrict_Loc
