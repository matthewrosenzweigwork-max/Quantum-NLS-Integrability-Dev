import Mathlib
import QuantumNLS.Local021Setting
import QuantumNLS.Local021ScaleFlow
import QuantumNLS.Local021ScaleAux

/-!
# LOCAL-021, stage 8c: coupling scaling for two settings

`Setting`s at couplings `κ` and `κ s²`: `ζ̃_κ(s x) = s ζ̃_{κ s²}(x)` (LOCAL-020 scaling clause), `η_κ(s y) = s η_{κ s²}(y)`, hence `Ω^κ_{s y} = Ω^{κ s²}_y`
as bilinear forms (`scaleΩ`, `local_covariance.tex:195`), and `Φ_κ(s u) = s Φ_{κ s²}(u)` (`Phi_scale`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)

variable {L κ r : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

namespace Setting

theorem zt_scale (SA : Setting L κ r hκ) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    (SB : Setting L (κ * s ^ 2) r hκ₂) {x : K} (hx₂ : ‖x‖ < SB.ρ) (hx : s * ‖x‖ < SA.ρ) :
    SA.zt (s • x) = s • SB.zt x := by
  unfold zt zetaT
  have e : s • x = (s : ℂ) • x := (Complex.coe_smul s x).symm
  rw [e, map_smul]
  have hu₂ : ‖(fourierL2 L).symm x‖ < SB.ρ := by rwa [LinearIsometryEquiv.norm_map]
  have hu : s * ‖(fourierL2 L).symm x‖ < SA.ρ := by rwa [LinearIsometryEquiv.norm_map]
  rw [zetaK_scale SA.fam hs hκ₂ SB.hρ SB.hC SB.fam hu₂ hu, Complex.coe_smul]
  rfl

theorem eta_scale (SA : Setting L κ r hκ) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    (SB : Setting L (κ * s ^ 2) r hκ₂) {y : K} (hy : y ∈ ball (0 : K) SB.R) (hsy : s • y ∈ ball (0 : K) SA.R) :
    SA.η (s • y) = s • SB.η y := by
  have hx := SB.eta_mem y hy
  have hxρ : SB.η y ∈ ball (0 : K) SB.ρ := ball_subset_ball SB.hRρ hx
  have hnorm : ‖SB.η y‖ = ‖y‖ := by
    have := SB.zt_norm hxρ
    rw [show SB.zt (SB.η y) = y from SB.zeta_eta y hy] at this
    exact this.symm
  have hsyn : s * ‖y‖ < SA.R := by
    have := mem_ball_zero_iff.1 hsy
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at this
  have h1 := SA.zt_scale hs hκ₂ SB (x := SB.η y) (by rw [hnorm]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hy) SB.hRρ)
    (by rw [hnorm]; exact lt_of_lt_of_le hsyn SA.hRρ)
  rw [show SB.zt (SB.η y) = y from SB.zeta_eta y hy] at h1
  have hsx : s • SB.η y ∈ ball (0 : K) SA.R := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs, hnorm]; exact hsyn
  have := SA.eta_zeta (s • SB.η y) hsx
  rw [show SA.zt = zetaT L κ SA.b SA.rr from rfl] at h1
  rw [show zetaT L κ SA.b SA.rr (s • SB.η y) = s • y from h1] at this
  exact this

theorem deta_scale (SA : Setting L κ r hκ) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    (SB : Setting L (κ * s ^ 2) r hκ₂) {y : K} (hy : y ∈ ball (0 : K) SB.R) (hsy : s • y ∈ ball (0 : K) SA.R) :
    fderiv ℝ SA.η (s • y) = fderiv ℝ SB.η y := by
  have hm1 : ∀ᶠ x in 𝓝 y, x ∈ ball (0 : K) SB.R := isOpen_ball.mem_nhds hy
  have hcont : ContinuousAt (fun x : K => s • x) y := (continuous_id.const_smul s).continuousAt
  have hm2 : ∀ᶠ x in 𝓝 y, s • x ∈ ball (0 : K) SA.R := hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hsy)
  have hev : (fun x => SA.η (s • x)) =ᶠ[𝓝 y] fun x => s • SB.η x := by
    filter_upwards [hm1, hm2] with x hx1 hx2
    exact SA.eta_scale hs hκ₂ SB hx1 hx2
  have h1 := fderiv_smul_scale (f := SA.η) (g := SB.η) (z := y) hs.ne' hs.ne' hev
  rw [inv_mul_cancel₀ hs.ne', one_smul] at h1
  exact h1

theorem scaleΩ_setting (SA : Setting L κ r hκ) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    (SB : Setting L (κ * s ^ 2) r hκ₂) : ScaleΩ SA.P SB.P s := by
  intro y hy hsy
  rw [SB.hPR] at hy
  rw [SA.hPR] at hsy
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  rw [SA.hΩ _ hsy, SB.hΩ _ hy, SA.deta_scale hs hκ₂ SB hy hsy]

theorem Phi_scale (SA : Setting L κ r hκ) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    (SB : Setting L (κ * s ^ 2) r hκ₂) {u : L2T L} (hu : ‖u‖ < SB.rM) (hsu : s * ‖u‖ < SA.rM) :
    SA.Phi ((s : ℂ) • u) = (s : ℂ) • SB.Phi u := by
  have hρB : ‖u‖ < SB.ρ := lt_trans hu SB.rM_lt_rho
  have hρA : s * ‖u‖ < SA.ρ := lt_trans hsu SA.rM_lt_rho
  unfold Phi
  rw [zetaK_scale SA.fam hs hκ₂ SB.hρ SB.hC SB.fam hρB hρA, Complex.coe_smul]
  have hmemB : u ∈ ball (0 : L2T L) SB.ρ := mem_ball_zero_iff.2 hρB
  have hw : ‖zetaK L (κ * s ^ 2) SB.b SB.rr u‖ = ‖u‖ := norm_zetaK SB.fam hmemB
  have := Si_scale SA.B SB.B hs (scaleΩ_setting SA hs hκ₂ SB)
    (w := zetaK L (κ * s ^ 2) SB.b SB.rr u) (by rw [hw]; exact hu) (by rw [hw]; exact hsu)
  rw [Complex.coe_smul]
  exact this

end Setting

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.Setting.scaleΩ_setting
#print axioms QuantumNLS.Local021.Setting.Phi_scale
