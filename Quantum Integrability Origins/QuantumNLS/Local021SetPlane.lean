import Mathlib
import QuantumNLS.Local021Setting
import QuantumNLS.Local021Deriv

/-!
# LOCAL-021, stage 8d: plane normalization

`ζ̃` and `η = ζ̃⁻¹` restrict to the identity on every coordinate plane, hence `Ω = η^*ω` restricts to `ω` there (`planeOmega`), so `S` fixes the
plane pointwise (stage 5) and `Φ(c e_k) = c e_k = 𝓕(c e_k)` (`Phi_plane`).
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

theorem Plane.eq_single {k : ℤ} {y : K} (hy : y ∈ Plane k) : y = lp.single 2 k (y k) := by
  ext n
  by_cases hn : n = k
  · subst hn; simp
  · simp [lp.single_apply, hn, hy n hn]

theorem norm_apply_le (y : K) (k : ℤ) : ‖y k‖ ≤ ‖y‖ := lp.norm_apply_le_norm (by norm_num) y k

namespace Setting

variable (S : Setting L κ r hκ)

theorem zt_plane {k : ℤ} {y : K} (hy : y ∈ Plane k) (hyρ : y ∈ ball (0 : K) S.ρ) : S.zt y = y := by
  have h := S.zt_single k (y k) (lt_of_le_of_lt (norm_apply_le y k) (mem_ball_zero_iff.1 hyρ))
  rwa [← Plane.eq_single hy] at h

theorem eta_plane {k : ℤ} {y : K} (hy : y ∈ Plane k) (hyR : y ∈ ball (0 : K) S.R) : S.η y = y := by
  have h := S.eta_zeta y hyR
  have h2 : S.zt y = y := S.zt_plane hy (ball_subset_ball S.hRρ hyR)
  rw [show S.zt = zetaT L κ S.b S.rr from rfl] at h2
  rwa [h2] at h

theorem deta_plane {k : ℤ} {y : K} (hy : y ∈ Plane k) (hyR : y ∈ ball (0 : K) S.R) {v : K} (hv : v ∈ Plane k) :
    fderiv ℝ S.η y v = v := by
  have hd : DifferentiableAt ℝ S.η y := (S.eta_an y hyR).differentiableAt
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd' : HasFDerivAt S.η (fderiv ℝ S.η y) (y + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hev : (fun s : ℝ => S.η (y + s • v)) =ᶠ[𝓝 0] fun s => y + s • v := by
    have hc : ContinuousAt (fun s : ℝ => y + s • v) 0 := by fun_prop
    have hopen := hc.preimage_mem_nhds (isOpen_ball.mem_nhds (by simpa using hyR : y + (0 : ℝ) • v ∈ ball (0 : K) S.R))
    filter_upwards [hopen] with s hs
    exact S.eta_plane (Plane.add hy (Plane.smul_real hv s)) hs
  have h2 : HasDerivAt (fun s : ℝ => S.η (y + s • v)) v 0 := hline.congr_of_eventuallyEq hev
  have := h1.unique h2
  simpa using this

theorem planeOmega (k : ℤ) : PlaneOmega S.P S.B k := by
  intro y hy hyB v hv w hw
  have hyR : y ∈ ball (0 : K) S.R := ball_subset_ball S.radius_le hyB
  rw [S.hΩ y hyR, S.deta_plane hy hyR hv, S.deta_plane hy hyR hw]

theorem Sm_plane' {k : ℤ} {z : K} (hz : z ∈ Plane k) (hzr : ‖z‖ < S.rM) : S.Sm z = z :=
  Sm_plane S.B (S.planeOmega k) hz hzr

theorem Si_plane' {k : ℤ} {z : K} (hz : z ∈ Plane k) (hzr : ‖z‖ < S.rM) : S.Si z = z :=
  Si_plane S.B (S.planeOmega k) hz hzr

theorem Phi_plane (k : ℤ) (c : ℂ) (hc : ‖c‖ < S.rM) :
    S.Phi (c • modeLp L k) = fourierL2 L (c • modeLp L k) := by
  have hρ : ‖c‖ < S.ρ := lt_trans hc S.rM_lt_rho
  have h1 : zetaK L κ S.b S.rr (c • modeLp L k) = lp.single 2 k c := zetaK_plane S.fam k c hρ
  have h2 : fourierL2 L (c • modeLp L k) = lp.single 2 k c := by
    rw [map_smul, QuantumNLS.Fourier.fourierL2_modeLp]; ext n; simp [lp.single_apply, Pi.single_apply]
  unfold Phi
  rw [h1, h2]
  refine S.Si_plane' (k := k) (fun n hn => by simp [lp.single_apply, hn]) ?_
  have : ‖(lp.single 2 k c : K)‖ = ‖c‖ := by simp
  rw [this]; exact hc

end Setting

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.Setting.planeOmega
#print axioms QuantumNLS.Local021.Setting.Phi_plane
