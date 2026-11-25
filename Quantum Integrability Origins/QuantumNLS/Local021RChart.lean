import Mathlib
import QuantumNLS.Local021Final

/-!
# LOCAL-021 repair, stage R2: the exact-modulus chart (without the Moser data)

`Chart` is the part of the frozen `Local021Setting.Setting` that is the printed premise of `prop:reset-moser-covariance`
("the preceding exact-modulus family is a full analytic diffeomorphism between Hilbert balls"): a LOCAL-020 family `Fam020` on a ball `ρ`
together with `ζ̃ = ζ ∘ 𝓕⁻¹ : K → K` real analytic on `B_R` with real-analytic inverse `η` onto `B_R` (`R ≤ ρ`).  The Moser data
(`PrintedHyp`, `PrintedBounds`) are NOT part of a `Chart`; the repair constructs them (`Local021RSetting`).

Facts derived here from the chart alone (the same arguments as in the frozen `Setting` API, with no Moser data):
`zt_norm`, `zt_cov`, `zt_neg`, `zt_single`, `fderiv_zt_zero` (`Dζ̃(0) = 1`), `eta_neg` (`η` odd), `dη_dzt`, `dzt_dη`
(`Dη_{ζ̃x} ∘ Dζ̃_x = 1`, `Dζ̃_{ηy} ∘ Dη_y = 1`), `fderiv_eta_zero`, `eta_quad` (`‖Dη_y − 1‖ ≤ C‖y‖²` near `0`).
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

namespace QuantumNLS.Local021R

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021

variable {L κ r : ℝ} [Fact (0 < L)]

/-- The exact-modulus chart: the printed premise (a LOCAL-020 family and a full analytic diffeomorphism of the ball `B_R`). -/
structure Chart (L κ r : ℝ) [Fact (0 < L)] (hκ : 0 < κ) where
  ρ : ℝ
  C : ℝ
  a : ℤ → L2T L → ℝ
  b : ℤ → L2T L → ℂ
  rr : L2T L → (ℤ →ᵇ ℝ)
  hρ : 0 < ρ
  hC : 0 ≤ C
  fam : Fam020 L κ r ρ C hκ a b rr
  R : ℝ
  hR : 0 < R
  hRρ : R ≤ ρ
  η : K → K
  zeta_an : AnalyticOnNhd ℝ (zetaT L κ b rr) (ball (0 : K) R)
  eta_an : AnalyticOnNhd ℝ η (ball (0 : K) R)
  eta_mem : ∀ y ∈ ball (0 : K) R, η y ∈ ball (0 : K) R
  zeta_eta : ∀ y ∈ ball (0 : K) R, zetaT L κ b rr (η y) = y
  eta_zeta : ∀ x ∈ ball (0 : K) R, η (zetaT L κ b rr x) = x

namespace Chart

variable {hκ : 0 < κ} (Ch : Chart L κ r hκ)

/-- `ζ̃` of the chart. -/
def zt : K → K := zetaT L κ Ch.b Ch.rr

theorem zt_norm {x : K} (hx : x ∈ ball (0 : K) Ch.ρ) : ‖Ch.zt x‖ = ‖x‖ := by
  unfold zt zetaT
  have hu : (fourierL2 L).symm x ∈ ball (0 : L2T L) Ch.ρ := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
  rw [norm_zetaK Ch.fam hu, LinearIsometryEquiv.norm_map]

theorem zt_cov (s : SymKind) {x : K} (hx : x ∈ ball (0 : K) Ch.ρ) :
    Ch.zt ((s.mono L).act x) = (s.mono L).act (Ch.zt x) := by
  unfold zt zetaT
  rw [Setting.fourier_symm_act]
  have hu : (fourierL2 L).symm x ∈ ball (0 : L2T L) Ch.ρ := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
  exact zetaK_cov Ch.fam s hu

theorem zt_neg {x : K} (hx : x ∈ ball (0 : K) Ch.ρ) : Ch.zt (-x) = -Ch.zt x := by
  have hU : ((SymKind.phase Real.pi).mono L).act x = -x := by
    ext n
    simp [SymKind.mono, Mono.cj, Complex.exp_pi_mul_I]
  have := Ch.zt_cov (SymKind.phase Real.pi) hx
  rw [hU] at this
  rw [this]
  ext n
  simp [SymKind.mono, Mono.cj, Complex.exp_pi_mul_I]

theorem zt_single (k : ℤ) (c : ℂ) (hc : ‖c‖ < Ch.ρ) : Ch.zt (lp.single 2 k c) = lp.single 2 k c := by
  unfold zt zetaT
  rw [fourier_symm_single]
  exact zetaK_plane Ch.fam k c hc

theorem zt_zero : Ch.zt 0 = 0 :=
  norm_eq_zero.1 (by rw [Ch.zt_norm (mem_ball_self Ch.hρ), norm_zero])

theorem fderiv_zt_zero : fderiv ℝ Ch.zt 0 = ContinuousLinearMap.id ℝ K := by
  have hd : DifferentiableAt ℝ Ch.zt 0 := (Ch.zeta_an 0 (mem_ball_self Ch.hR)).differentiableAt
  refine eq_of_single_eq fun n c => ?_
  set h : K := lp.single 2 n c with hh
  have hline : HasDerivAt (fun s : ℝ => s • h) h 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hd' : HasFDerivAt Ch.zt (fderiv ℝ Ch.zt 0) ((0 : ℝ) • h) := by simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hev : (fun s : ℝ => Ch.zt (s • h)) =ᶠ[𝓝 0] fun s => s • h := by
    have hlim : Tendsto (fun s : ℝ => ‖(s : ℂ) * c‖) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun s : ℝ => ‖(s : ℂ) * c‖) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hlim.eventually (gt_mem_nhds Ch.hρ)] with s hs
    rw [hh, real_smul_single]
    exact Ch.zt_single n _ hs
  have h2 : HasDerivAt (fun s : ℝ => Ch.zt (s • h)) h 0 := hline.congr_of_eventuallyEq hev
  have := h1.unique h2
  simpa using this

theorem zt_mem_ball {x : K} (hx : x ∈ ball (0 : K) Ch.R) : Ch.zt x ∈ ball (0 : K) Ch.R := by
  have hxρ : x ∈ ball (0 : K) Ch.ρ := ball_subset_ball Ch.hRρ hx
  rw [mem_ball_zero_iff, Ch.zt_norm hxρ]; exact mem_ball_zero_iff.1 hx

theorem eta_neg {y : K} (hy : y ∈ ball (0 : K) Ch.R) : Ch.η (-y) = -Ch.η y := by
  have hx := Ch.eta_mem y hy
  have hxρ : Ch.η y ∈ ball (0 : K) Ch.ρ := ball_subset_ball Ch.hRρ hx
  have h1 : Ch.zt (-Ch.η y) = -y := by
    rw [Ch.zt_neg hxρ]
    have := Ch.zeta_eta y hy
    exact congrArg Neg.neg this
  have hmx : -Ch.η y ∈ ball (0 : K) Ch.R := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
  have := Ch.eta_zeta _ hmx
  rw [show zetaT L κ Ch.b Ch.rr = Ch.zt from rfl, h1] at this
  exact this

/-- `Dη_{ζ̃ x} ∘ Dζ̃_x = 1`. -/
theorem deta_dzt {x : K} (hx : x ∈ ball (0 : K) Ch.R) :
    (fderiv ℝ Ch.η (Ch.zt x)).comp (fderiv ℝ Ch.zt x) = ContinuousLinearMap.id ℝ K := by
  have hz : DifferentiableAt ℝ Ch.zt x := (Ch.zeta_an x hx).differentiableAt
  have he : DifferentiableAt ℝ Ch.η (Ch.zt x) := (Ch.eta_an _ (Ch.zt_mem_ball hx)).differentiableAt
  have h1 : HasFDerivAt (Ch.η ∘ Ch.zt) ((fderiv ℝ Ch.η (Ch.zt x)).comp (fderiv ℝ Ch.zt x)) x :=
    he.hasFDerivAt.comp x hz.hasFDerivAt
  have hev : (Ch.η ∘ Ch.zt) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    exact Ch.eta_zeta w hw
  have h2 : HasFDerivAt (Ch.η ∘ Ch.zt) (ContinuousLinearMap.id ℝ K) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hev
  exact h1.unique h2

/-- `Dζ̃_{η y} ∘ Dη_y = 1`. -/
theorem dzt_deta {y : K} (hy : y ∈ ball (0 : K) Ch.R) :
    (fderiv ℝ Ch.zt (Ch.η y)).comp (fderiv ℝ Ch.η y) = ContinuousLinearMap.id ℝ K := by
  have he : DifferentiableAt ℝ Ch.η y := (Ch.eta_an y hy).differentiableAt
  have hz : DifferentiableAt ℝ Ch.zt (Ch.η y) := (Ch.zeta_an _ (Ch.eta_mem y hy)).differentiableAt
  have h1 : HasFDerivAt (Ch.zt ∘ Ch.η) ((fderiv ℝ Ch.zt (Ch.η y)).comp (fderiv ℝ Ch.η y)) y :=
    hz.hasFDerivAt.comp y he.hasFDerivAt
  have hev : (Ch.zt ∘ Ch.η) =ᶠ[𝓝 y] id := by
    filter_upwards [isOpen_ball.mem_nhds hy] with w hw
    exact Ch.zeta_eta w hw
  have h2 : HasFDerivAt (Ch.zt ∘ Ch.η) (ContinuousLinearMap.id ℝ K) y :=
    (hasFDerivAt_id y).congr_of_eventuallyEq hev
  exact h1.unique h2

theorem fderiv_eta_zero : fderiv ℝ Ch.η 0 = ContinuousLinearMap.id ℝ K := by
  have := Ch.deta_dzt (mem_ball_self Ch.hR)
  rw [Ch.zt_zero, Ch.fderiv_zt_zero] at this
  simpa using this

theorem eta_quad : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y : K, ‖y‖ < δ → ‖fderiv ℝ Ch.η y - 1‖ ≤ C * ‖y‖ ^ 2 := by
  have hf : ContDiffAt ℝ 3 Ch.η 0 := (Ch.eta_an 0 (mem_ball_self Ch.hR)).contDiffAt.of_le le_top
  have hodd : ∀ᶠ y in 𝓝 (0 : K), Ch.η (-y) = -Ch.η y := by
    filter_upwards [ball_mem_nhds (0 : K) Ch.hR] with y hy
    exact Ch.eta_neg hy
  obtain ⟨C, δ, hC, hδ, h⟩ := quad_of_odd hf hodd
  refine ⟨C, δ, hC, hδ, fun y hy => ?_⟩
  have := h y hy
  rwa [Ch.fderiv_eta_zero] at this

end Chart

end QuantumNLS.Local021R

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021R.Chart.fderiv_zt_zero
#print axioms QuantumNLS.Local021R.Chart.eta_neg
#print axioms QuantumNLS.Local021R.Chart.deta_dzt
#print axioms QuantumNLS.Local021R.Chart.dzt_deta
#print axioms QuantumNLS.Local021R.Chart.eta_quad
