import Mathlib
import QuantumNLS.Local021Setting
import QuantumNLS.Local021Quad

/-!
# LOCAL-021, stage 8b: Fourier derivative at zero and the unit-coupling quadratic bound

Source: `local_covariance.tex:211-217`: "`Φ` ... has the Fourier derivative at zero.  The unit-coupling quadratic differential bound now becomes the
displayed estimate."

* `eq_of_single_eq` : bounded `ℝ`-linear maps on `ℓ²(ℤ)` agreeing on all `c e_k` are equal (density of finite sequences);
* `fderiv_zt_zero` : `Dζ̃(0) = 1` (from `ζ̃(c e_k) = c e_k` and differentiability at `0`);
* `zt_quad` : `‖Dζ̃(x) - 1‖ ≤ C ‖x‖²` near `0` (phase covariance makes `ζ̃` odd; `quad_of_odd`);
* `fderiv_PhiK` and `PhiK_quad` : `DΦ(0) = 1` and `‖DΦ(x) - 1‖ ≤ C‖x‖²` near `0`, `Φ = S⁻¹ ∘ ζ̃`.
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

variable {L κ r : ℝ} [Fact (0 < L)]

theorem eq_of_single_eq {A B : K →L[ℝ] K} (h : ∀ (n : ℤ) (c : ℂ), A (lp.single 2 n c) = B (lp.single 2 n c)) :
    A = B := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hs := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
  have hA := hs.mapL A
  have hB := hs.mapL B
  simp only [h] at hA
  exact hA.unique hB

theorem fourier_symm_single (k : ℤ) (c : ℂ) : (fourierL2 L).symm (lp.single 2 k c) = c • modeLp L k := by
  apply (fourierL2 L).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_smul, QuantumNLS.Fourier.fourierL2_modeLp]
  ext n
  simp [lp.single_apply, Pi.single_apply]

theorem real_smul_single (s : ℝ) (k : ℤ) (c : ℂ) :
    s • (lp.single 2 k c : K) = (lp.single (E := fun _ : ℤ => ℂ) 2 k ((s : ℂ) * c) : K) := by
  ext n
  simp [lp.single_apply, Pi.single_apply, Complex.real_smul]

namespace Setting

variable {hκ : 0 < κ} (S : Setting L κ r hκ)

theorem zt_single (k : ℤ) (c : ℂ) (hc : ‖c‖ < S.ρ) : S.zt (lp.single 2 k c) = lp.single 2 k c := by
  unfold zt zetaT
  rw [fourier_symm_single]
  exact zetaK_plane S.fam k c hc

theorem fderiv_zt_zero : fderiv ℝ S.zt 0 = ContinuousLinearMap.id ℝ K := by
  have hd : DifferentiableAt ℝ S.zt 0 := (S.zeta_an 0 (mem_ball_self S.hR)).differentiableAt
  refine eq_of_single_eq fun n c => ?_
  set h : K := lp.single 2 n c with hh
  have hline : HasDerivAt (fun s : ℝ => s • h) h 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hd' : HasFDerivAt S.zt (fderiv ℝ S.zt 0) ((0 : ℝ) • h) := by simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hev : (fun s : ℝ => S.zt (s • h)) =ᶠ[𝓝 0] fun s => s • h := by
    have hlim : Tendsto (fun s : ℝ => ‖(s : ℂ) * c‖) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun s : ℝ => ‖(s : ℂ) * c‖) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hlim.eventually (gt_mem_nhds S.hρ)] with s hs
    rw [hh, real_smul_single]
    exact S.zt_single n _ hs
  have h2 : HasDerivAt (fun s : ℝ => S.zt (s • h)) h 0 := hline.congr_of_eventuallyEq hev
  have := h1.unique h2
  simpa using this

theorem zt_neg {x : K} (hx : x ∈ ball (0 : K) S.ρ) : S.zt (-x) = -S.zt x := by
  have hU : ((SymKind.phase Real.pi).mono L).act x = -x := by
    ext n
    simp [SymKind.mono, Mono.cj, Complex.exp_pi_mul_I]
  have := S.zt_cov (SymKind.phase Real.pi) hx
  rw [hU] at this
  rw [this]
  ext n
  simp [SymKind.mono, Mono.cj, Complex.exp_pi_mul_I]

theorem zt_quad : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : K, ‖x‖ < δ → ‖fderiv ℝ S.zt x - 1‖ ≤ C * ‖x‖ ^ 2 := by
  have hf : ContDiffAt ℝ 3 S.zt 0 := (S.zeta_an 0 (mem_ball_self S.hR)).contDiffAt.of_le le_top
  have hodd : ∀ᶠ x in 𝓝 (0 : K), S.zt (-x) = -S.zt x := by
    filter_upwards [ball_mem_nhds (0 : K) S.hρ] with x hx
    exact S.zt_neg hx
  obtain ⟨C, δ, hC, hδ, h⟩ := quad_of_odd hf hodd
  refine ⟨C, δ, hC, hδ, fun x hx => ?_⟩
  have := h x hx
  rwa [S.fderiv_zt_zero] at this


/-- the Fourier transform `𝓕 : L²(𝕋_L) → ℓ²(ℤ)` as a real-linear homeomorphism. -/
def Fcle (L : ℝ) [Fact (0 < L)] : L2T L ≃L[ℝ] K where
  toFun := fun u => fourierL2 L u
  invFun := fun x => (fourierL2 L).symm x
  map_add' := fun u v => map_add (fourierL2 L) u v
  map_smul' := fun c u => by
    simp only [RingHom.id_apply]
    exact LinearMap.map_smul_of_tower (fourierL2 L).toLinearEquiv.toLinearMap c u
  left_inv := fun u => (fourierL2 L).symm_apply_apply u
  right_inv := fun x => (fourierL2 L).apply_symm_apply x
  continuous_toFun := (fourierL2 L).continuous
  continuous_invFun := (fourierL2 L).symm.continuous

/-- the Fourier transform as a real-linear bounded map (the `F` of the report). -/
def Fcl (L : ℝ) [Fact (0 < L)] : L2T L →L[ℝ] K := (Fcle L : L2T L →L[ℝ] K)

theorem Fcl_apply (u : L2T L) : Fcl L u = fourierL2 L u := rfl

theorem norm_Fcl_le : ‖Fcl L‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [Fcl_apply, LinearIsometryEquiv.norm_map, one_mul]

/-- `Φ` in Fourier variables, `Φ̂ = S⁻¹ ∘ ζ̃ : K → K`. -/
def PhiK : K → K := fun x => S.Si (S.zt x)

theorem Phi_eq (u : L2T L) : S.Phi u = S.PhiK (fourierL2 L u) := by
  unfold Phi PhiK zt zetaT
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem fderiv_Phi (u : L2T L) : fderiv ℝ S.Phi u = (fderiv ℝ S.PhiK (fourierL2 L u)).comp (Fcl L) := by
  have : S.Phi = S.PhiK ∘ ⇑(Fcle L) := funext fun u => S.Phi_eq u
  rw [this, (Fcle L).comp_right_fderiv]
  rfl

theorem hasFDerivAt_PhiK {x : K} (hx : ‖x‖ < S.rM) :
    HasFDerivAt S.PhiK ((fderiv ℝ S.Si (S.zt x)).comp (fderiv ℝ S.zt x)) x := by
  have hxρ : x ∈ ball (0 : K) S.ρ := mem_ball_zero_iff.2 (lt_trans hx S.rM_lt_rho)
  have hxR : x ∈ ball (0 : K) S.R := mem_ball_zero_iff.2 (lt_trans hx S.rM_lt_R)
  have hzt : DifferentiableAt ℝ S.zt x := (S.zeta_an x hxR).differentiableAt
  have hSi : DifferentiableAt ℝ S.Si (S.zt x) := by
    refine (S.MD.Tinv_analyticAt (w := S.zt x) ?_).differentiableAt
    rw [S.zt_norm hxρ]; exact hx
  exact hSi.hasFDerivAt.comp x hzt.hasFDerivAt

theorem fderiv_PhiK {x : K} (hx : ‖x‖ < S.rM) :
    fderiv ℝ S.PhiK x = (fderiv ℝ S.Si (S.zt x)).comp (fderiv ℝ S.zt x) := (S.hasFDerivAt_PhiK hx).fderiv

theorem Si_quad : ∃ CS : ℝ, 0 ≤ CS ∧ ∀ w : K, ‖w‖ < S.rM → ‖fderiv ℝ S.Si w - 1‖ ≤ CS * ‖w‖ ^ 2 := by
  obtain ⟨CS, hC0, -, -, -, -, -, -, -, h2⟩ := S.MD.sfl_corrects
  refine ⟨CS, hC0, fun w hw => ?_⟩
  have := h2 w (mem_ball_zero_iff.2 hw)
  have hn := norm_nonneg (fderiv ℝ (S.MD.Sfl 1) w - 1)
  exact le_trans (le_add_of_nonneg_left hn) this

theorem fderiv_PhiK_zero : fderiv ℝ S.PhiK 0 = 1 := by
  have h0 : ‖(0 : K)‖ < S.rM := by rw [norm_zero]; exact S.rM_pos
  rw [S.fderiv_PhiK h0]
  obtain ⟨CS, -, hCS⟩ := S.Si_quad
  have h1 := hCS 0 h0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h1
  have h2 : fderiv ℝ S.Si (S.zt 0) = 1 := by
    have := norm_nonneg (fderiv ℝ S.Si 0 - 1)
    have h3 : fderiv ℝ S.Si 0 - 1 = 0 := norm_le_zero_iff.1 (by linarith)
    have h4 : S.zt 0 = 0 :=
      norm_eq_zero.1 (by rw [S.zt_norm (mem_ball_self S.hρ), norm_zero])
    rw [h4]; exact sub_eq_zero.1 h3
  rw [h2, S.fderiv_zt_zero]
  rfl

theorem PhiK_quad : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : K, ‖x‖ < δ → ‖x‖ < S.rM →
    ‖fderiv ℝ S.PhiK x - 1‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C1, δ1, hC1, hδ1, h1⟩ := S.zt_quad
  obtain ⟨CS, hCS0, hCS⟩ := S.Si_quad
  refine ⟨2 * CS + C1, min δ1 (1 / Real.sqrt (C1 + 1)), by positivity,
    lt_min hδ1 (by positivity), fun x hxδ hxr => ?_⟩
  have hx1 : ‖x‖ < δ1 := lt_of_lt_of_le hxδ (min_le_left _ _)
  have hx2 : ‖x‖ < 1 / Real.sqrt (C1 + 1) := lt_of_lt_of_le hxδ (min_le_right _ _)
  have hxρ : x ∈ ball (0 : K) S.ρ := mem_ball_zero_iff.2 (lt_trans hxr S.rM_lt_rho)
  have hsq : C1 * ‖x‖ ^ 2 ≤ 1 := by
    have h0 : 0 < Real.sqrt (C1 + 1) := Real.sqrt_pos.2 (by linarith)
    have : ‖x‖ * Real.sqrt (C1 + 1) < 1 := by
      rw [lt_div_iff₀ h0] at hx2; exact hx2
    have h3 : (‖x‖ * Real.sqrt (C1 + 1)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) this.le
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h3
    nlinarith [sq_nonneg ‖x‖]
  rw [S.fderiv_PhiK hxr]
  set A := fderiv ℝ S.Si (S.zt x) with hA
  set Bm := fderiv ℝ S.zt x with hBm
  have hB1 : ‖Bm - 1‖ ≤ C1 * ‖x‖ ^ 2 := h1 x hx1
  have hBn : ‖Bm‖ ≤ 2 := by
    have : ‖Bm‖ ≤ ‖Bm - 1‖ + ‖(1 : K →L[ℝ] K)‖ := by
      have := norm_add_le (Bm - 1) 1
      simpa using this
    have h11 : ‖(1 : K →L[ℝ] K)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith
  have hAn : ‖A - 1‖ ≤ CS * ‖x‖ ^ 2 := by
    have := hCS (S.zt x) (by rw [S.zt_norm hxρ]; exact hxr)
    rwa [S.zt_norm hxρ] at this
  have e : A.comp Bm - 1 = (A - 1).comp Bm + (Bm - 1) := by
    ext v; simp
  rw [e]
  calc ‖(A - 1).comp Bm + (Bm - 1)‖ ≤ ‖(A - 1).comp Bm‖ + ‖Bm - 1‖ := norm_add_le _ _
    _ ≤ ‖A - 1‖ * ‖Bm‖ + ‖Bm - 1‖ := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (CS * ‖x‖ ^ 2) * 2 + C1 * ‖x‖ ^ 2 := by gcongr
    _ = (2 * CS + C1) * ‖x‖ ^ 2 := by ring

end Setting

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.Setting.fderiv_zt_zero
#print axioms QuantumNLS.Local021.Setting.zt_quad
#print axioms QuantumNLS.Local021.Setting.fderiv_PhiK_zero
#print axioms QuantumNLS.Local021.Setting.PhiK_quad
