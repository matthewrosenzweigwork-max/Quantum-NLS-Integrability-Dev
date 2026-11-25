import Mathlib
import QuantumNLS.Local007Final
import QuantumNLS.Fourier

/-! LOCAL-020: uniqueness of the exact-mass factor `rr` (identity theorem) and its covariance.

`eq_of_mul_eq`: two real-analytic functions on a ball that agree after multiplication by `‖g‖²` (`g` analytic, not
identically zero) agree.  `g_ne_zero`: the LOCAL-003 reduction coordinate `g_n = gcoef b_n` is not identically zero
on a small ball (cubic estimate).  `rr_cov_generic`: if a real-linear isometry `T` and an index map `σ` satisfy
`I_n(Tw) = I_{σ n}(w)` and `|g_n(Tw)| = |g_{σ n}(w)|` then `rr_n(Tw) = rr_{σ n}(w)`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate BoundedContinuousFunction
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)

namespace QuantumNLS.Local020Rr

theorem analyticAt_normSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ} {x : E}
    (hg : AnalyticAt ℝ g x) : AnalyticAt ℝ (fun w => ‖g w‖ ^ 2) x := by
  have h1 : AnalyticAt ℝ (fun w => (g w).re) x := (Complex.reCLM.analyticAt _).comp hg
  have h2 : AnalyticAt ℝ (fun w => (g w).im) x := (Complex.imCLM.analyticAt _).comp hg
  have := (h1.pow 2).add (h2.pow 2)
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Complex.sq_norm, Complex.normSq_apply, Pi.add_apply, Pi.pow_apply]
  ring

theorem eq_of_mul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ρ : ℝ}
    {g : E → ℂ} (hg : AnalyticOnNhd ℝ g (ball (0 : E) ρ)) (hg0 : ∃ w ∈ ball (0 : E) ρ, g w ≠ 0)
    {f1 f2 : E → ℝ} (h1 : AnalyticOnNhd ℝ f1 (ball (0 : E) ρ)) (h2 : AnalyticOnNhd ℝ f2 (ball (0 : E) ρ))
    (heq : ∀ w ∈ ball (0 : E) ρ, ‖g w‖ ^ 2 * f1 w = ‖g w‖ ^ 2 * f2 w) :
    ∀ w ∈ ball (0 : E) ρ, f1 w = f2 w := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨w0, hw0, hne⟩ := hcon
  have hφ : AnalyticOnNhd ℝ (fun w => ‖g w‖ ^ 2) (ball (0 : E) ρ) := fun w hw => analyticAt_normSq (hg w hw)
  have hd : ContinuousAt (fun w => f1 w - f2 w) w0 := (h1 w0 hw0).continuousAt.sub (h2 w0 hw0).continuousAt
  have hev : ∀ᶠ w in 𝓝 w0, f1 w - f2 w ≠ 0 :=
    hd.eventually_ne (sub_ne_zero.2 hne)
  have hev2 : ∀ᶠ w in 𝓝 w0, w ∈ ball (0 : E) ρ := isOpen_ball.mem_nhds hw0
  have hz : (fun w => ‖g w‖ ^ 2) =ᶠ[𝓝 w0] 0 := by
    filter_upwards [hev, hev2] with w hw hwb
    have := heq w hwb
    have h3 : ‖g w‖ ^ 2 * (f1 w - f2 w) = 0 := by linarith
    simpa [hw] using h3
  have hzero := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : E) ρ).isPreconnected hw0 hz
  obtain ⟨w, hw, hgw⟩ := hg0
  have := hzero hw
  simp only [Pi.zero_apply] at this
  exact hgw (norm_eq_zero.1 (by simpa using this))

theorem norm_modeLp (L : ℝ) [Fact (0 < L)] (n : ℤ) : ‖QuantumNLS.Fourier.modeLp L n‖ = 1 := by
  have := (QuantumNLS.Fourier.fourierL2 L).norm_map (QuantumNLS.Fourier.modeLp L n)
  rw [QuantumNLS.Fourier.fourierL2_modeLp, lp.norm_single (by norm_num)] at this
  simpa using this.symm

theorem coeff_smul_mode (L : ℝ) [Fact (0 < L)] (t : ℂ) (n : ℤ) :
    QuantumNLS.Fourier.coeff L (((t • QuantumNLS.Fourier.modeLp L n : L2T L)) : AddCircle L → ℂ) n = t := by
  rw [← QuantumNLS.Fourier.fourierL2_apply, map_smul, QuantumNLS.Fourier.fourierL2_modeLp]
  simp

theorem g_ne_zero {L κ r ρ C : ℝ} [Fact (0 < L)] {n : ℤ} {a : L2T L → ℝ} {b : L2T L → ℂ}
    (hP : Pkg L κ r ρ C n a b) (hC0 : 0 ≤ C) {ρ' : ℝ} (hρ' : 0 < ρ') (hρρ : ρ' ≤ ρ) (hC : C * ρ' ^ 2 < 1) :
    ∃ w ∈ ball (0 : L2T L) ρ', gcoef L κ * b w ≠ 0 := by
  set t : ℝ := ρ' / 2 with ht
  have htp : 0 < t := by positivity
  set w : L2T L := (t : ℂ) • QuantumNLS.Fourier.modeLp L n with hw
  have hwn : ‖w‖ = t := by
    rw [hw, norm_smul, norm_modeLp, mul_one, Complex.norm_real, Real.norm_of_nonneg htp.le]
  have hwb : w ∈ ball (0 : L2T L) ρ' := by
    rw [mem_ball_zero_iff, hwn]; linarith
  refine ⟨w, hwb, fun h0 => ?_⟩
  have hcub := hP.2.2.2.2.2.2.1 w (mem_ball_zero_iff.2 (by rw [hwn]; linarith))
  rw [h0, zero_sub, norm_neg, hw, coeff_smul_mode, Complex.norm_real, Real.norm_of_nonneg htp.le, hwn] at hcub
  have : t * (1 - C * t ^ 2) ≤ 0 := by nlinarith
  have hCt : C * t ^ 2 < 1 := by
    have : t ^ 2 ≤ ρ' ^ 2 := by nlinarith
    nlinarith
  have : 0 < t * (1 - C * t ^ 2) := mul_pos htp (by linarith)
  linarith

open QuantumNLS.RootIndexedMasses (masses)

/-- **Covariance of `rr` by uniqueness.** -/
theorem rr_cov_generic {L κ r ρ C : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ}
    {rr : L2T L → (ℤ →ᵇ ℝ)} (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (hC0 : 0 ≤ C)
    (hrr : AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ))
    (hmassid : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, (masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n)
    {ρ' : ℝ} (hρ' : 0 < ρ') (hρρ : ρ' ≤ ρ) (hC : C * ρ' ^ 2 < 1)
    (T : L2T L →L[ℝ] L2T L) (hT : ∀ w, ‖T w‖ = ‖w‖) (σ : ℤ → ℤ) (n : ℤ)
    (hmass : ∀ w ∈ ball (0 : L2T L) ρ', (masses hκ (T w)).1 n = (masses hκ w).1 (σ n))
    (hmod : ∀ w ∈ ball (0 : L2T L) ρ', ‖b n (T w)‖ = ‖b (σ n) w‖) :
    ∀ w ∈ ball (0 : L2T L) ρ', rr (T w) n = rr w (σ n) := by
  have hsub : ball (0 : L2T L) ρ' ⊆ ball (0 : L2T L) ρ := ball_subset_ball hρρ
  have hTb : ∀ w ∈ ball (0 : L2T L) ρ', T w ∈ ball (0 : L2T L) ρ := fun w hw => by
    rw [mem_ball_zero_iff, hT]; exact hsub hw |> fun h => by simpa using h
  have hev : ∀ (m : ℤ), AnalyticAt ℝ (fun x : L2T L => (rr x) m) (T 0) → True := fun _ _ => trivial
  have ev : ∀ (m : ℤ) (x : L2T L), x ∈ ball (0 : L2T L) ρ → AnalyticAt ℝ (fun y : L2T L => (rr y) m) x := by
    intro m x hx
    exact ((BoundedContinuousFunction.evalCLM ℝ m).analyticAt (rr x)).comp (hrr x hx)
  have h1 : AnalyticOnNhd ℝ (fun w : L2T L => (rr (T w)) n) (ball (0 : L2T L) ρ') := fun w hw =>
    (ev n (T w) (hTb w hw)).comp (T.analyticAt w)
  have h2 : AnalyticOnNhd ℝ (fun w : L2T L => (rr w) (σ n)) (ball (0 : L2T L) ρ') := fun w hw =>
    ev (σ n) w (hsub hw)
  have hg : AnalyticOnNhd ℝ (fun w : L2T L => gcoef L κ * b (σ n) w) (ball (0 : L2T L) ρ') :=
    (hP (σ n)).2.2.2.2.2.1.mono hsub
  obtain ⟨w0, hw0, hg0⟩ := g_ne_zero (hP (σ n)) hC0 hρ' hρρ hC
  refine eq_of_mul_eq hg ⟨w0, hw0, hg0⟩ h1 h2 fun w hw => ?_
  have e1 := hmassid (T w) (hTb w hw) n
  have e2 := hmassid w (hsub hw) (σ n)
  have e3 : ‖gcoef L κ * b n (T w)‖ = ‖gcoef L κ * b (σ n) w‖ := by
    rw [norm_mul, norm_mul, hmod w hw]
  rw [hmass w hw, e2, e3] at e1
  exact e1.symm

end QuantumNLS.Local020Rr

#print axioms QuantumNLS.Local020Rr.rr_cov_generic
#print axioms QuantumNLS.Local020Rr.g_ne_zero
