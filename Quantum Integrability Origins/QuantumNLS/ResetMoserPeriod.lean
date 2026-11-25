import QuantumNLS.ResetMoserPeriodBase

/-!
# `thm:reset-moser` (LOCAL-017), stage 3b (item 2(b)): `DA_j = −2π dq_j` and `A_j + 2π q_j = 0`

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "Define `A_j(z) = ∫_0^{2π} α_{φ_j^s z}(X_{q_j}(φ_j^s z)) ds`. For a
tangent direction `h`, variation of the integral of a one-form along this loop gives
`DA_j(z)h = ∫_0^{2π} Ω_{φ_j^s z}(Dφ_j^s(z)h, X_{q_j}(φ_j^s z)) ds = −2π dq_j(z)h`. The endpoint term vanishes since `φ_j^{2π}` is the identity,
including its differential. The second equality uses `ι_{X_{q_j}}Ω = dq_j` and conservation of `q_j`. It follows [...] that `A_j + 2π q_j`
is constant. Scaling to zero [...] shows that this constant is zero."

* `Aper S j z = ∫_0^{2π} α_{φ_j^s z}(X_j(φ_j^s z)) ds` with `α = alphaR` (`alphaR_apply` in `ResetMoserPeriodBase` is the source radial formula);
* `Hyp.hasFDerivAt_Aper`: differentiation under the integral (dominated convergence, uniform Gronwall bound `norm_fderiv_phi_le`, the bound
  `‖DX_j‖ ≤ 2Mρ²+2`, `‖α‖`, `‖Dα‖`), derivative `∫ Fd` with `Fd z s h = α_γ(DX_j(γ) η) + Dα_γ(η)(X_j γ)`, `γ = φ_j^s z`, `η = Dφ_j^s(z)h`;
* `Hyp.integral_Fd_apply`: `∫_0^{2π} Fd z s h ds = −2π dq_j(z)h`: `Fd − (d/ds)[α_γ(η)] = Ω_γ(η, X_j(γ)) = −dq_j(γ)η = −dq_j(z)h`
  (from `alphaD_antisym` = `dα = Ω`, `Xn_spec`, conservation of `q_j`, and the variational equation `Hyp.variational_flow`); the endpoint term
  `α_z(η(2π)) − α_z(η(0)) = 0` since `φ_j^{2π} = id` on the open ball so `Dφ_j^{2π}(z) = id`;
* `Hyp.Aper_eq`: `A_j(z) = −2π q_j(z)` for every `z ∈ B_ρ` (the constant is fixed at `z = 0`, where `φ_j^s 0 = 0` and `X_j(0) = 0`; the ball is
  convex so no finite-dimensional connectedness is needed).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow

/-- The integrand of the derivative of `A_j`. -/
def Fd (S : Hyp) (j : ℤ) (z : K) (s : ℝ) : K →L[ℝ] ℝ :=
  (alphaR S (S.φ j s z)).comp ((fderiv ℝ (Xn S.Ω j) (S.φ j s z)).comp (fderiv ℝ (S.φ j s) z)) +
    (ContinuousLinearMap.apply ℝ ℝ (Xn S.Ω j (S.φ j s z))).comp
      ((alphaD S (S.φ j s z)).comp (fderiv ℝ (S.φ j s) z))

/-- `A_j(z) = ∫_0^{2π} α_{φ_j^s z}(X_j(φ_j^s z)) ds`. -/
def Aper (S : Hyp) (j : ℤ) (z : K) : ℝ :=
  ∫ s in (0 : ℝ)..(2 * Real.pi), alphaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z))

theorem Hyp.phi_mem_ball (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) (s : ℝ) :
    S.φ j s z ∈ ball (0 : K) ρ := by
  rw [mem_ball_zero_iff, S.norm_flow (ball_mono_R hL hz) j s]
  exact mem_ball_zero_iff.1 hz

theorem Hyp.cont_gamma {α : Type*} [TopologicalSpace α] (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K}
    (hz : z ∈ ball (0 : K) ρ) {g : K → α} (hg : ∀ w ∈ ball (0 : K) ρ, ContinuousAt g w) :
    Continuous (fun s => g (S.φ j s z)) :=
  continuous_iff_continuousAt.2 fun s =>
    ContinuousAt.comp (g := g) (f := fun s => S.φ j s z) (x := s) (hg _ (S.phi_mem_ball hL j hz s))
      (S.gamma_continuous (ball_mono_R hL hz) j).continuousAt

theorem Hyp.integrand_continuous (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) :
    Continuous (fun s => alphaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z))) := by
  have h1 := S.cont_gamma hL j hz (g := alphaR S) (fun w hw => alphaR_continuousAt S hL hw)
  have h2 := S.cont_gamma hL j hz (g := Xn S.Ω j)
    (fun w hw => (S.Xn_contDiffAt (ball_mono_R hL hw) j).continuousAt)
  exact h1.clm_apply h2

theorem Hyp.hasFDerivAt_integrand (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K}
    (hz : z ∈ ball (0 : K) ρ) (s : ℝ) :
    HasFDerivAt (fun y => alphaR S (S.φ j s y) (Xn S.Ω j (S.φ j s y))) (Fd S j z s) z := by
  have hγ : HasFDerivAt (S.φ j s) (fderiv ℝ (S.φ j s) z) z := (S.diffAt_flow hL.ρR j hz s).hasFDerivAt
  have hw := S.phi_mem_ball hL j hz s
  have hα := (alphaR_hasFDerivAt S hL hw).comp z hγ
  have hX := ((S.hasFDerivAt_Xn hL hw j).1).comp z hγ
  refine (hα.clm_apply hX).congr_fderiv ?_
  ext h
  rfl

theorem Hyp.Fd_continuous (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) :
    Continuous (fun s => Fd S j z s) := by
  have hc := S.cont_gamma hL j hz (g := alphaR S) (fun w hw => alphaR_continuousAt S hL hw)
  have hDX := S.cont_gamma hL j hz (g := fderiv ℝ (Xn S.Ω j)) (fun w hw =>
    ((S.Xn_contDiffAt (ball_mono_R hL hw) j).fderiv_right (m := 0) (by norm_num)).continuousAt)
  have hA := S.cont_gamma hL j hz (g := alphaD S) (fun w hw => alphaD_continuousAt S hL hw)
  have hv := S.cont_gamma hL j hz (g := Xn S.Ω j)
    (fun w hw => (S.Xn_contDiffAt (ball_mono_R hL hw) j).continuousAt)
  have hP : Continuous (fun s => fderiv ℝ (S.φ j s) z) :=
    continuous_iff_continuousAt.2 fun s => (S.variational_flow hL.ρR j hz s).continuousAt
  unfold Fd
  exact (hc.clm_comp (hDX.clm_comp hP)).add
    (((ContinuousLinearMap.apply ℝ ℝ).continuous.comp hv).clm_comp (hA.clm_comp hP))

theorem norm_apply_aux (v : K) : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun f => by
    simpa [mul_comm] using f.le_opNorm v

/-- The explicit uniform bound for `Fd`. -/
def Bd (M ρ : ℝ) : ℝ :=
  (M * ρ ^ 3 + ‖(omegaF : Form)‖ * ρ) * ((2 * M * ρ ^ 2 + 2) * Real.exp ((2 * M * ρ ^ 2 + 2) * (2 * Real.pi))) +
    (2 * M * ρ ^ 2 + ‖(omegaF : Form)‖) * Real.exp ((2 * M * ρ ^ 2 + 2) * (2 * Real.pi)) * (2 * ρ)

theorem Hyp.norm_Fd_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (2 * Real.pi)) : ‖Fd S j z s‖ ≤ Bd M ρ := by
  have hw := S.phi_mem_ball hL j hz s
  have hP := S.norm_fderiv_phi_le hL j hz hs
  have hDX := (S.hasFDerivAt_Xn hL hw j).2
  have hα := norm_alphaR_le S hL hw
  have hA := norm_alphaD_le S hL hw
  have hρ := hL.ρpos
  have hM := hL.M0
  have hwn : ‖S.φ j s z‖ < ρ := mem_ball_zero_iff.1 hw
  have hXn : ‖Xn S.Ω j (S.φ j s z)‖ ≤ 2 * ρ := by
    refine (norm_Xn_le S (ball_mono_R hL hw) j).trans ?_
    have := norm_apply_le_norm' (S.φ j s z) j
    linarith
  have hω0 := norm_nonneg (omegaF : Form)
  unfold Fd Bd
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul hα ?_ (norm_nonneg _) (by positivity)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul hDX hP (norm_nonneg _) (by positivity)
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖ContinuousLinearMap.apply ℝ ℝ (Xn S.Ω j (S.φ j s z))‖ ≤ 2 * ρ :=
      (norm_apply_aux _).trans hXn
    have h2 : ‖(alphaD S (S.φ j s z)).comp (fderiv ℝ (S.φ j s) z)‖ ≤
        (2 * M * ρ ^ 2 + ‖(omegaF : Form)‖) * Real.exp ((2 * M * ρ ^ 2 + 2) * (2 * Real.pi)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hA hP (norm_nonneg _) (by positivity))
    calc _ ≤ (2 * ρ) * ((2 * M * ρ ^ 2 + ‖(omegaF : Form)‖) * Real.exp ((2 * M * ρ ^ 2 + 2) * (2 * Real.pi))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem Hyp.hasFDerivAt_Aper (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z₀ : K} (hz₀ : z₀ ∈ ball (0 : K) ρ) :
    HasFDerivAt (Aper S j) (∫ s in (0 : ℝ)..(2 * Real.pi), Fd S j z₀ s) z₀ := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  unfold Aper
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (s := ball (0 : K) ρ)
    (F := fun y s => alphaR S (S.φ j s y) (Xn S.Ω j (S.φ j s y))) (F' := fun y s => Fd S j y s)
    (bound := fun _ => Bd M ρ) (isOpen_ball.mem_nhds hz₀) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [isOpen_ball.mem_nhds hz₀] with y hy
    exact (S.integrand_continuous hL j hy).aestronglyMeasurable
  · exact (S.integrand_continuous hL j hz₀).intervalIntegrable _ _
  · exact (S.Fd_continuous hL j hz₀).aestronglyMeasurable
  · rw [uIoc_of_le hpi]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact S.norm_Fd_le hL j hy ⟨ht.1.le, ht.2⟩
  · exact intervalIntegrable_const
  · rw [uIoc_of_le hpi]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact S.hasFDerivAt_integrand hL j hy t

theorem Hyp.fderiv_phi_period (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) :
    fderiv ℝ (S.φ j (2 * Real.pi)) z = ContinuousLinearMap.id ℝ K := by
  have hzR : z ∈ ball (0 : K) S.R := ball_subset_ball hρ hz
  have : S.φ j (2 * Real.pi) =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hzR) fun w hw => S.φ_period j w hw
  rw [this.fderiv_eq, fderiv_id]

theorem Hyp.dq_phi (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) (s : ℝ) (h : K) :
    fderiv ℝ (q j) (S.φ j s z) (fderiv ℝ (S.φ j s) z h) = fderiv ℝ (q j) z h := by
  have hzR : z ∈ ball (0 : K) S.R := ball_subset_ball hρ hz
  have hγ : HasFDerivAt (S.φ j s) (fderiv ℝ (S.φ j s) z) z := (S.diffAt_flow hρ j hz s).hasFDerivAt
  have hq := (hasFDerivAt_q j (S.φ j s z)).comp z hγ
  have hev : (q j ∘ S.φ j s) =ᶠ[𝓝 z] q j :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hzR) fun w hw => S.flow_q hw j j s
  have h1 : fderiv ℝ (q j) z = ((fderiv ℝ (q j) (S.φ j s z))).comp (fderiv ℝ (S.φ j s) z) := by
    rw [← hev.fderiv_eq, hq.fderiv, (hasFDerivAt_q j (S.φ j s z)).fderiv]
  rw [h1]
  rfl

theorem Hyp.integral_Fd_apply (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ)
    (h : K) :
    (∫ s in (0 : ℝ)..(2 * Real.pi), Fd S j z s) h = -(2 * Real.pi) * fderiv ℝ (q j) z h := by
  have hρ := hL.ρR
  have hzR : z ∈ ball (0 : K) S.R := ball_subset_ball hρ hz
  have hcont := S.Fd_continuous hL j hz
  have hint : (∫ s in (0 : ℝ)..(2 * Real.pi), Fd S j z s) h = ∫ s in (0 : ℝ)..(2 * Real.pi), Fd S j z s h :=
    ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable _ _) h
  have hgd : ∀ s : ℝ, HasDerivAt (fun s => alphaR S (S.φ j s z) (fderiv ℝ (S.φ j s) z h))
      (Fd S j z s h + fderiv ℝ (q j) z h) s := by
    intro s
    have hw := S.phi_mem_ball hL j hz s
    have hγs := S.φ_deriv j z hzR s
    have hα := HasFDerivAt.comp_hasDerivAt (l := alphaR S) (f := fun r => S.φ j r z) s
      (alphaR_hasFDerivAt S hL hw) hγs
    have hvar := S.variational_flow hρ j hz s
    have hη := HasFDerivAt.comp_hasDerivAt (l := ContinuousLinearMap.apply ℝ K h)
      (f := fun r => fderiv ℝ (S.φ j r) z) s (ContinuousLinearMap.apply ℝ K h).hasFDerivAt hvar
    refine (hα.clm_apply hη).congr_deriv ?_
    have hanti := alphaD_antisym S hL hw (fderiv ℝ (S.φ j s) z h) (Xn S.Ω j (S.φ j s z))
    have hspec := Xn_spec (S.Ω_lt _ (ball_mono_R hL hw)) j (fderiv ℝ (S.φ j s) z h)
    have hdq := S.dq_phi hρ j hz s h
    have hΩ' : S.Ω (S.φ j s z) (fderiv ℝ (S.φ j s) z h) (Xn S.Ω j (S.φ j s z)) = -(fderiv ℝ (q j) z h) := by
      rw [S.Ω_alt, hspec, hdq]
    rw [hΩ'] at hanti
    have hFd : Fd S j z s h = alphaR S (S.φ j s z) ((fderiv ℝ (Xn S.Ω j) (S.φ j s z)) (fderiv ℝ (S.φ j s) z h)) +
        alphaD S (S.φ j s z) (fderiv ℝ (S.φ j s) z h) (Xn S.Ω j (S.φ j s z)) := rfl
    rw [hFd]
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply]
    linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi) (fun s _ => hgd s)
    (((hcont.clm_apply continuous_const).add continuous_const).intervalIntegrable _ _)
  have h0 : S.φ j 0 = id := funext (S.φ_zero j)
  have hend : alphaR S (S.φ j (2 * Real.pi) z) (fderiv ℝ (S.φ j (2 * Real.pi)) z h) -
      alphaR S (S.φ j 0 z) (fderiv ℝ (S.φ j 0) z h) = 0 := by
    rw [S.φ_period j z hzR, S.fderiv_phi_period hρ j hz, h0]
    simp
  rw [intervalIntegral.integral_add (hcont.clm_apply continuous_const |>.intervalIntegrable _ _)
    intervalIntegrable_const] at hftc
  rw [hint]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hftc
  linarith

theorem Hyp.phi_zero_point (S : Hyp) (j : ℤ) (s : ℝ) : S.φ j s 0 = 0 := by
  have h := S.norm_flow (z := 0) (by simpa using S.R_pos) j s
  rw [norm_zero] at h
  exact norm_eq_zero.1 h

theorem Xn_zero (S : Hyp) (j : ℤ) : Xn S.Ω j 0 = 0 := by
  have := norm_Xn_le S (w := 0) (by simpa using S.R_pos) j
  simpa using this

/-- **`A_j = −2π q_j`** on `B_ρ`. -/
theorem Hyp.Aper_eq (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ) :
    Aper S j z = -(2 * Real.pi) * q j z := by
  have hG : ∀ w ∈ ball (0 : K) ρ,
      HasFDerivAt (fun v => Aper S j v + (2 * Real.pi) * q j v) (0 : K →L[ℝ] ℝ) w := by
    intro w hw
    have h1 := S.hasFDerivAt_Aper hL j hw
    have h2 := (hasFDerivAt_q j w).const_mul (2 * Real.pi)
    refine (h1.add h2).congr_fderiv ?_
    ext h
    have hD := (hasFDerivAt_q j w).fderiv
    rw [ContinuousLinearMap.add_apply, S.integral_Fd_apply hL j hw h, ContinuousLinearMap.smul_apply,
      ← hD, ContinuousLinearMap.zero_apply, smul_eq_mul]
    ring
  have hdiff : DifferentiableOn ℝ (fun v => Aper S j v + (2 * Real.pi) * q j v) (ball (0 : K) ρ) :=
    fun w hw => (hG w hw).differentiableAt.differentiableWithinAt
  have hf0 : ∀ w ∈ ball (0 : K) ρ, fderiv ℝ (fun v => Aper S j v + (2 * Real.pi) * q j v) w = 0 :=
    fun w hw => (hG w hw).fderiv
  have hc := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : K) ρ).isPreconnected hdiff hf0 hz
    (mem_ball_self hL.ρpos)
  have hA0 : Aper S j 0 = 0 := by
    unfold Aper
    simp [S.phi_zero_point, Xn_zero]
  have hq0 : q j 0 = 0 := by simp [q]
  simp only [hA0, hq0, mul_zero, add_zero] at hc
  linarith

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Hyp.hasFDerivAt_Aper
#print axioms QuantumNLS.ResetMoser.Hyp.integral_Fd_apply
#print axioms QuantumNLS.ResetMoser.Hyp.Aper_eq
