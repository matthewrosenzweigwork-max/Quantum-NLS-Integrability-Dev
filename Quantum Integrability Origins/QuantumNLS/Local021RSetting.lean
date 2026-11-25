import Mathlib
import QuantumNLS.Local021RChart
import QuantumNLS.Local021RPull
import QuantumNLS.IndexedPeriodTheoremR30b
import QuantumNLS.RootMassInvolutionBatchR9

/-!
# LOCAL-021 repair, stage R3: discharging the Moser hypotheses (`PrintedHyp`) for the actual exact-modulus chart

Source: `local_transform.tex:152` ("The indexed-mass Hamiltonians commute by Theorem `thm:root-mass-involution`.  Theorem `reset:period-theorem` gives time `2π` equal to the identity for every
individual flow on this ball. ... The exact actions of `ζ` conjugate these fields to the `q_n = |z_n|²` fields for `Ω`.  They commute and are periodic with this common period.  Theorem `thm:reset-moser` therefore applies.")

For a `Chart` (the printed premise: LOCAL-020 family + full analytic diffeomorphism `ζ̃ : B_R → B_R` with analytic inverse `η`) and `Ω = (ζ̃⁻¹)^*ω = η^*ω` (`pullForm η`) we construct, on a common ball `B_{Rs}`
(`Rs ≤ R`, `Rs ≤ δ = delta L κ` of LOCAL-016, `‖Dη − 1‖ ≤ min(C‖y‖², 1/10)`), the `PrintedHyp` fields of `thm:reset-moser`:

* `Ω` real analytic in the operator norm, closed, alternating (`Local021RPull`), `Ω = ω + O(‖y‖²)` (from `η` odd, `Dη(0) = 1`: `Chart.eta_quad`), `‖Ω − ω‖ < 1`;
* `X_n := Xn Ω n` with `ι_{X_n} Ω = dq_n` (`Xn_spec`);  the Hamiltonian flow `φ_n(t, y) = ζ̃(ψ_n(t, η y))` with `ψ_n(t, x) = 𝓕 (flow_n(t, 𝓕⁻¹ x))` the flow of the PHYSICAL indexed mass `I_n = mass hκ n`
  (LOCAL-016 `IndexedGlobalR27b.flow`, `field = hamField (mass hκ n) = −i∇ I_n`), solving `dφ/dt = X_n(φ)` for all time (`Chart.key`: `Ω_{ζ̃ x}(Dζ̃_x(𝓕 X^{phys}_{I_n}), w) = dq_n(w)`, using `q_n ∘ ζ̃ = I_n ∘ 𝓕⁻¹` from `norm_zeta_sq`),
  staying in `B_{Rs}` (`‖ζ̃ x‖ = ‖x‖`, `‖flow‖ = ‖·‖`), and returning at `2π` (`IndexedPeriodTheoremR30b.reset_period_theorem`);
* `Ω_z(X_m, X_n) = ω_phys(X^{phys}_{I_m}, X^{phys}_{I_n}) = {I_m, I_n}_phys = 0` (R-507DD869, `RootMassInvolutionR9.indexed_pair_bracket`).

`PrintedBounds` is supplied by the proved `PrintedBounds.exists`.  The result is `Chart.toSetting : Setting L κ r hκ`, the frozen `Local021Setting.Setting` built (not assumed) from the chart.
Conventions: both `ω = 2 Im⟨·,·⟩` (physical `L²(𝕋_L)` and sequence `ℓ²`, identified by the `ℂ`-linear isometry `𝓕`), `X_F = −i∇F`, `ι_{X_F}ω = dF`, time variable `t ∈ ℝ`, period `2π`.
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
open QuantumNLS.IndexedGlobalR27b (flow delta flow_initial flow_derivative flow_norm)
open QuantumNLS.IndexedFieldR27b (field)
open QuantumNLS.RootMassInvolutionR8 (mass)

variable {L κ r : ℝ} [Fact (0 < L)]

theorem omegaF_fourier (a b : L2T L) : omegaF (fourierL2 L a) (fourierL2 L b) = omega a b := by
  rw [omegaF_apply, omega, omega, LinearIsometryEquiv.inner_map_map]

/-- the flow of the physical indexed mass `I_n` in Fourier variables. -/
def psi (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (n : ℤ) (t : ℝ) (x : K) : K := fourierL2 L (flow hκ n t ((fourierL2 L).symm x))

/-- the physical Hamiltonian field `X_{I_n} = −i∇I_n` in Fourier variables, at `x = 𝓕 u`. -/
def Vf (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (n : ℤ) (x : K) : K := Setting.Fcl L (field hκ n ((fourierL2 L).symm x))

theorem norm_psi (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (n : ℤ) (t : ℝ) (x : K) : ‖psi L hκ n t x‖ = ‖x‖ := by
  unfold psi
  rw [LinearIsometryEquiv.norm_map, flow_norm, LinearIsometryEquiv.norm_map]

theorem psi_zero (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (n : ℤ) (x : K) : psi L hκ n 0 x = x := by
  unfold psi
  rw [flow_initial, LinearIsometryEquiv.apply_symm_apply]

theorem psi_period (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (n : ℤ) {x : K} (hx : ‖x‖ < delta L κ) : psi L hκ n (2 * Real.pi) x = x := by
  unfold psi
  have hu : ‖(fourierL2 L).symm x‖ < delta L κ := by rwa [LinearIsometryEquiv.norm_map]
  rw [(QuantumNLS.IndexedPeriodTheoremR30b.reset_period_theorem (L := L) hκ).2.2.1 n _ hu,
    LinearIsometryEquiv.apply_symm_apply]

theorem hasDerivAt_psi (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (n : ℤ) (x : K) (t : ℝ) :
    HasDerivAt (fun s => psi L hκ n s x) (Vf L hκ n (psi L hκ n t x)) t := by
  have h := (Setting.Fcl L).hasFDerivAt.comp_hasDerivAt t (flow_derivative hκ n ((fourierL2 L).symm x) t)
  have e : Vf L hκ n (psi L hκ n t x) = Setting.Fcl L (field hκ n (flow hκ n t ((fourierL2 L).symm x))) := by
    unfold Vf psi
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [e]
  exact h

namespace Chart

variable {hκ : 0 < κ} (Ch : Chart L κ r hκ)

theorem q_zt {x : K} (hx : x ∈ ball (0 : K) Ch.ρ) (n : ℤ) :
    q n (Ch.zt x) = mass hκ n ((fourierL2 L).symm x) := by
  have hu : (fourierL2 L).symm x ∈ ball (0 : L2T L) Ch.ρ := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
  unfold Chart.zt zetaT
  rw [q, zetaK_apply Ch.fam hu]
  exact norm_zeta_sq Ch.fam hu n

/-- the transported physical field is the `Ω`-Hamiltonian field of `q_n`: `Ω_{ζ̃ x}(Dζ̃_x X^{phys}_{I_n}(x), w) = dq_n(ζ̃ x) w`. -/
theorem key {x : K} (hx : x ∈ ball (0 : K) Ch.R) (n : ℤ) (w : K) :
    pullForm Ch.η (Ch.zt x) (fderiv ℝ Ch.zt x (Vf L hκ n x)) w = fderiv ℝ (q n) (Ch.zt x) w := by
  have hxρ : x ∈ ball (0 : K) Ch.ρ := ball_subset_ball Ch.hRρ hx
  have hyR : Ch.zt x ∈ ball (0 : K) Ch.R := Ch.zt_mem_ball hx
  have h1 := Ch.deta_dzt hx
  have h2 : (fderiv ℝ Ch.zt x).comp (fderiv ℝ Ch.η (Ch.zt x)) = ContinuousLinearMap.id ℝ K := by
    have := Ch.dzt_deta hyR
    rwa [show Ch.η (Ch.zt x) = x from Ch.eta_zeta x hx] at this
  set u : L2T L := (fourierL2 L).symm x with hu
  set A : K →L[ℝ] K := fderiv ℝ Ch.η (Ch.zt x) with hA
  set g : L2T L := (fourierL2 L).symm (A w) with hg
  have hFg : fourierL2 L g = A w := LinearIsometryEquiv.apply_symm_apply _ _
  have hmass : DifferentiableAt ℝ (mass hκ n) u :=
    (QuantumNLS.RootMassInvolutionR9.root_mass_involution (L := L) hκ).1 n u |>.differentiableAt
  have hL : pullForm Ch.η (Ch.zt x) (fderiv ℝ Ch.zt x (Vf L hκ n x)) w = fderiv ℝ (mass hκ n) u g := by
    rw [pullForm_apply]
    have e1 : A (fderiv ℝ Ch.zt x (Vf L hκ n x)) = Vf L hκ n x := congrArg (fun T => T (Vf L hκ n x)) h1
    rw [e1, ← hFg]
    have hV : Vf L hκ n x = fourierL2 L (field hκ n u) := rfl
    rw [hV, omegaF_fourier]
    exact omega_hamField (mass hκ n) u g
  have hR : fderiv ℝ (q n) (Ch.zt x) w = fderiv ℝ (mass hκ n) u g := by
    have hw : w = fderiv ℝ Ch.zt x (A w) := (congrArg (fun T => T w) h2).symm
    have hzt : HasFDerivAt Ch.zt (fderiv ℝ Ch.zt x) x := ((Ch.zeta_an x hx).differentiableAt).hasFDerivAt
    have hq : HasFDerivAt (q n) (fderiv ℝ (q n) (Ch.zt x)) (Ch.zt x) :=
      (hasFDerivAt_q n (Ch.zt x)).differentiableAt.hasFDerivAt
    have hcomp := hq.comp x hzt
    have hm : HasFDerivAt (fun x' : K => mass hκ n ((Setting.Fcle L).symm x'))
        ((fderiv ℝ (mass hκ n) u).comp ((Setting.Fcle L).symm : K →L[ℝ] L2T L)) x := by
      have hl : HasFDerivAt (fun x' : K => (Setting.Fcle L).symm x') ((Setting.Fcle L).symm : K →L[ℝ] L2T L) x :=
        (Setting.Fcle L).symm.hasFDerivAt
      have hu' : (Setting.Fcle L).symm x = u := rfl
      have hm' : HasFDerivAt (mass hκ n) (fderiv ℝ (mass hκ n) u) ((Setting.Fcle L).symm x) := by
        rw [hu']; exact hmass.hasFDerivAt
      exact hm'.comp x hl
    have hev : (q n ∘ Ch.zt) =ᶠ[𝓝 x] (fun x' : K => mass hκ n ((Setting.Fcle L).symm x')) := by
      filter_upwards [isOpen_ball.mem_nhds hxρ] with w' hw'
      exact Ch.q_zt hw' n
    have huniq := (hcomp.congr_of_eventuallyEq hev.symm).unique hm
    have := congrArg (fun T : K →L[ℝ] ℝ => T (A w)) huniq
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← hw] at this
    exact this
  rw [hL, hR]

/-- non-degeneracy: the Neumann-series field `Xn` of `Ω = η^*ω` is the transported physical field. -/
theorem Xn_eq {x : K} (hx : x ∈ ball (0 : K) Ch.R) (hlt : ‖pullForm Ch.η (Ch.zt x) - omegaF‖ < 1) (n : ℤ) :
    Xn (pullForm Ch.η) n (Ch.zt x) = fderiv ℝ Ch.zt x (Vf L hκ n x) := by
  have h1 := Xn_spec hlt n
  have : Xn (pullForm Ch.η) n (Ch.zt x) - fderiv ℝ Ch.zt x (Vf L hκ n x) = 0 := by
    refine PrintedHyp.eq_zero_of_pairing (D := pullForm Ch.η (Ch.zt x)) hlt fun w => ?_
    rw [map_sub, ContinuousLinearMap.sub_apply, h1, Ch.key hx n w, sub_self]
  exact sub_eq_zero.1 this

theorem poisson_V {x : K} (hx : x ∈ ball (0 : K) Ch.R) (m n : ℤ) :
    pullForm Ch.η (Ch.zt x) (fderiv ℝ Ch.zt x (Vf L hκ m x)) (fderiv ℝ Ch.zt x (Vf L hκ n x)) = 0 := by
  rw [pullForm_apply]
  have e : ∀ k : ℤ, fderiv ℝ Ch.η (Ch.zt x) (fderiv ℝ Ch.zt x (Vf L hκ k x)) = Vf L hκ k x :=
    fun k => congrArg (fun T => T (Vf L hκ k x)) (Ch.deta_dzt hx)
  rw [e m, e n]
  set u : L2T L := (fourierL2 L).symm x with hu
  have hV : ∀ k : ℤ, Vf L hκ k x = fourierL2 L (field hκ k u) := fun k => rfl
  rw [hV m, hV n, omegaF_fourier]
  have := QuantumNLS.RootMassInvolutionR9.indexed_pair_bracket (L := L) hκ u m n
  rw [← this]
  exact omega_hamField (mass hκ m) u (field hκ n u)

theorem norm_eta {y : K} (hy : y ∈ ball (0 : K) Ch.R) : ‖Ch.η y‖ = ‖y‖ := by
  have hxρ : Ch.η y ∈ ball (0 : K) Ch.ρ := ball_subset_ball Ch.hRρ (Ch.eta_mem y hy)
  have := Ch.zt_norm hxρ
  rw [show Ch.zt (Ch.η y) = y from Ch.zeta_eta y hy] at this
  exact this.symm

/-- the common radius: inside `B_R`, inside LOCAL-016's invariant ball, with `‖Dη − 1‖ ≤ C‖y‖²` and `≤ 1/10`. -/
theorem exists_radius :
    ∃ Rs Cq : ℝ, 0 < Rs ∧ Rs ≤ Ch.R ∧ Rs ≤ delta L κ ∧ 0 ≤ Cq ∧
      ∀ y : K, ‖y‖ < Rs → ‖fderiv ℝ Ch.η y - 1‖ ≤ Cq * ‖y‖ ^ 2 ∧ ‖fderiv ℝ Ch.η y - 1‖ ≤ 1 / 10 := by
  obtain ⟨C, δ, hC, hδ, h⟩ := Ch.eta_quad
  have hd : 0 < delta L κ := (QuantumNLS.IndexedPeriodTheoremR30b.reset_period_theorem (L := L) hκ).1
  have hpos : 0 < 1 / (10 * (C + 1)) := by positivity
  refine ⟨min (min Ch.R (delta L κ)) (min δ (1 / (10 * (C + 1)))), C, ?_, ?_, ?_, hC, fun y hy => ?_⟩
  · exact lt_min (lt_min Ch.hR hd) (lt_min hδ hpos)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · have h1 : ‖y‖ < δ := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : ‖y‖ < 1 / (10 * (C + 1)) := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨h y h1, (h y h1).trans ?_⟩
    have hs0 : 0 ≤ ‖y‖ := norm_nonneg y
    have hle : 1 / (10 * (C + 1)) ≤ 1 / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hs1 : ‖y‖ ≤ 1 := by linarith
    have h3 : C * ‖y‖ ^ 2 ≤ C * ‖y‖ := by
      apply mul_le_mul_of_nonneg_left _ hC; nlinarith
    have h4 : C * ‖y‖ ≤ C * (1 / (10 * (C + 1))) := mul_le_mul_of_nonneg_left h2.le hC
    have h5 : C * (1 / (10 * (C + 1))) ≤ 1 / 10 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith

theorem lt_one (Rs Cq : ℝ)
    (hq : ∀ y : K, ‖y‖ < Rs → ‖fderiv ℝ Ch.η y - 1‖ ≤ Cq * ‖y‖ ^ 2 ∧ ‖fderiv ℝ Ch.η y - 1‖ ≤ 1 / 10)
    {y : K} (hy : y ∈ ball (0 : K) Rs) : ‖pullForm Ch.η y - omegaF‖ < 1 := by
  have := pullForm_sub_le Ch.η y (e := 1 / 10) (by norm_num) (hq y (mem_ball_zero_iff.1 hy)).2
  linarith

/-- The printed hypotheses of `thm:reset-moser` for `Ω = (ζ̃⁻¹)^*ω`, constructed from the chart. -/
def printed (Rs Cq : ℝ) (hRs : 0 < Rs) (hRsR : Rs ≤ Ch.R) (hRsδ : Rs ≤ delta L κ)
    (hq : ∀ y : K, ‖y‖ < Rs → ‖fderiv ℝ Ch.η y - 1‖ ≤ Cq * ‖y‖ ^ 2 ∧ ‖fderiv ℝ Ch.η y - 1‖ ≤ 1 / 10) :
    PrintedHyp where
  R := Rs
  R_pos := hRs
  Ω := pullForm Ch.η
  Ω_alt := fun _ _ v w => pullForm_alt _ _ v w
  Ω_analytic := fun z hz =>
    (QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPoly _ z).1
      (analyticAt_pullForm (Ch.eta_an z (ball_subset_ball hRsR hz)))
  Ω_closed := fun z hz a b c => pullForm_closed (Ch.eta_an z (ball_subset_ball hRsR hz)) a b c
  Ω_quad := by
    refine Asymptotics.IsBigO.of_bound (5 * Cq) ?_
    filter_upwards [ball_mem_nhds (0 : K) hRs] with y hy
    have hy' : ‖y‖ < Rs := mem_ball_zero_iff.1 hy
    obtain ⟨h1, h2⟩ := hq y hy'
    have h3 := pullForm_sub_le Ch.η y (e := ‖fderiv ℝ Ch.η y - 1‖) (norm_nonneg _) le_rfl
    simp only [norm_pow, norm_norm]
    have h4 : 0 ≤ ‖fderiv ℝ Ch.η y - 1‖ := norm_nonneg _
    nlinarith
  Ω_lt := fun z hz => Ch.lt_one Rs Cq hq hz
  X := Xn (pullForm Ch.η)
  X_spec := fun n z hz h => Xn_spec (Ch.lt_one Rs Cq hq hz) n h
  φ := fun n t y => Ch.zt (psi L hκ n t (Ch.η y))
  φ_zero := fun n z hz => by
    show Ch.zt (psi L hκ n 0 (Ch.η z)) = z
    rw [psi_zero L]
    exact Ch.zeta_eta z (ball_subset_ball hRsR hz)
  φ_mem := fun n z hz t => by
    have hzR : z ∈ ball (0 : K) Ch.R := ball_subset_ball hRsR hz
    have hn : ‖Ch.η z‖ = ‖z‖ := Ch.norm_eta hzR
    have hxρ : psi L hκ n t (Ch.η z) ∈ ball (0 : K) Ch.ρ := by
      rw [mem_ball_zero_iff, norm_psi L, hn]
      exact lt_of_lt_of_le (mem_ball_zero_iff.1 hz) (hRsR.trans Ch.hRρ)
    rw [mem_ball_zero_iff, Ch.zt_norm hxρ, norm_psi L, hn]
    exact mem_ball_zero_iff.1 hz
  φ_deriv := fun n z hz t => by
    have hzR : z ∈ ball (0 : K) Ch.R := ball_subset_ball hRsR hz
    have hn : ‖Ch.η z‖ = ‖z‖ := Ch.norm_eta hzR
    have hxR : psi L hκ n t (Ch.η z) ∈ ball (0 : K) Ch.R := by
      rw [mem_ball_zero_iff, norm_psi L, hn]
      exact lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hRsR
    have hxρ : psi L hκ n t (Ch.η z) ∈ ball (0 : K) Ch.ρ := ball_subset_ball Ch.hRρ hxR
    have hyS : Ch.zt (psi L hκ n t (Ch.η z)) ∈ ball (0 : K) Rs := by
      rw [mem_ball_zero_iff, Ch.zt_norm hxρ, norm_psi L, hn]; exact mem_ball_zero_iff.1 hz
    have hzt : HasFDerivAt Ch.zt (fderiv ℝ Ch.zt (psi L hκ n t (Ch.η z))) (psi L hκ n t (Ch.η z)) :=
      ((Ch.zeta_an _ hxR).differentiableAt).hasFDerivAt
    have h1 := hzt.comp_hasDerivAt t (hasDerivAt_psi L hκ n (Ch.η z) t)
    have h2 := Ch.Xn_eq hxR (Ch.lt_one Rs Cq hq hyS) n
    show HasDerivAt (fun s => Ch.zt (psi L hκ n s (Ch.η z))) (Xn (pullForm Ch.η) n (Ch.zt (psi L hκ n t (Ch.η z)))) t
    rw [h2]
    exact h1
  φ_period := fun n z hz => by
    have hzR : z ∈ ball (0 : K) Ch.R := ball_subset_ball hRsR hz
    have hn : ‖Ch.η z‖ = ‖z‖ := Ch.norm_eta hzR
    show Ch.zt (psi L hκ n (2 * Real.pi) (Ch.η z)) = z
    rw [psi_period L hκ n (by rw [hn]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hRsδ)]
    exact Ch.zeta_eta z hzR
  poisson := fun m n z hz => by
    have hzR : z ∈ ball (0 : K) Ch.R := ball_subset_ball hRsR hz
    have hz' : Ch.zt (Ch.η z) = z := Ch.zeta_eta z hzR
    have hxR : Ch.η z ∈ ball (0 : K) Ch.R := Ch.eta_mem z hzR
    have hlt : ‖pullForm Ch.η (Ch.zt (Ch.η z)) - omegaF‖ < 1 := by rw [hz']; exact Ch.lt_one Rs Cq hq hz
    have e1 := Ch.Xn_eq hxR hlt m
    have e2 := Ch.Xn_eq hxR hlt n
    rw [hz'] at e1 e2 hlt
    show pullForm Ch.η z (Xn (pullForm Ch.η) m z) (Xn (pullForm Ch.η) n z) = 0
    rw [e1, e2]
    have := Ch.poisson_V hxR m n
    rwa [hz'] at this

/-- **The setting of LOCAL-021, constructed (not assumed)** from the printed premise (the chart). -/
def toSetting (Rs Cq : ℝ) (hRs : 0 < Rs) (hRsR : Rs ≤ Ch.R) (hRsδ : Rs ≤ delta L κ)
    (hq : ∀ y : K, ‖y‖ < Rs → ‖fderiv ℝ Ch.η y - 1‖ ≤ Cq * ‖y‖ ^ 2 ∧ ‖fderiv ℝ Ch.η y - 1‖ ≤ 1 / 10) :
    Setting L κ r hκ where
  ρ := Ch.ρ
  C := Ch.C
  a := Ch.a
  b := Ch.b
  rr := Ch.rr
  hρ := Ch.hρ
  hC := Ch.hC
  fam := Ch.fam
  R := Rs
  hR := hRs
  hRρ := hRsR.trans Ch.hRρ
  η := Ch.η
  zeta_an := Ch.zeta_an.mono (ball_subset_ball hRsR)
  eta_an := Ch.eta_an.mono (ball_subset_ball hRsR)
  eta_mem := fun y hy => by
    rw [mem_ball_zero_iff, Ch.norm_eta (ball_subset_ball hRsR hy)]; exact mem_ball_zero_iff.1 hy
  zeta_eta := fun y hy => Ch.zeta_eta y (ball_subset_ball hRsR hy)
  eta_zeta := fun x hx => Ch.eta_zeta x (ball_subset_ball hRsR hx)
  P := Ch.printed Rs Cq hRs hRsR hRsδ hq
  hPR := rfl
  hΩ := fun y _ v w => rfl
  B := Classical.choice (PrintedBounds.exists (Ch.printed Rs Cq hRs hRsR hRsδ hq))

end Chart

end QuantumNLS.Local021R

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021R.Chart.key
#print axioms QuantumNLS.Local021R.Chart.Xn_eq
#print axioms QuantumNLS.Local021R.Chart.poisson_V
#print axioms QuantumNLS.Local021R.Chart.exists_radius
#print axioms QuantumNLS.Local021R.Chart.printed
#print axioms QuantumNLS.Local021R.Chart.toSetting
