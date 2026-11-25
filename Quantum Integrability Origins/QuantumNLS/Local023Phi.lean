import Mathlib
import QuantumNLS.Local023Premise

/-!
# LOCAL-023, stage Φ: the canonical map `Φ = S⁻¹ ∘ ζ` of one LOCAL-021 `Setting` is a real-analytic canonical diffeomorphism of `B_{r_M}`

Source: `local_transform.tex:10` (`thm:reset-open-transform`) and its proof, paragraph "Exact periods and the symplectic correction"
(`local_transform.tex:165-185`): `S` is an analytic diffeomorphism of the ball preserving every `q_n` with `S^*Ω = ω`; `Φ = S⁻¹∘ζ`; "its genuine inverse is
`ζ⁻¹∘S`"; `Φ^*ω = ζ^*(S⁻¹)^*ω = ζ^*Ω = ω`; "the differential bounds follow by composing the full quadratic estimates and their inverses".

For a `Setting S` (the literal LOCAL-017 outputs `Sm = S`, `Si = S⁻¹` on the constructed `Ω = (ζ̃⁻¹)^*ω`, and `Φ = Si ∘ ζ`) this module proves, on `{‖u‖ < r_M}`:
* `Psi S : ℓ² → L²`, `Psi y = 𝓕⁻¹ (η (Sm y))` is the genuine inverse `ζ⁻¹ ∘ S` (`Psi_Phi`, `Phi_Psi`), both analytic and norm preserving;
* `|Φ(u)_n|² = I_n(u)` (`norm_Phi_apply`), `‖Φ(u)‖ = ‖u‖`;
* `Φ^*ω = ω` on all Hilbert tangent vectors (`omega_DPhi`);
* `DΦ(u)` is a bounded invertible real-linear map with inverse `D(Φ⁻¹)(Φ(u))` (`exists_equiv`), and `inv_diff_bound` turns the quadratic bound on `DΦ - 𝓕` into the one on the inverse differential.
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

namespace QuantumNLS.Local023

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021 QuantumNLS.Local021R
open QuantumNLS.RootIndexedMasses (masses)

variable {L : ℝ} [Fact (0 < L)] {κ r : ℝ} {hκ : 0 < κ} (S : Setting L κ r hκ)

/-- The literal LOCAL-017 conclusions for the constructed `Ω = (ζ̃⁻¹)^*ω`: `S`, `S⁻¹` are mutually inverse analytic self-maps of `B_{r_M}`, `S^*Ω = ω`, each `q_n` is preserved. -/
def Corr : Prop :=
  (∀ z ∈ ball (0 : K) S.rM, S.Sm z ∈ ball (0 : K) S.rM ∧ S.Si z ∈ ball (0 : K) S.rM) ∧
  (∀ z ∈ ball (0 : K) S.rM, S.Si (S.Sm z) = z ∧ S.Sm (S.Si z) = z) ∧
  AnalyticOnNhd ℝ S.Sm (ball (0 : K) S.rM) ∧ AnalyticOnNhd ℝ S.Si (ball (0 : K) S.rM) ∧
  (∀ z ∈ ball (0 : K) S.rM, ∀ a b : K, S.P.Ω (S.Sm z) (fderiv ℝ S.Sm z a) (fderiv ℝ S.Sm z b) = omegaF a b) ∧
  (∀ (n : ℤ), ∀ z ∈ ball (0 : K) S.rM, q n (S.Sm z) = q n z)

theorem corr (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) : Corr S := by
  obtain ⟨⟨C0, ⟨hC0, hmem, hinv, hSa, hSia, hpull, hq, h3, h2⟩, hflow⟩, -⟩ := settingProps hr hr2 S
  exact ⟨hmem, hinv, hSa, hSia, hpull, hq⟩

/-- `Φ⁻¹ = ζ⁻¹ ∘ S` in physical variables: `Psi y = 𝓕⁻¹ (η (S y))`. -/
def Psi (y : K) : L2T L := Fi L (S.η (S.Sm y))

theorem rM_sub_R {z : K} (hz : ‖z‖ < S.rM) : z ∈ ball (0 : K) S.R := mem_ball_zero_iff.2 (lt_trans hz S.rM_lt_R)

theorem rM_sub_rho {z : K} (hz : ‖z‖ < S.rM) : z ∈ ball (0 : K) S.ρ := mem_ball_zero_iff.2 (lt_trans hz S.rM_lt_rho)

theorem zt_mem_ball' {x : K} (hx : x ∈ ball (0 : K) S.R) : S.zt x ∈ ball (0 : K) S.R := by
  have hxρ : x ∈ ball (0 : K) S.ρ := ball_subset_ball S.hRρ hx
  rw [mem_ball_zero_iff, S.zt_norm hxρ]; exact mem_ball_zero_iff.1 hx

theorem eta_norm {y : K} (hy : y ∈ ball (0 : K) S.R) : ‖S.η y‖ = ‖y‖ := by
  have hx := S.eta_mem y hy
  have hxρ : S.η y ∈ ball (0 : K) S.ρ := ball_subset_ball S.hRρ hx
  have h1 := S.zt_norm hxρ
  have h2 : S.zt (S.η y) = y := S.zeta_eta y hy
  rw [h2] at h1
  exact h1.symm

theorem deta_dzt {x : K} (hx : x ∈ ball (0 : K) S.R) :
    (fderiv ℝ S.η (S.zt x)).comp (fderiv ℝ S.zt x) = ContinuousLinearMap.id ℝ K := by
  have hz : DifferentiableAt ℝ S.zt x := (S.zeta_an x hx).differentiableAt
  have he : DifferentiableAt ℝ S.η (S.zt x) := (S.eta_an _ (zt_mem_ball' S hx)).differentiableAt
  have h1 : HasFDerivAt (S.η ∘ S.zt) ((fderiv ℝ S.η (S.zt x)).comp (fderiv ℝ S.zt x)) x :=
    he.hasFDerivAt.comp x hz.hasFDerivAt
  have hev : (S.η ∘ S.zt) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    exact S.eta_zeta w hw
  have h2 : HasFDerivAt (S.η ∘ S.zt) (ContinuousLinearMap.id ℝ K) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hev
  exact h1.unique h2

theorem norm_Si (w : K) : ‖S.Si w‖ = ‖w‖ := S.MD.norm_Tinv w

theorem norm_Sm (y : K) : ‖S.Sm y‖ = ‖y‖ := S.MD.norm_Sfl 1 y

theorem norm_Si_apply (hc : Corr S) {w : K} (hw : ‖w‖ < S.rM) (n : ℤ) : ‖S.Si w n‖ ^ 2 = ‖w n‖ ^ 2 := by
  have hwb : w ∈ ball (0 : K) S.rM := mem_ball_zero_iff.2 hw
  have hz := (hc.1 w hwb).2
  have h1 := hc.2.2.2.2.2 n (S.Si w) hz
  rw [(hc.2.1 w hwb).2] at h1
  unfold q at h1
  exact h1.symm

theorem norm_Phi {u : L2T L} (hu : ‖u‖ < S.rM) : ‖S.Phi u‖ = ‖u‖ := by
  have hρ : u ∈ ball (0 : L2T L) S.ρ := mem_ball_zero_iff.2 (lt_trans hu S.rM_lt_rho)
  show ‖S.Si (zetaK L κ S.b S.rr u)‖ = ‖u‖
  rw [norm_Si S, norm_zetaK S.fam hρ]

theorem norm_Phi_apply (hc : Corr S) {u : L2T L} (hu : ‖u‖ < S.rM) (n : ℤ) :
    ‖S.Phi u n‖ ^ 2 = (masses hκ u).1 n := by
  have hρ : u ∈ ball (0 : L2T L) S.ρ := mem_ball_zero_iff.2 (lt_trans hu S.rM_lt_rho)
  have hz : ‖zetaK L κ S.b S.rr u‖ < S.rM := by rw [norm_zetaK S.fam hρ]; exact hu
  show ‖S.Si (zetaK L κ S.b S.rr u) n‖ ^ 2 = _
  rw [norm_Si_apply S hc hz n, zetaK_apply S.fam hρ n]
  exact norm_zeta_sq S.fam hρ n

theorem analyticAt_PhiK (hc : Corr S) {x : K} (hx : ‖x‖ < S.rM) : AnalyticAt ℝ S.PhiK x := by
  have hxR := rM_sub_R S hx
  have hxρ := rM_sub_rho S hx
  have hzt : ‖S.zt x‖ < S.rM := by rw [S.zt_norm hxρ]; exact hx
  exact (hc.2.2.2.1 (S.zt x) (mem_ball_zero_iff.2 hzt)).comp (S.zeta_an x hxR)

theorem analyticAt_Phi (hc : Corr S) {u : L2T L} (hu : ‖u‖ < S.rM) : AnalyticAt ℝ S.Phi u := by
  have e : S.Phi = S.PhiK ∘ ⇑(Setting.Fcl L) := funext fun u => S.Phi_eq u
  rw [e]
  have hx : ‖Setting.Fcl L u‖ < S.rM := by
    rw [Setting.Fcl_apply, LinearIsometryEquiv.norm_map]; exact hu
  exact (analyticAt_PhiK S hc hx).comp ((Setting.Fcl L).analyticAt u)

theorem analyticAt_Psi (hc : Corr S) {y : K} (hy : ‖y‖ < S.rM) : AnalyticAt ℝ (Psi S) y := by
  have hSm : S.Sm y ∈ ball (0 : K) S.rM := (hc.1 y (mem_ball_zero_iff.2 hy)).1
  have h1 : AnalyticAt ℝ S.η (S.Sm y) := S.eta_an _ (rM_sub_R S (mem_ball_zero_iff.1 hSm))
  have h2 : AnalyticAt ℝ S.Sm y := hc.2.2.1 y (mem_ball_zero_iff.2 hy)
  exact ((Fi L).analyticAt _).comp (h1.comp h2)

theorem norm_Psi (hc : Corr S) {y : K} (hy : ‖y‖ < S.rM) : ‖(Psi S) y‖ = ‖y‖ := by
  have hSm : S.Sm y ∈ ball (0 : K) S.rM := (hc.1 y (mem_ball_zero_iff.2 hy)).1
  have hR := rM_sub_R S (mem_ball_zero_iff.1 hSm)
  show ‖Fi L (S.η (S.Sm y))‖ = ‖y‖
  rw [norm_Fi, eta_norm S hR, norm_Sm S y]

theorem Phi_Psi (hc : Corr S) {y : K} (hy : ‖y‖ < S.rM) : S.Phi ((Psi S) y) = y := by
  have hyb : y ∈ ball (0 : K) S.rM := mem_ball_zero_iff.2 hy
  have hSm : S.Sm y ∈ ball (0 : K) S.rM := (hc.1 y hyb).1
  have hR := rM_sub_R S (mem_ball_zero_iff.1 hSm)
  rw [S.Phi_eq]
  show S.Si (S.zt (fourierL2 L (Fi L (S.η (S.Sm y))))) = y
  rw [show fourierL2 L (Fi L (S.η (S.Sm y))) = S.η (S.Sm y) from (fourierL2 L).apply_symm_apply _]
  rw [show S.zt (S.η (S.Sm y)) = S.Sm y from S.zeta_eta _ hR]
  exact (hc.2.1 y hyb).1

theorem Psi_Phi (hc : Corr S) {u : L2T L} (hu : ‖u‖ < S.rM) : (Psi S) (S.Phi u) = u := by
  have hFu : ‖fourierL2 L u‖ < S.rM := by rwa [LinearIsometryEquiv.norm_map]
  have hFuR := rM_sub_R S hFu
  have hFuρ := rM_sub_rho S hFu
  have hw : ‖S.zt (fourierL2 L u)‖ < S.rM := by rw [S.zt_norm hFuρ]; exact hFu
  rw [S.Phi_eq]
  show Fi L (S.η (S.Sm (S.Si (S.zt (fourierL2 L u))))) = u
  rw [(hc.2.1 _ (mem_ball_zero_iff.2 hw)).2]
  rw [show S.η (S.zt (fourierL2 L u)) = fourierL2 L u from S.eta_zeta _ hFuR]
  exact (fourierL2 L).symm_apply_apply u

theorem exists_equiv (hc : Corr S) {u : L2T L} (hu : ‖u‖ < S.rM) :
    ∃ e : L2T L ≃L[ℝ] K, (e : L2T L →L[ℝ] K) = fderiv ℝ S.Phi u ∧
      (e.symm : K →L[ℝ] L2T L) = fderiv ℝ (Psi S) (S.Phi u) := by
  have hPu : ‖S.Phi u‖ < S.rM := by rw [norm_Phi S hu]; exact hu
  have hdP : HasFDerivAt S.Phi (fderiv ℝ S.Phi u) u := hasFDerivAt_Phi S hu
  have hdQ : HasFDerivAt (Psi S) (fderiv ℝ (Psi S) (S.Phi u)) (S.Phi u) :=
    ((analyticAt_Psi S hc hPu).differentiableAt).hasFDerivAt
  have hl : (fderiv ℝ (Psi S) (S.Phi u)).comp (fderiv ℝ S.Phi u) = ContinuousLinearMap.id ℝ (L2T L) := by
    have h1 : HasFDerivAt ((Psi S) ∘ S.Phi) ((fderiv ℝ (Psi S) (S.Phi u)).comp (fderiv ℝ S.Phi u)) u :=
      hdQ.comp u hdP
    have hev : ((Psi S) ∘ S.Phi) =ᶠ[𝓝 u] id := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hu : u ∈ ball (0 : L2T L) S.rM)] with w hw
      exact Psi_Phi S hc (mem_ball_zero_iff.1 hw)
    have h2 : HasFDerivAt ((Psi S) ∘ S.Phi) (ContinuousLinearMap.id ℝ (L2T L)) u :=
      (hasFDerivAt_id u).congr_of_eventuallyEq hev
    exact h1.unique h2
  have hr : (fderiv ℝ S.Phi u).comp (fderiv ℝ (Psi S) (S.Phi u)) = ContinuousLinearMap.id ℝ K := by
    have hdP' : HasFDerivAt S.Phi (fderiv ℝ S.Phi u) ((Psi S) (S.Phi u)) := by
      rw [Psi_Phi S hc hu]; exact hdP
    have h1 : HasFDerivAt (S.Phi ∘ (Psi S)) ((fderiv ℝ S.Phi u).comp (fderiv ℝ (Psi S) (S.Phi u))) (S.Phi u) :=
      hdP'.comp (S.Phi u) hdQ
    have hev : (S.Phi ∘ (Psi S)) =ᶠ[𝓝 (S.Phi u)] id := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hPu : S.Phi u ∈ ball (0 : K) S.rM)] with w hw
      exact Phi_Psi S hc (mem_ball_zero_iff.1 hw)
    have h2 : HasFDerivAt (S.Phi ∘ (Psi S)) (ContinuousLinearMap.id ℝ K) (S.Phi u) :=
      (hasFDerivAt_id _).congr_of_eventuallyEq hev
    exact h1.unique h2
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ S.Phi u) (fderiv ℝ (Psi S) (S.Phi u))
    (fun h => congrArg (fun T => T h) hl) (fun k => congrArg (fun T => T k) hr),
    ContinuousLinearMap.ext fun h => rfl, ContinuousLinearMap.ext fun k => rfl⟩

theorem Si_symp (hc : Corr S) {w : K} (hw : ‖w‖ < S.rM) (a b : K) :
    omegaF (fderiv ℝ S.Si w a) (fderiv ℝ S.Si w b) = omegaF (fderiv ℝ S.η w a) (fderiv ℝ S.η w b) := by
  have hwb : w ∈ ball (0 : K) S.rM := mem_ball_zero_iff.2 hw
  have hz : S.Si w ∈ ball (0 : K) S.rM := (hc.1 w hwb).2
  have hcomp : ∀ a : K, fderiv ℝ S.Sm (S.Si w) (fderiv ℝ S.Si w a) = a := by
    intro a
    have hSi : DifferentiableAt ℝ S.Si w := (hc.2.2.2.1 w hwb).differentiableAt
    have hSm : DifferentiableAt ℝ S.Sm (S.Si w) := (hc.2.2.1 _ hz).differentiableAt
    have h1 : HasFDerivAt (S.Sm ∘ S.Si) ((fderiv ℝ S.Sm (S.Si w)).comp (fderiv ℝ S.Si w)) w :=
      hSm.hasFDerivAt.comp w hSi.hasFDerivAt
    have hev : (S.Sm ∘ S.Si) =ᶠ[𝓝 w] id := by
      filter_upwards [isOpen_ball.mem_nhds hwb] with v hv
      exact (hc.2.1 v hv).2
    have h2 : HasFDerivAt (S.Sm ∘ S.Si) (ContinuousLinearMap.id ℝ K) w :=
      (hasFDerivAt_id w).congr_of_eventuallyEq hev
    have := h1.unique h2
    exact congrArg (fun T => T a) this
  have hp := hc.2.2.2.2.1 (S.Si w) hz (fderiv ℝ S.Si w a) (fderiv ℝ S.Si w b)
  rw [(hc.2.1 w hwb).2, hcomp a, hcomp b] at hp
  rw [← hp, S.hΩ w (rM_sub_R S hw) a b]

theorem PhiK_symp (hc : Corr S) {x : K} (hx : ‖x‖ < S.rM) (h k : K) :
    omegaF (fderiv ℝ S.PhiK x h) (fderiv ℝ S.PhiK x k) = omegaF h k := by
  have hxR := rM_sub_R S hx
  have hxρ := rM_sub_rho S hx
  have hw : ‖S.zt x‖ < S.rM := by rw [S.zt_norm hxρ]; exact hx
  have e : ∀ v : K, fderiv ℝ S.η (S.zt x) (fderiv ℝ S.zt x v) = v := fun v =>
    congrArg (fun T => T v) (deta_dzt S hxR)
  rw [S.fderiv_PhiK hx]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Si_symp S hc hw, e h, e k]

theorem omega_DPhi (hc : Corr S) {u : L2T L} (hu : ‖u‖ < S.rM) (h k : L2T L) :
    omega (fderiv ℝ S.Phi u h) (fderiv ℝ S.Phi u k) = omega h k := by
  have hFu : ‖fourierL2 L u‖ < S.rM := by rwa [LinearIsometryEquiv.norm_map]
  have h1 := PhiK_symp S hc hFu (Setting.Fcl L h) (Setting.Fcl L k)
  rw [omegaF_apply, omegaF_apply] at h1
  rw [S.fderiv_Phi u]
  refine h1.trans ?_
  exact (omegaF_apply _ _).symm.trans (omegaF_fourier h k)

/-- the inverse differential is controlled by the differential (`‖A − 𝓕‖ ≤ ε ≤ 1/2 ⇒ ‖A⁻¹ − 𝓕⁻¹‖ ≤ 2ε`). -/
theorem inv_diff_bound {A : L2T L →L[ℝ] K} {A' : K →L[ℝ] L2T L}
    (hA' : A'.comp A = ContinuousLinearMap.id ℝ (L2T L)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ‖A - Setting.Fcl L‖ ≤ ε) (hε2 : ε ≤ 1 / 2) : ‖A' - Fi L‖ ≤ 2 * ε := by
  have hFF : ∀ y : K, Setting.Fcl L (Fi L y) = y := fun y => (fourierL2 L).apply_symm_apply y
  have key : A' - Fi L = (A'.comp (Setting.Fcl L - A)).comp (Fi L) := by
    refine ContinuousLinearMap.ext fun y => ?_
    have h2 : A' (A (Fi L y)) = Fi L y := congrArg (fun T => T (Fi L y)) hA'
    simp [hFF, h2]
  have h1 : ‖A' - Fi L‖ ≤ ‖A'‖ * ε := by
    rw [key]
    calc ‖(A'.comp (Setting.Fcl L - A)).comp (Fi L)‖
        ≤ ‖A'.comp (Setting.Fcl L - A)‖ * ‖Fi L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖A'‖ * ‖Setting.Fcl L - A‖) * 1 :=
          mul_le_mul (ContinuousLinearMap.opNorm_comp_le _ _) norm_Fi_le (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ ‖A'‖ * ε := by
          rw [mul_one, norm_sub_rev]; exact mul_le_mul_of_nonneg_left hε (norm_nonneg _)
  have h2 : ‖A'‖ ≤ 1 + ‖A'‖ * ε := by
    calc ‖A'‖ = ‖Fi L + (A' - Fi L)‖ := by rw [show Fi L + (A' - Fi L) = A' by abel]
      _ ≤ ‖Fi L‖ + ‖A' - Fi L‖ := norm_add_le _ _
      _ ≤ 1 + ‖A'‖ * ε := add_le_add norm_Fi_le h1
  have h3 : ‖A'‖ ≤ 2 := by
    nlinarith [norm_nonneg A', mul_le_mul_of_nonneg_left hε2 (norm_nonneg A')]
  nlinarith [mul_le_mul_of_nonneg_right h3 hε0]

end QuantumNLS.Local023

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local023.corr
#print axioms QuantumNLS.Local023.norm_Phi_apply
#print axioms QuantumNLS.Local023.Phi_Psi
#print axioms QuantumNLS.Local023.Psi_Phi
#print axioms QuantumNLS.Local023.exists_equiv
#print axioms QuantumNLS.Local023.omega_DPhi
#print axioms QuantumNLS.Local023.inv_diff_bound
