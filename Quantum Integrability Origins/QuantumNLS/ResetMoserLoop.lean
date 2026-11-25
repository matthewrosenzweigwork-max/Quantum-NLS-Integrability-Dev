import QuantumNLS.ResetMoserPeriod

/-!
# `thm:reset-moser` (LOCAL-017), stage 3c (item 2(b), conclusion): the `β`-period of every flow loop vanishes

Source: `symplectic_correction.tex`, "The periods of a radial primitive": `A_j + 2π q_j ≡ 0` (`Hyp.Aper_eq`), "the loop `s ↦ φ_j^s(z)` has winding vector `−e_j`"
(`Hyp.winding`), and "`β = α − α^0`" with `α^0_z(h) = Im⟨z,h⟩ = ½ ω(z,h)`: the integral of `α^0` along the loop is `Σ_k |z_k|² · (winding)_k = −2π q_j`,
hence `∮ β = A_j − ∮ α^0 = −2π q_j + 2π q_j = 0`.

* `omega_eq_sum`: `ω(h,k) = 2 Σ_{n∈T} Im(conj(h_n) k_n)` when `h` vanishes off the finite set `T`;
* `Hyp.loop_beta_zero`: for `z ∈ B_ρ` with finite support `T` and `z_j ≠ 0`, `∫_0^{2π} β_{φ_j^s z}(X_j(φ_j^s z)) ds = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow

theorem inner_coord (a b : ℂ) : inner ℂ a b = conj a * b := by
  simp [RCLike.inner_apply, mul_comm]

theorem omega_eq_sum (T : Finset ℤ) (h k : K) (hT : ∀ n, n ∉ T → h n = 0) :
    omega h k = 2 * ∑ n ∈ T, (conj (h n) * k n).im := by
  unfold omega
  rw [lp.inner_eq_tsum, tsum_eq_sum (s := T) (fun n hn => by rw [hT n hn]; simp), Complex.im_sum]
  simp only [inner_coord]

theorem Hyp.gamma_coord_zero (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j : ℤ) {k : ℤ} (hk : z k = 0) (s : ℝ) :
    S.φ j s z k = 0 := by
  have := S.gamma_norm_coord hz j k s
  rw [hk, norm_zero] at this
  exact norm_eq_zero.1 this

theorem Hyp.loop_beta_zero (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K} (hz : z ∈ ball (0 : K) ρ)
    (T : Finset ℤ) (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) (hj : z j ≠ 0) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), betaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z)) = 0 := by
  have hzR : z ∈ ball (0 : K) S.R := ball_mono_R hL hz
  have hA := S.Aper_eq hL j hz
  unfold Aper at hA
  have hbc : Continuous (fun s => betaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z))) := by
    have h1 := S.cont_gamma hL j hz (g := betaR S)
      (fun w hw => (betaR_hasFDerivAt S hL hw).continuousAt)
    have h2 := S.cont_gamma hL j hz (g := Xn S.Ω j)
      (fun w hw => (S.Xn_contDiffAt (ball_mono_R hL hw) j).continuousAt)
    exact h1.clm_apply h2
  have hOc : Continuous (fun s => (1 / 2 : ℝ) * omegaF (S.φ j s z) (Xn S.Ω j (S.φ j s z))) := by
    have h1 := S.cont_gamma hL j hz (g := fun w : K => (omegaF : K →L[ℝ] Cov) w)
      (fun w _ => ((omegaF : K →L[ℝ] Cov).continuous).continuousAt)
    have h2 := S.cont_gamma hL j hz (g := Xn S.Ω j)
      (fun w hw => (S.Xn_contDiffAt (ball_mono_R hL hw) j).continuousAt)
    exact continuous_const.mul (h1.clm_apply h2)
  have hsplit : ∀ s : ℝ, alphaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z)) =
      betaR S (S.φ j s z) (Xn S.Ω j (S.φ j s z)) +
        (1 / 2 : ℝ) * omegaF (S.φ j s z) (Xn S.Ω j (S.φ j s z)) := by
    intro s; simp [alphaR]
  simp_rw [hsplit] at hA
  rw [intervalIntegral.integral_add (hbc.intervalIntegrable _ _) (hOc.intervalIntegrable _ _)] at hA
  -- the integral of ½ ω(γ, X_j γ)
  have hpt : ∀ s : ℝ, (1 / 2 : ℝ) * omegaF (S.φ j s z) (Xn S.Ω j (S.φ j s z)) =
      ∑ k ∈ T, ‖z k‖ ^ 2 * ang S j k (S.φ j s z) := by
    intro s
    rw [omegaF_apply, omega_eq_sum T (S.φ j s z) _ (fun n hn => S.gamma_coord_zero hzR j
      (by by_contra hne; exact hn ((hT n).1 hne)) s)]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hzk : z k ≠ 0 := (hT k).2 hk
    have hk' := S.gamma_coord_ne hzR j k hzk s
    have hn := S.gamma_norm_coord hzR j k s
    have hpos : 0 < ‖S.φ j s z k‖ := norm_pos_iff.2 hk'
    unfold ang
    rw [hn]
    rw [hn] at hpos
    field_simp
  have hωint : ∫ s in (0 : ℝ)..(2 * Real.pi), (1 / 2 : ℝ) * omegaF (S.φ j s z) (Xn S.Ω j (S.φ j s z)) =
      -(2 * Real.pi) * q j z := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_finset_sum (fun k hk => by
      exact (continuous_const.mul (S.ang_gamma_continuous hzR j k ((hT k).2 hk))).intervalIntegrable _ _)]
    have hk : ∀ k ∈ T, ∫ s in (0 : ℝ)..(2 * Real.pi), ‖z k‖ ^ 2 * ang S j k (S.φ j s z) =
        ‖z k‖ ^ 2 * (-(2 * Real.pi) * (if k = j then 1 else 0)) := by
      intro k hk
      rw [intervalIntegral.integral_const_mul, S.winding hL hz j k ((hT k).2 hk)]
    rw [Finset.sum_congr rfl hk]
    have hjT : j ∈ T := (hT j).1 hj
    have : ∀ k ∈ T, ‖z k‖ ^ 2 * (-(2 * Real.pi) * (if k = j then 1 else 0)) =
        if k = j then -(2 * Real.pi) * ‖z j‖ ^ 2 else 0 := by
      intro k _
      by_cases h : k = j
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' T j]
    simp [hjT, q]
  linarith

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.omega_eq_sum
#print axioms QuantumNLS.ResetMoser.Hyp.loop_beta_zero
