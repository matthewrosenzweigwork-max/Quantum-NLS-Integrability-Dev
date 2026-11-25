import Mathlib
import QuantumNLS.Local007Final
import QuantumNLS.Local007MassN
import QuantumNLS.Local007AlgA
import QuantumNLS.Local020PhiRot
import QuantumNLS.Local020DiscC
import QuantumNLS.Local020DiscR
import QuantumNLS.Local020Cov

/-! LOCAL-020: covariance of the exact indexed masses `I_n(u)` under reflection and conjugation,
`I_n(Ru) = I_{-n}(u)`, `I_n(ū) = I_{-n}(u)` for `‖u‖` small, via the accepted LOCAL-007 formula
`I_n(u) = (L|b|²/(4κ)) Re Phi(F(boost(-n)u), a - p_n, |b|²)`, the rotation invariance `Phi_rot`, and the discriminant laws
`Δ_{Ru}(z) = Δ_u(-z)`, `Δ_{ū}(z) = Δ_u(-z)`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)
open QuantumNLS.RootMassBoostSymbol (boost norm_boost coe_boost)

namespace QuantumNLS.Local020Mass

variable {L κ r ρ C : ℝ} [Fact (0 < L)]
variable {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ}

/-- Reflection commutes with boosts up to the sign of the index. -/
theorem boost_refl (n : ℤ) (u : L2T L) :
    boost (-n) (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) =
      QuantumNLS.ResetNormalizationUniqueness.reflectR L (boost n u) := by
  apply Lp.ext
  filter_upwards [coe_boost (-n) (QuantumNLS.ResetNormalizationUniqueness.reflectR L u),
    QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L u,
    QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L (boost n u),
    (QuantumNLS.ResetNormalizationUniqueness.negMP L).quasiMeasurePreserving.ae_eq_comp (coe_boost n u)] with x h1 h2 h3 h4
  rw [h1, h3]
  simp only [Function.comp] at h4
  rw [h4, h2]
  congr 1
  rw [fourier_neg, fourier_apply (n := n) (x := -x), smul_neg, fourier_neg']

theorem boost_star (n : ℤ) (u : L2T L) : boost (-n) (star u) = star (boost n u) := by
  apply Lp.ext
  filter_upwards [coe_boost (-n) (star u), Lp.coeFn_star u, Lp.coeFn_star (boost n u), coe_boost n u]
    with x h1 h2 h3 h4
  rw [h1, h3, h2]
  simp only [Pi.star_apply]
  rw [h4]
  simp [fourier_neg]

section FhLaws

open QuantumNLS.Local007AlgB (A)
open QuantumNLS.Local020PhiRot (shiftL shiftL_apply Phi_rot)

variable (κ : ℝ) {c : ℝ} {Fh : L2T L → A}

theorem exp_shift_pi (c : ℝ) (θ : ℝ) :
    (c : ℂ) * Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) = -((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem Fh_refl (hFh : ∀ v : L2T L, ‖v‖ < 1 → ∀ θ : ℝ,
    Fh v θ = QuantumNLS.Local007Zeros.Dl κ v ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
    {v : L2T L} (hv : ‖v‖ < 1) :
    Fh (QuantumNLS.ResetNormalizationUniqueness.reflectR L v) = shiftL Real.pi (Fh v) := by
  ext θ
  have hRv : ‖QuantumNLS.ResetNormalizationUniqueness.reflectR L v‖ < 1 := by
    rwa [LinearIsometry.norm_map]
  rw [hFh _ hRv, shiftL_apply, hFh v hv, exp_shift_pi]
  have := QuantumNLS.Local020DiscR.disc_refl κ (QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L v)
    (-((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
  rw [neg_neg] at this
  exact this

theorem Fh_star (hFh : ∀ v : L2T L, ‖v‖ < 1 → ∀ θ : ℝ,
    Fh v θ = QuantumNLS.Local007Zeros.Dl κ v ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
    {v : L2T L} (hv : ‖v‖ < 1) : Fh (star v) = shiftL Real.pi (Fh v) := by
  ext θ
  have hRv : ‖star v‖ < 1 := by rwa [QuantumNLS.ResetNormalizationUniqueness.norm_cj]
  rw [hFh _ hRv, shiftL_apply, hFh v hv, exp_shift_pi]
  exact QuantumNLS.Local020DiscC.disc_star κ v _

theorem Fh_per (hFh : ∀ v : L2T L, ‖v‖ < 1 → ∀ θ : ℝ,
    Fh v θ = QuantumNLS.Local007Zeros.Dl κ v ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
    {v : L2T L} (hv : ‖v‖ < 1) : shiftL (2 * Real.pi) (Fh v) = Fh v := by
  ext θ
  rw [shiftL_apply, hFh v hv, hFh v hv]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add]
  have : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := Complex.exp_two_pi_mul_I
  rw [this, mul_one]

end FhLaws

open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.Local007AlgB (Phi)

theorem mass_covariance (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρN : ℝ, 0 < ρN ∧ ∀ {ρ C : ℝ} {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ},
      (∀ n, Pkg L κ r ρ C n (a n) (b n)) → ∀ u ∈ ball (0 : L2T L) (min ρ ρN), ∀ n : ℤ,
        (masses hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u)).1 n = (masses hκ u).1 (-n) ∧
        (masses hκ (star u)).1 n = (masses hκ u).1 (-n) := by
  have hL : 0 < L := Fact.out
  set c : ℝ := 1 / (8 * L) with hc
  obtain ⟨Fh, -, hFh⟩ := QuantumNLS.Local007AlgA.Fhat_pkg (L := L) κ c
  obtain ⟨ρN, hρN, hmass⟩ := QuantumNLS.Local007MassN.mass_n hκ hr hr2 hc Fh hFh
  refine ⟨min ρN 1, lt_min hρN one_pos, ?_⟩
  intro ρ C a b hP u hu n
  have hu1 : ‖u‖ < ρ := lt_of_lt_of_le (mem_ball_zero_iff.1 hu) (min_le_left _ _)
  have hu2 : ‖u‖ < min ρN 1 := lt_of_lt_of_le (mem_ball_zero_iff.1 hu) (min_le_right _ _)
  have hu3 : ‖u‖ < ρN := lt_of_lt_of_le hu2 (min_le_left _ _)
  have hu4 : ‖u‖ < 1 := lt_of_lt_of_le hu2 (min_le_right _ _)
  have huρ : u ∈ ball (0 : L2T L) ρ := mem_ball_zero_iff.2 hu1
  -- the mass formula at a point of the ball
  have formula : ∀ (w : L2T L) (m : ℤ), ‖w‖ < ρ → ‖w‖ < ρN → (masses hκ w).1 m =
      (L * ‖b m w‖ ^ 2 / (4 * κ)) *
        (Phi c L (Fh (boost (-m) w)) (a m w - pm L m) (‖b m w‖ ^ 2)).re := by
    intro w m hw1 hw2
    have hwm : w ∈ ball (0 : L2T L) ρ := mem_ball_zero_iff.2 hw1
    have pk := (hP m).2.2.2.2.1 w hwm
    exact hmass w hw2 m (a m w) (b m w) pk.1 pk.2.2.2.1 pk.2.1 pk.2.2.1
  have bn : ‖boost n u‖ < 1 := by rwa [QuantumNLS.RootMassBoostSymbol.norm_boost]
  have e0 := formula u (-n) hu1 hu3
  rw [neg_neg] at e0
  have pm' : pm L (-n) = -pm L n := QuantumNLS.Local020Refl.pm_neg' n
  refine ⟨?_, ?_⟩
  · have hRu1 : ‖QuantumNLS.ResetNormalizationUniqueness.reflectR L u‖ < ρ := by rwa [LinearIsometry.norm_map]
    have hRu3 : ‖QuantumNLS.ResetNormalizationUniqueness.reflectR L u‖ < ρN := by rwa [LinearIsometry.norm_map]
    rw [formula _ n hRu1 hRu3, e0]
    obtain ⟨hb, ha⟩ := QuantumNLS.Local020Cov.cov_refl hP huρ (-n)
    rw [neg_neg] at hb ha
    rw [hb, ha, boost_refl, Fh_refl κ hFh bn]
    have := QuantumNLS.Local020PhiRot.Phi_rot c L (Fh (boost n u)) (Fh_per κ hFh bn) (a (-n) u - pm L (-n)) (‖b (-n) u‖ ^ 2)
    have e2 : -a (-n) u - pm L n = -(a (-n) u - pm L (-n)) := by rw [pm']; ring
    rw [e2, this]
  · have hRu1 : ‖star u‖ < ρ := by rwa [QuantumNLS.ResetNormalizationUniqueness.norm_cj]
    have hRu3 : ‖star u‖ < ρN := by rwa [QuantumNLS.ResetNormalizationUniqueness.norm_cj]
    rw [formula _ n hRu1 hRu3, e0]
    obtain ⟨hb, ha⟩ := QuantumNLS.Local020Cov.cov_conj hP huρ (-n)
    rw [neg_neg] at hb ha
    rw [hb, ha, norm_neg, Complex.norm_conj, boost_star, Fh_star κ hFh bn]
    have := QuantumNLS.Local020PhiRot.Phi_rot c L (Fh (boost n u)) (Fh_per κ hFh bn) (a (-n) u - pm L (-n)) (‖b (-n) u‖ ^ 2)
    have e2 : -a (-n) u - pm L n = -(a (-n) u - pm L (-n)) := by rw [pm']; ring
    rw [e2, this]

end QuantumNLS.Local020Mass

#print axioms QuantumNLS.Local020Mass.mass_covariance
