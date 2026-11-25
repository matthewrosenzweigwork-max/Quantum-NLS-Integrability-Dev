import QuantumNLS.ResetMoserBetaData
import QuantumNLS.ResetMoserPullback
import QuantumNLS.ResetMoserAnalytic

/-!
# `thm:reset-moser` (LOCAL-017): the action-preserving correction, as one theorem

Source: `symplectic_correction.tex:25`, Theorem `thm:reset-moser` ("Proved: Action-preserving correction"): "Suppose that `Ω` is a real-analytic closed two-form on an open ball `B_R ⊂ ℋ`.  Suppose that its values
are bounded alternating bilinear forms, analytically in the full operator norm, and `Ω_z = ω + O(‖z‖²)`, `‖Ω_z − ω‖ < 1`.  Assume that the `q_n` pairwise Poisson commute for `Ω`, and their Hamiltonian flows exist
on `B_R` and have time `2π` equal to the identity.  Then, on a smaller ball `B_r` ..., the procedure specified below constructs a real-analytic diffeomorphism `S : B_r → B_r` such that `S^*Ω = ω`,
`q_n ∘ S = q_n` (`n ∈ ℤ`), `S(z) = z + O(‖z‖³)`.  Both `S` and `S^{-1}` have bounded full Hilbert differentials on every sufficiently small closed subball, with `‖DS(z) − 1‖ + ‖DS^{-1}(z) − 1‖ ≤ C‖z‖²`.
All assertions include zero coordinates and infinite support."

The hypotheses are exactly the structure `Hyp S` (`ResetMoserHyp`, the printed hypotheses literally).  No other hypothesis.  `reset_moser S`: there are `r ∈ (0, R]`, maps `S, S⁻¹ : K → K`, and `C ≥ 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp

/-- **`thm:reset-moser` (LOCAL-017).** -/
theorem reset_moser (S : Hyp) :
    ∃ r : ℝ, 0 < r ∧ r ≤ S.R ∧ ∃ (Sm Si : K → K) (C : ℝ), 0 ≤ C ∧
      (∀ z ∈ ball (0 : K) r, Sm z ∈ ball (0 : K) r ∧ Si z ∈ ball (0 : K) r) ∧
      (∀ z ∈ ball (0 : K) r, Si (Sm z) = z ∧ Sm (Si z) = z) ∧
      AnalyticOnNhd ℝ Sm (ball (0 : K) r) ∧ AnalyticOnNhd ℝ Si (ball (0 : K) r) ∧
      (∀ z ∈ ball (0 : K) r, ∀ a b : K, S.Ω (Sm z) (fderiv ℝ Sm z a) (fderiv ℝ Sm z b) = omegaF a b) ∧
      (∀ (n : ℤ), ∀ z ∈ ball (0 : K) r, q n (Sm z) = q n z) ∧
      (∀ z ∈ ball (0 : K) r, ‖Sm z - z‖ ≤ C * ‖z‖ ^ 3) ∧
      (∀ z ∈ ball (0 : K) r, ‖fderiv ℝ Sm z - 1‖ + ‖fderiv ℝ Si z - 1‖ ≤ C * ‖z‖ ^ 2) := by
  set MD := moserData S with hMD
  have hR0 := MD.R0_pos
  obtain ⟨κ, hκ, hv⟩ := MD.exists_var_bound
  have hB := MD.B_nonneg
  refine ⟨MD.R0 / 4, by positivity, ?_, MD.Sfl 1, MD.Tinv, MD.B + 2 * κ * Real.exp (κ * MD.R0 ^ 2),
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := MD.hL.ρR
    have h2 : MD.R0 / 4 ≤ MD.R0 := by linarith
    exact h2.trans this
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    exact ⟨by rw [mem_ball_zero_iff, MD.norm_Sfl]; exact hn, by rw [mem_ball_zero_iff, MD.norm_Tinv]; exact hn⟩
  · intro z _
    exact ⟨MD.Tinv_Sfl_one z, MD.Sfl_one_Tinv z⟩
  · intro z hz
    exact MD.Sfl_one_analyticAt (mem_ball_zero_iff.1 hz)
  · intro z hz
    exact MD.Tinv_analyticAt (mem_ball_zero_iff.1 hz)
  · intro z hz a b
    exact MD.pullback (mem_ball_zero_iff.1 hz) a b
  · intro n z _
    exact MD.q_Sfl n 1 z
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    refine (MD.norm_Sfl_sub_le hn).trans ?_
    have h3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    have : MD.B ≤ MD.B + 2 * κ * Real.exp (κ * MD.R0 ^ 2) := by
      have : 0 ≤ 2 * κ * Real.exp (κ * MD.R0 ^ 2) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this h3
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    have hz2 : ‖z‖ ^ 2 ≤ MD.R0 ^ 2 := by
      have : ‖z‖ ≤ MD.R0 := by linarith
      nlinarith [norm_nonneg z]
    have hexp : Real.exp (κ * ‖z‖ ^ 2) ≤ Real.exp (κ * MD.R0 ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz2 hκ)
    have h1 : ‖Lam (fderiv ℝ (MD.Fl 1) (z, 0)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * ‖z‖ ^ 2) := by
      have := hv (z, 0) (by simpa using hn) 1 (by simp) 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    have h2 : ‖Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * ‖z‖ ^ 2) := by
      have := hv (z, 1) (by simpa using hn) (-1) (by simp) 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    have e1 : fderiv ℝ (MD.Sfl 1) z = Lam (fderiv ℝ (MD.Fl 1) (z, 0)) := MD.DS_eq 1 z
    have e2 : fderiv ℝ MD.Tinv z = Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) := (MD.hasFDerivAt_Tinv z).fderiv
    rw [e1, e2]
    have hk : 0 ≤ κ * ‖z‖ ^ 2 := by positivity
    have h1' : ‖Lam (fderiv ℝ (MD.Fl 1) (z, 0)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * MD.R0 ^ 2) :=
      h1.trans (mul_le_mul_of_nonneg_left hexp hk)
    have h2' : ‖Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * MD.R0 ^ 2) :=
      h2.trans (mul_le_mul_of_nonneg_left hexp hk)
    have hBz : 0 ≤ MD.B * ‖z‖ ^ 2 := by positivity
    nlinarith [h1', h2', hBz]

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.reset_moser
#check @QuantumNLS.ResetMoser.reset_moser
