import NlsGge.GK38.TauGammaCircleMoments

/-! Contour independence and fixed-family gluing precede analytic conclusions. -/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem moment_contour_independent38 (φ : PotPair) (C C' : ℤ → ℂ) (R R' : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (hf' : IsolatingFamily38 φ C' R') (n : ℤ) (k : ℕ) :
    CircleIntegrable (momentIntegrand38 φ k) (C n) (R n) ∧
      CircleIntegrable (momentIntegrand38 φ k) (C' n) (R' n) ∧
      circleIntegral (momentIntegrand38 φ k) (C n) (R n) =
        circleIntegral (momentIntegrand38 φ k) (C' n) (R' n) := by
  refine ⟨moment_circleIntegrable38 φ C R hf n k,
    moment_circleIntegrable38 φ C' R' hf' n k, ?_⟩
  rw [moment_circleIntegral38 φ C R hf n k, moment_circleIntegral38 φ C' R' hf' n k]

theorem moment_local_selector_glue38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (V : Set PotPair) (C₀ : ℤ → ℂ) (R₀ : ℤ → ℝ)
    (hV : V ⊆ gkW) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C₀ R₀)
    (φ : PotPair) (hφ : φ ∈ V) (n : ℤ) (k : ℕ) :
    fixedMoment38 φ (C φ) (R φ) n k = fixedMoment38 φ C₀ R₀ n k := by
  rw [fixedMoment_pair38 φ (C φ) (R φ) (hsel φ (hV hφ)) n k,
    fixedMoment_pair38 φ C₀ R₀ (hf φ hφ) n k]

theorem isolating_selectors_admissible38 : AdmissibleSelectors38 discC discR :=
  fun φ hφ => isolating_family38 φ hφ

theorem tau_pair_mean38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    tauN38 C R φ n = (lamPlus φ n + lamMinus φ n) / 2 := by
  rw [tauN38, moment_circleIntegral38 φ (C φ) (R φ) (hsel φ hφ) n 1]
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  simp only [pow_one]
  field_simp
  ring

theorem q2_pair_squares38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    q2N38 C R φ n = (lamPlus φ n) ^ 2 + (lamMinus φ n) ^ 2 := by
  rw [q2N38, fixedMoment_pair38 φ (C φ) (R φ) (hsel φ hφ) n 2, add_comm]

theorem gamma2_pair_gap38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    gamma2N38 C R φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := by
  rw [gamma2N38, q2_pair_squares38 C R hsel φ hφ n, tau_pair_mean38 C R hsel φ hφ n]
  ring

theorem gapMagnitude_pair_norm38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    gapMagnitude38 C R φ n = ‖lamPlus φ n - lamMinus φ n‖ := by
  rw [gapMagnitude38, gamma2_pair_gap38 C R hsel φ hφ n, norm_pow]
  exact Real.sqrt_sq (norm_nonneg _)

theorem selected_pair_identities38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    tauN38 C R φ n = (lamPlus φ n + lamMinus φ n) / 2 ∧
      q2N38 C R φ n = (lamPlus φ n) ^ 2 + (lamMinus φ n) ^ 2 ∧
      gamma2N38 C R φ n = (lamPlus φ n - lamMinus φ n) ^ 2 ∧
      gapMagnitude38 C R φ n = ‖lamPlus φ n - lamMinus φ n‖ :=
  ⟨tau_pair_mean38 C R hsel φ hφ n, q2_pair_squares38 C R hsel φ hφ n,
    gamma2_pair_gap38 C R hsel φ hφ n, gapMagnitude_pair_norm38 C R hsel φ hφ n⟩

theorem pair_polynomial_identity38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ) :
    (lamPlus φ n - z) * (lamMinus φ n - z) =
      (tauN38 C R φ n - z) ^ 2 - gamma2N38 C R φ n / 4 := by
  rw [tau_pair_mean38 C R hsel φ hφ n, gamma2_pair_gap38 C R hsel φ hφ n]
  ring

end
end NlsGge.GK38
