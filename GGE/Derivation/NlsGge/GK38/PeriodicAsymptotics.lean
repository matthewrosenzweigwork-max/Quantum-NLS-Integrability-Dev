import NlsGge.GK38.PeriodicAsymptoticsLocal
import NlsGge.GK38.PeriodicAsymptoticsL2
import NlsGge.GK38.PeriodicAsymptoticsCritical

/-! # S3: local square summability of periodic and critical spectral deviations

Book Proposition 6.7 and the asymptotic part of Lemma 6.5, with the separately
reviewed direct matrix argument for periodic roots. Every real tsum bound is
accompanied by its prior summability proof, for all complex potential pairs. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

/-- One neighbourhood and nonnegative constant bound both full spectral square sums. -/
theorem spectral_local_l2_38 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      Summable (fun n : ℤ => ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, (‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ≤ C ∧
      (∑' n : ℤ, ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ C := by
  obtain ⟨U, hU, N, _hN, hloc⟩ := labelling_local_bounds38 φ₀
  let b : ℝ := 2 * (N : ℝ) * Real.pi + Real.pi / 4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let R : ℝ := ‖φ₀‖ + 1
  obtain ⟨Cp, hCp, hp⟩ := perChar_roots_sine_l2_38 R b hb
  obtain ⟨Cd, hCd, hd⟩ := critical_roots_sine_l2_38 R b
  let T : ℝ := ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * b ^ 2
  let K : ℝ := Real.pi / 2 + 1
  let Bp : ℝ := T + K ^ 2 * Cp
  let Bd : ℝ := T + K ^ 2 * Cd
  have hBp : 0 ≤ Bp := by dsimp [Bp, T]; positivity
  have hBd : 0 ≤ Bd := by dsimp [Bd, T]; positivity
  refine ⟨U ∩ ball φ₀ 1, inter_mem hU (ball_mem_nhds φ₀ zero_lt_one),
    2 * Bp + Bd, by positivity, fun φ hφ => ?_⟩
  have hR : ‖φ‖ ≤ R := by
    have hdist : ‖φ - φ₀‖ < 1 := mem_ball_iff_norm.mp hφ.2
    have hn : ‖φ‖ ≤ ‖φ - φ₀‖ + ‖φ₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (φ - φ₀) φ₀
    dsimp [R]
    linarith
  obtain ⟨hshift, hfar⟩ := hloc φ hφ.1
  have hmRoot (n : ℤ) : perChar φ (lamMinus φ n) = 0 :=
    (lamSeq_enumeration38 φ).1 (2 * n)
  have hpRoot (n : ℤ) : perChar φ (lamPlus φ n) = 0 :=
    (lamSeq_enumeration38 φ).1 (2 * n + 1)
  have hdRoot (n : ℤ) : deriv (discrim φ) (lamDot φ n) = 0 :=
    (lamDot_enumeration38 φ).1 n
  obtain ⟨hsM, htM⟩ := hp φ hR (lamMinus φ) (fun n => (hshift n).1) hmRoot
  obtain ⟨hsP, htP⟩ := hp φ hR (lamPlus φ) (fun n => (hshift n).2.1) hpRoot
  obtain ⟨hsD, htD⟩ := hd φ hR (lamDot φ) (fun n => (hshift n).2.2) hdRoot
  have hm := localized_sine_l2_38 (lamMinus φ) N b Cp hb hCp
    (fun n => (hshift n).1) (fun n hn => ((hfar n hn).1).le) hsM htM
  have hp' := localized_sine_l2_38 (lamPlus φ) N b Cp hb hCp
    (fun n => (hshift n).2.1) (fun n hn => ((hfar n hn).2.1).le) hsP htP
  have hd' := localized_sine_l2_38 (lamDot φ) N b Cd hb hCd
    (fun n => (hshift n).2.2) (fun n hn => ((hfar n hn).2.2).le) hsD htD
  refine ⟨hm.1.add hp'.1, hd'.1, ?_, ?_⟩
  · rw [hm.1.tsum_add hp'.1]
    have hh := add_le_add hm.2 hp'.2
    change _ ≤ Bp + Bp at hh
    linarith
  · have hh := hd'.2
    change _ ≤ Bd at hh
    linarith

/-- The periodic local bound exports the summability prerequisite together with its bound. -/
theorem periodic_l2_summable38 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, (‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ≤ C := by
  obtain ⟨U, hU, C, hC, h⟩ := spectral_local_l2_38 φ₀
  exact ⟨U, hU, C, hC, fun φ hφ => ⟨(h φ hφ).1, (h φ hφ).2.2.1⟩⟩

/-- Book Lemma 6.5: the common local critical square sum, after summability. -/
theorem critical_l2 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ => ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ C := by
  obtain ⟨U, hU, C, hC, h⟩ := spectral_local_l2_38 φ₀
  exact ⟨U, hU, C, hC, fun φ hφ => ⟨(h φ hφ).2.1, (h φ hφ).2.2.2⟩⟩

/-- Exact S3 contract, book Proposition 6.7, for arbitrary complex L² pairs. -/
theorem periodic_l2 (φ₀ : PotPair) :
  ∃ U ∈ 𝓝 φ₀, ∃ c : ℝ, ∀ φ ∈ U,
    (∑' n : ℤ, (‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
      ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ≤ c := by
  obtain ⟨U, hU, C, _hC, h⟩ := periodic_l2_summable38 φ₀
  exact ⟨U, hU, C, fun φ hφ => (h φ hφ).2⟩

/-- Pointwise paired periodic summability, independent of any totalized tsum identity. -/
theorem periodic_summable38 (φ : PotPair) :
  Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
    ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  obtain ⟨U, hU, C, _hC, h⟩ := periodic_l2_summable38 φ
  exact (h φ (mem_of_mem_nhds hU)).1

/-- The minus enumeration has its own summability prerequisite for the S4 product. -/
theorem periodic_minus_summable38 (φ : PotPair) :
  Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
  (periodic_summable38 φ).of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ =>
    le_add_of_nonneg_right (sq_nonneg _))

/-- The plus enumeration has its own summability prerequisite for the S4 product. -/
theorem periodic_plus_summable38 (φ : PotPair) :
  Summable (fun n : ℤ => ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
  (periodic_summable38 φ).of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ =>
    le_add_of_nonneg_left (sq_nonneg _))

/-- Pointwise critical summability precedes its symmetric product representation. -/
theorem critical_summable38 (φ : PotPair) :
  Summable (fun n : ℤ => ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  obtain ⟨U, hU, C, _hC, h⟩ := critical_l2 φ
  exact (h φ (mem_of_mem_nhds hU)).1

end
end NlsGge.GK38
