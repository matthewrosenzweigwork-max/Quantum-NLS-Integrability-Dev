import Mathlib
import NlsGge.Atomic.G1.G1050
import NlsGge.Atomic.G1.G1052
import NlsGge.Atomic.G1.G1053
import NlsGge.GK38.TauGammaCoefficient

set_option autoImplicit false

/- G1-054 COMMAND02 (proof development) pre-approval proof, GRAPH-ROUTE rework (proof development, AUTHOR; not self-reviewed).  GK Lemma 6.9, tail-local route.
   Uniform inputs (graph route, landed): G1-048/G1-052 counting (`simultaneous_counting_lemmaG`, `labelling_local_boundsG`), G1-052 `periodic_l2G`, G1-053 `perChar_eq_periodicProductG`,
   G1-047 relative asymptotics (`perChar_asympG`, `critical_asymp`), G1-050 critical l2 (`critical_l2G`).  Production lemmas used only if their dependency closure is free of
   `perChar_eq_periodicProduct38`, `productRepr_*`, `Lib.product_growth`, `periodic_l2_summable38` (checked by an #eval constant-closure probe): `paired_omit_cauchy38`, `critical_denominator_algebra38`,
   `sinc_square_inner_bound38`, `sincAt_square_translate38`, `sincSquareProfile_entire38`, `Lib.omitProd/multipliable_omit/entProd_eq_mul_omitProd/analyticAt_omitProd_line`, `l2SequenceOf_*`, `pairedFactors_eq_mul38`.
   Local graph-route copies (section GraphRoute) of `exterior_perChar_factor38`, `exterior_entire38`, `exterior_eq_omitProducts38`, `exterior_inner_error_bounds38`, `periodic_deviation_norms_local38`
   with explicit summability hypotheses from `periodic_l2G` (G1-044M PROOF04 precedent).  Steps: (1) Rouche on small circles gives uniform location of lamDot, lamPlus, lamMinus in ball(n pi, r);
   (2) maximum principle plus G1-047 on the circle of radius pi/4: ext_n(z) = sinc^2(z - n pi) + O(1/8) uniformly, hence |q - 1| <= 1/4; (3) the critical-point equation from
   perChar = -4 (a - z)(b - z) ext_n(z) and the algebra `critical_denominator_algebra38` give d = g q'/(4 (2 q + d q')); (4) l2 bound of q' from `paired_omit_cauchy38` and `critical_l2G`. -/

namespace NlsGge.Atomic.G1054S3

open Filter Topology Set Metric NlsGge.GK38 NlsGge.Pilot NlsGge.Atomic.G1050S2 NlsGge.Atomic.G1052S3

noncomputable section

/-- Maximum principle: a bound on a sphere propagates to the closed ball (entire function). -/
theorem bound_closedBall_of_sphere {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) (c : ℂ) {R : ℝ}
    (hR : 0 < R) {B : ℝ} (hB : ∀ z ∈ sphere c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall c R, ‖f z‖ ≤ B := by
  intro z hz
  have hdiff : Differentiable ℂ f := fun w => (hf w (mem_univ w)).differentiableAt
  have hd : DiffContOnCl ℂ f (ball c R) := hdiff.diffContOnCl
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hd ?_ ?_
  · rw [frontier_ball c hR.ne']
    exact hB
  · rw [closure_ball c hR.ne']
    exact hz

theorem norm_cos_lattice (n : ℤ) : ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖ = 1 := by
  have h := cos_lattice_square38 n
  have h2 : ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖ ^ 2 = 1 := by
    rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp h2

theorem norm_sin_translate (n : ℤ) (z : ℂ) :
    ‖Complex.sin z‖ = ‖Complex.sin (z - (n : ℂ) * (Real.pi : ℂ))‖ := by
  have h := Complex.sin_add (z - (n : ℂ) * (Real.pi : ℂ)) ((n : ℂ) * (Real.pi : ℂ))
  simp only [sub_add_cancel, Complex.sin_int_mul_pi, mul_zero, add_zero] at h
  rw [h, norm_mul, norm_cos_lattice, mul_one]

theorem sin_sphere_lower {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi) :
    ∃ m : ℝ, 0 < m ∧ ∀ w : ℂ, ‖w‖ = r → m ≤ ‖Complex.sin w‖ := by
  have hne : ∀ w ∈ sphere (0 : ℂ) r, Complex.sin w ≠ 0 := by
    intro w hw h0
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
    have hn : ‖w‖ = r := by simpa using hw
    have hk' : w = countingCenter38 k := hk
    rw [hk', norm_countingCenter38] at hn
    have h1 : |(k : ℝ)| < 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [Real.pi_pos]
    have hk0 : k = 0 := by
      have h2 : |k| < 1 := by exact_mod_cast h1
      obtain ⟨a, b⟩ := abs_lt.mp h2
      omega
    subst hk0
    simp [countingCenter38] at hn
    linarith
  obtain ⟨m, hm, hmin⟩ := Lib.exists_pos_le_norm_sphere hr
    (Complex.continuous_sin.continuousOn) hne
  exact ⟨m, hm, fun w hw => hmin w (by simpa using hw)⟩

theorem free_small_card (n : ℤ) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ Real.pi / 4) :
    Multiset.card (Lib.zeroMultiset (perChar 0) (ball (countingCenter38 n) r)) = 2 := by
  have he := Lib.zeroMultiset_ball_eq_replicate hr
    ((analyticOnNhd_perChar_z 0).mono (subset_univ _)) (a := countingCenter38 n)
    (fun z hz hzn => ?_)
  · have hsin : Complex.sin (countingCenter38 n) = 0 := Complex.sin_eq_zero_iff.mpr ⟨n, rfl⟩
    rw [he, Multiset.card_replicate, counting_free_order38, if_pos hsin]
  · intro hz0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp ((counting_free_zero_iff38 z).mp hz0)
    have hmn : m ≠ n := by
      intro h
      apply hzn
      simpa only [h, countingCenter38] using hm
    have hsep := countingCenter_separated38 hmn
    have hclose : ‖countingCenter38 m - countingCenter38 n‖ ≤ r := by
      simpa only [mem_closedBall, dist_eq_norm, countingCenter38, ← hm] using hz
    linarith [Real.pi_pos]

theorem free_small_card_crit (n : ℤ) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ Real.pi / 4) :
    Multiset.card (Lib.zeroMultiset (deriv (NlsGge.GK38.discrim 0)) (ball (countingCenter38 n) r)) = 1 := by
  have he := Lib.zeroMultiset_ball_eq_replicate hr
    ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _)) (a := countingCenter38 n)
    (fun z hz hzn => ?_)
  · have hsin : Complex.sin (countingCenter38 n) = 0 := Complex.sin_eq_zero_iff.mpr ⟨n, rfl⟩
    rw [he, Multiset.card_replicate, critical_free_order38, if_pos hsin]
  · intro hz0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp ((critical_free_zero_iff38 z).mp hz0)
    have hmn : m ≠ n := by
      intro h
      apply hzn
      simpa only [h, countingCenter38] using hm
    have hsep := countingCenter_separated38 hmn
    have hclose : ‖countingCenter38 m - countingCenter38 n‖ ≤ r := by
      simpa only [mem_closedBall, dist_eq_norm, countingCenter38, ← hm] using hz
    linarith [Real.pi_pos]

/-- A root in the larger ball lies in the smaller one when both multisets have equal cardinality. -/
theorem root_in_small_of_card {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) {c : ℂ} {r R : ℝ}
    (hrR : r ≤ R) (hw : ∃ w ∈ closedBall c R, F w ≠ 0)
    (hcard : Multiset.card (Lib.zeroMultiset F (ball c r)) =
      Multiset.card (Lib.zeroMultiset F (ball c R)))
    {z : ℂ} (hz : z ∈ ball c R) (hz0 : F z = 0) : z ∈ ball c r := by
  classical
  have hle : Lib.zeroMultiset F (ball c r) ≤ Lib.zeroMultiset F (ball c R) := by
    rw [Multiset.le_iff_count]
    intro w
    rw [Lib.count_zeroMultiset_ball (hF.mono (subset_univ _)),
      Lib.count_zeroMultiset_ball (hF.mono (subset_univ _))]
    by_cases h1 : w ∈ ball c r
    · rw [if_pos h1, if_pos (ball_subset_ball hrR h1)]
    · rw [if_neg h1]
      exact Nat.zero_le _
  have heq := Multiset.eq_of_le_of_card_le hle hcard.ge
  have hmem : z ∈ Lib.zeroMultiset F (ball c R) :=
    (Lib.mem_zeroMultiset_iff_zero (hF.mono (subset_univ _)) ball_subset_closedBall hw).2 ⟨hz, hz0⟩
  rw [← heq] at hmem
  exact ((Lib.mem_zeroMultiset_iff_zero (hF.mono (subset_univ _))
    (ball_subset_ball hrR |>.trans ball_subset_closedBall) hw).1 hmem).1


theorem roots_in_small_ball (φ0 : PotPair) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ Real.pi / 4) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ0 ∧ ∃ N : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, (N : ℤ) < |n| →
      Multiset.card (Lib.zeroMultiset (deriv (discrim ψ))
        (ball (countingCenter38 n) (Real.pi / 4))) = 1 ∧
      lamDot ψ n ∈ ball (countingCenter38 n) r ∧
      lamPlus ψ n ∈ ball (countingCenter38 n) r ∧ lamMinus ψ n ∈ ball (countingCenter38 n) r ∧
      (∀ z1 ∈ ball (countingCenter38 n) (Real.pi / 4), ∀ z2 ∈ ball (countingCenter38 n) (Real.pi / 4),
        deriv (discrim ψ) z1 = 0 → deriv (discrim ψ) z2 = 0 → z1 = z2) := by
  obtain ⟨m, hm, hmlow⟩ := sin_sphere_lower hr (by linarith [Real.pi_pos])
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) (Real.pi / 4)).exists_bound_of_continuousOn
    Complex.continuous_sin.continuousOn
  set M1 : ℝ := max M0 1 with hM1def
  have hM1pos : 0 < M1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM1 : ∀ w : ℂ, ‖w‖ ≤ Real.pi / 4 → ‖Complex.sin w‖ ≤ M1 := fun w hw =>
    (hM0 w (by simpa using hw)).trans (le_max_left _ _)
  set ε : ℝ := min (m / (2 * M1)) (2 * m ^ 2 / M1 ^ 2) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ m / (2 * M1) := min_le_left _ _
  have hε2 : ε ≤ 2 * m ^ 2 / M1 ^ 2 := min_le_right _ _
  obtain ⟨U1, hU1, R1, h1⟩ := perChar_asympG φ0 ε hεpos
  obtain ⟨U2, hU2, R2, h2⟩ := critical_asymp φ0 ε hεpos
  obtain ⟨U3, hU3, N3, hN3⟩ := simultaneous_counting_lemmaG φ0
  obtain ⟨U4, hU4, N4, -, hN4⟩ := labelling_local_boundsG φ0
  obtain ⟨K, hK⟩ := exists_nat_gt ((max R1 R2 + Real.pi) / Real.pi)
  refine ⟨U1 ∩ (U2 ∩ (U3 ∩ U4)), inter_mem hU1 (inter_mem hU2 (inter_mem hU3 hU4)),
    max K (max N3 N4), fun ψ hψ n hn => ?_⟩
  obtain ⟨hψ1, hψ2, hψ3, hψ4⟩ := hψ
  have hnK : (K : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_left _ _) hn
  have hnN3 : (N3 : ℤ) < |n| :=
    lt_of_le_of_lt (by exact_mod_cast (le_max_left N3 N4).trans (le_max_right K _)) hn
  have hnN4 : (N4 : ℤ) < |n| :=
    lt_of_le_of_lt (by exact_mod_cast (le_max_right N3 N4).trans (le_max_right K _)) hn
  have hn1 : (K : ℝ) + 1 ≤ |(n : ℝ)| := by
    have : (K : ℤ) + 1 ≤ |n| := hnK
    have h' : ((K : ℤ) : ℝ) + 1 ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hRz : ∀ z ∈ sphere (countingCenter38 n) (Real.pi / 4), max R1 R2 < ‖z‖ := by
    intro z hz
    have hz' : ‖z - countingCenter38 n‖ = Real.pi / 4 := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    have h3 : ‖countingCenter38 n‖ - ‖z - countingCenter38 n‖ ≤ ‖z‖ := by
      have h5 : ‖countingCenter38 n‖ ≤ ‖z‖ + ‖z - countingCenter38 n‖ := by
        calc ‖countingCenter38 n‖ = ‖z + (countingCenter38 n - z)‖ := by congr 1; ring
          _ ≤ ‖z‖ + ‖countingCenter38 n - z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖z - countingCenter38 n‖ := by rw [norm_sub_rev]
      linarith
    rw [norm_countingCenter38] at h3
    have hK' : (max R1 R2 + Real.pi) < (K : ℝ) * Real.pi := by
      have := (div_lt_iff₀ Real.pi_pos).mp hK
      linarith
    nlinarith [Real.pi_pos, hn1]
  have hsinsph : ∀ z ∈ sphere (countingCenter38 n) (Real.pi / 4), ‖Complex.sin z‖ ≤ M1 := by
    intro z hz
    rw [norm_sin_translate n z]
    exact hM1 _ (by simpa [mem_sphere, dist_eq_norm, countingCenter38] using hz.le)
  have hsin_an : ∀ z : ℂ, AnalyticAt ℂ Complex.sin z := fun z => Complex.differentiable_sin.analyticAt z
  have hsep_of : ∀ z ∈ sphere (countingCenter38 n) (Real.pi / 4), ∀ k : ℤ,
      Real.pi / 4 ≤ ‖z - countingCenter38 k‖ := fun z hz k =>
    counting_small_sphere_separated38 n hz k
  -- sup bounds on the closed ball of radius pi/4
  have hchi : ∀ z ∈ closedBall (countingCenter38 n) (Real.pi / 4),
      ‖perChar ψ z + 4 * Complex.sin z ^ 2‖ ≤ ε * M1 ^ 2 := by
    refine bound_closedBall_of_sphere (f := fun z => perChar ψ z + 4 * Complex.sin z ^ 2)
      ((analyticOnNhd_perChar_z ψ).add (fun z _ => analyticAt_const.mul ((hsin_an z).pow 2)))
      _ (by positivity) ?_
    intro z hz
    have h := h1 ψ hψ1 z (lt_of_le_of_lt (le_max_left _ _) (hRz z hz)) (hsep_of z hz)
    have he : perChar ψ z + 4 * Complex.sin z ^ 2 = perChar ψ z - (-4 * Complex.sin z ^ 2) := by ring
    rw [he]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hεpos.le)
    exact pow_le_pow_left₀ (norm_nonneg _) (hsinsph z hz) 2
  have hcrit : ∀ z ∈ closedBall (countingCenter38 n) (Real.pi / 4),
      ‖deriv (discrim ψ) z + 2 * Complex.sin z‖ ≤ 2 * ε * M1 := by
    refine bound_closedBall_of_sphere (f := fun z => deriv (discrim ψ) z + 2 * Complex.sin z)
      ((analyticOnNhd_discrimDeriv38 ψ).add (fun z _ => analyticAt_const.mul (hsin_an z)))
      _ (by positivity) ?_
    intro z hz
    have h := h2 ψ hψ2 z (lt_of_le_of_lt (le_max_right _ _) (hRz z hz)) (hsep_of z hz)
    have he : deriv (discrim ψ) z + 2 * Complex.sin z = deriv (discrim ψ) z - (-2 * Complex.sin z) := by ring
    rw [he]
    refine h.trans ?_
    have hn2 : ‖(-2 : ℂ) * Complex.sin z‖ = 2 * ‖Complex.sin z‖ := by
      rw [norm_mul]; simp
    rw [hn2]
    nlinarith [hsinsph z hz, hεpos]
  have hr_sub : sphere (countingCenter38 n) r ⊆ closedBall (countingCenter38 n) (Real.pi / 4) :=
    fun z hz => by
      rw [mem_sphere] at hz
      rw [mem_closedBall]
      linarith
  have hsinr : ∀ z ∈ sphere (countingCenter38 n) r, m ≤ ‖Complex.sin z‖ := by
    intro z hz
    rw [norm_sin_translate n z]
    exact hmlow _ (by simpa [mem_sphere, dist_eq_norm, countingCenter38] using hz)
  have hεM : ε * M1 ^ 2 ≤ 2 * m ^ 2 := by
    have := (le_div_iff₀ (by positivity : 0 < M1 ^ 2)).mp hε2
    linarith
  have hεM' : 2 * ε * M1 ≤ m := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * M1)).mp hε1
    linarith
  -- Rouche for chi
  have hcmpχ : ∀ z ∈ sphere (countingCenter38 n) r,
      ‖perChar ψ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
    intro z hz
    have hb := hchi z (hr_sub hz)
    have he : perChar ψ z - perChar 0 z = perChar ψ z + 4 * Complex.sin z ^ 2 := by
      rw [perChar_zero]; ring
    rw [he, perChar_zero]
    have hn4 : ‖(-4 : ℂ) * Complex.sin z ^ 2‖ = 4 * ‖Complex.sin z‖ ^ 2 := by
      rw [norm_mul, norm_pow]; simp
    rw [hn4]
    have hmz := hsinr z hz
    nlinarith [hmz, hm]
  have hnezχ : ∀ z ∈ sphere (countingCenter38 n) r, perChar ψ z ≠ 0 := by
    intro z hz h0
    have := hcmpχ z hz
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  have hcmpΔ : ∀ z ∈ sphere (countingCenter38 n) r,
      ‖deriv (discrim ψ) z - deriv (NlsGge.GK38.discrim 0) z‖ < ‖deriv (NlsGge.GK38.discrim 0) z‖ := by
    intro z hz
    have hb := hcrit z (hr_sub hz)
    have h0 : deriv (NlsGge.GK38.discrim 0) z = -2 * Complex.sin z := by rw [discrimDeriv_zero38]
    have he : deriv (discrim ψ) z - deriv (NlsGge.GK38.discrim 0) z = deriv (discrim ψ) z + 2 * Complex.sin z := by
      rw [h0]; ring
    rw [he, h0]
    have hn2 : ‖(-2 : ℂ) * Complex.sin z‖ = 2 * ‖Complex.sin z‖ := by
      rw [norm_mul]; simp
    rw [hn2]
    have hmz := hsinr z hz
    nlinarith [hmz, hm]
  have hnezΔ : ∀ z ∈ sphere (countingCenter38 n) r, deriv (discrim ψ) z ≠ 0 := by
    intro z hz h0
    have := hcmpΔ z hz
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  have hw0 : countingCenter38 n + (r : ℂ) ∈ sphere (countingCenter38 n) r := by
    simp [mem_sphere, dist_eq_norm, abs_of_pos hr]
  have hw1 : countingCenter38 n + (r : ℂ) ∈ closedBall (countingCenter38 n) (Real.pi / 4) :=
    hr_sub hw0
  -- counts
  have hcardχ : Multiset.card (Lib.zeroMultiset (perChar ψ) (ball (countingCenter38 n) r)) =
      Multiset.card (Lib.zeroMultiset (perChar ψ) (ball (countingCenter38 n) (Real.pi / 4))) := by
    rw [(hN3 ψ hψ3).1.2.2.2.2.1 n hnN3]
    have := Lib.rouche_circle (c := countingCenter38 n) hr
      ((analyticOnNhd_perChar_z 0).mono (subset_univ _))
      ((analyticOnNhd_perChar_z ψ).mono (subset_univ _)) hcmpχ
    rw [this]
    exact free_small_card n hr hr4
  have hcardΔ : Multiset.card (Lib.zeroMultiset (deriv (discrim ψ)) (ball (countingCenter38 n) r)) =
      Multiset.card (Lib.zeroMultiset (deriv (discrim ψ)) (ball (countingCenter38 n) (Real.pi / 4))) := by
    rw [(hN3 ψ hψ3).2.2.2.2.2.1 n hnN3]
    have := Lib.rouche_circle (c := countingCenter38 n) hr
      ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _))
      ((analyticOnNhd_discrimDeriv38 ψ).mono (subset_univ _)) hcmpΔ
    rw [this]
    exact free_small_card_crit n hr hr4
  have hrootχ : ∀ z ∈ ball (countingCenter38 n) (Real.pi / 4), perChar ψ z = 0 →
      z ∈ ball (countingCenter38 n) r := fun z hz hz0 =>
    root_in_small_of_card (analyticOnNhd_perChar_z ψ) hr4
      ⟨_, hw1, hnezχ _ hw0⟩ hcardχ hz hz0
  have hrootΔ : ∀ z ∈ ball (countingCenter38 n) (Real.pi / 4), deriv (discrim ψ) z = 0 →
      z ∈ ball (countingCenter38 n) r := fun z hz hz0 =>
    root_in_small_of_card (analyticOnNhd_discrimDeriv38 ψ) hr4
      ⟨_, hw1, hnezΔ _ hw0⟩ hcardΔ hz hz0
  refine ⟨(hN3 ψ hψ3).2.2.2.2.2.1 n hnN3, ?_, ?_, ?_, ?_⟩
  · -- lamDot
    have hcnt := (hN3 ψ hψ3).2
    have heq := lamDot_eq_candidate38 ψ hcnt
    have hsh := (criticalCandidate_shift_bound38 hcnt n).2 hnN3
    have hD : lamDot ψ n ∈ ball (countingCenter38 n) (Real.pi / 4) := by
      rw [heq]; exact mem_ball_iff_norm.mpr hsh
    exact hrootΔ _ hD ((lamDot_enumeration38 ψ).1 n)
  · have hD : lamPlus ψ n ∈ ball (countingCenter38 n) (Real.pi / 4) :=
      mem_ball_iff_norm.mpr (hN4 ψ hψ4 |>.2 n hnN4).2
    exact hrootχ _ hD ((lamSeq_enumeration38 ψ).1 (2 * n + 1))
  · have hD : lamMinus ψ n ∈ ball (countingCenter38 n) (Real.pi / 4) :=
      mem_ball_iff_norm.mpr (hN4 ψ hψ4 |>.2 n hnN4).1
    exact hrootχ _ hD ((lamSeq_enumeration38 ψ).1 (2 * n))
  · have hcard1 := (hN3 ψ hψ3).2.2.2.2.2.1 n hnN3
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hcard1
    have hmemΔ : ∀ z ∈ ball (countingCenter38 n) (Real.pi / 4), deriv (discrim ψ) z = 0 →
        z ∈ Lib.zeroMultiset (deriv (discrim ψ)) (ball (countingCenter38 n) (Real.pi / 4)) :=
      fun z hz hz0 =>
        (Lib.mem_zeroMultiset_iff_zero ((analyticOnNhd_discrimDeriv38 ψ).mono (subset_univ _))
          ball_subset_closedBall ⟨_, hw1, hnezΔ _ hw0⟩).2 ⟨hz, hz0⟩
    intro z1 hz1 z2 hz2 h1 h2
    have m1 := hmemΔ z1 hz1 h1
    have m2 := hmemΔ z2 hz2 h2
    rw [hx, Multiset.mem_singleton] at m1 m2
    rw [m1, m2]


theorem sphere_norm_gt {R : ℝ} {K : ℕ} (hK : (R + Real.pi) / Real.pi < K) {n : ℤ}
    (hn : (K : ℤ) < |n|) {z : ℂ} (hz : z ∈ sphere (countingCenter38 n) (Real.pi / 4)) :
    R < ‖z‖ := by
  have hn1 : (K : ℝ) + 1 ≤ |(n : ℝ)| := by
    have : (K : ℤ) + 1 ≤ |n| := hn
    have h' : ((K : ℤ) : ℝ) + 1 ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hz' : ‖z - countingCenter38 n‖ = Real.pi / 4 := by
    simpa only [mem_sphere, dist_eq_norm] using hz
  have h3 : ‖countingCenter38 n‖ - ‖z - countingCenter38 n‖ ≤ ‖z‖ := by
    have h5 : ‖countingCenter38 n‖ ≤ ‖z‖ + ‖z - countingCenter38 n‖ := by
      calc ‖countingCenter38 n‖ = ‖z + (countingCenter38 n - z)‖ := by congr 1; ring
        _ ≤ ‖z‖ + ‖countingCenter38 n - z‖ := norm_add_le _ _
        _ = ‖z‖ + ‖z - countingCenter38 n‖ := by rw [norm_sub_rev]
    linarith
  rw [norm_countingCenter38] at h3
  have hK' : R + Real.pi < (K : ℝ) * Real.pi := by
    have := (div_lt_iff₀ Real.pi_pos).mp hK
    linarith
  nlinarith [Real.pi_pos, hn1]

theorem E_bound (χ s P w : ℂ) {p0 W c1 c2 c3 : ℝ} (hp0 : 0 < p0) (hP : p0 ≤ ‖P‖) (hW : 0 < W)
    (hw : ‖w‖ = W) (h1 : ‖χ + 4 * s‖ ≤ c1) (h2 : ‖s‖ ≤ c2) (h3 : ‖P - w ^ 2‖ ≤ c3) :
    ‖χ / (-4 * P) - s / w ^ 2‖ ≤ c1 / (4 * p0) + c2 * c3 / (p0 * W ^ 2) := by
  have hPne : P ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hp0 hP)
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    linarith
  have hid : χ / (-4 * P) - s / w ^ 2 =
      ((χ + 4 * s) * w ^ 2 + 4 * s * (P - w ^ 2)) / (-4 * P * w ^ 2) := by
    field_simp
    ring
  rw [hid, norm_div]
  have hden : 4 * p0 * W ^ 2 ≤ ‖(-4 : ℂ) * P * w ^ 2‖ := by
    rw [norm_mul, norm_mul, norm_pow, hw]
    have : ‖(-4 : ℂ)‖ = 4 := by simp
    rw [this]
    have := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith [sq_nonneg W]
  have hnum : ‖(χ + 4 * s) * w ^ 2 + 4 * s * (P - w ^ 2)‖ ≤ c1 * W ^ 2 + 4 * c2 * c3 := by
    calc _ ≤ ‖(χ + 4 * s) * w ^ 2‖ + ‖4 * s * (P - w ^ 2)‖ := norm_add_le _ _
      _ ≤ c1 * W ^ 2 + 4 * c2 * c3 := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, hw]
        have h4 : ‖(4 : ℂ)‖ = 4 := by simp
        rw [h4]
        have hc1 : 0 ≤ c1 := (norm_nonneg _).trans h1
        have hc2 : 0 ≤ c2 := (norm_nonneg _).trans h2
        have ha := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ W ^ 2)
        have hb : 4 * ‖s‖ * ‖P - w ^ 2‖ ≤ 4 * c2 * c3 :=
          mul_le_mul (by linarith) h3 (norm_nonneg _) (by positivity)
        linarith
  have hpos : 0 < 4 * p0 * W ^ 2 := by positivity
  calc ‖(χ + 4 * s) * w ^ 2 + 4 * s * (P - w ^ 2)‖ / ‖(-4 : ℂ) * P * w ^ 2‖
      ≤ (c1 * W ^ 2 + 4 * c2 * c3) / (4 * p0 * W ^ 2) :=
        div_le_div₀ (by nlinarith [norm_nonneg ((χ + 4 * s) * w ^ 2 + 4 * s * (P - w ^ 2))]) hnum hpos hden
    _ = c1 / (4 * p0) + c2 * c3 / (p0 * W ^ 2) := by
        field_simp

/-! ### Graph-route local versions of the exterior-factor lemmas (G1054_PROOF02).
Each lemma below is a copy of the corresponding production lemma of `TauGammaExterior`/`ProductReprConstruction`/`TauGammaDeviationBounds`
with its old-route summability premise (`periodic_plus_summable38`, `periodic_minus_summable38`, `periodic_l2_summable38`) replaced by an explicit hypothesis
(provided from G1-052 `periodic_l2G`) and `perChar_eq_periodicProduct38` replaced by G1-053 `perChar_eq_periodicProductG`. -/

section GraphRoute

open SummationFilter

theorem plus_sigmaG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) (n : ℤ) :
    Lib.sigmaOf (periodicPlusDeviation38 ψ) n = lamPlus ψ n := by
  unfold Lib.sigmaOf periodicPlusDeviation38
  rw [l2SequenceOf_apply38 _ hsP]
  ring

theorem minus_sigmaG (ψ : PotPair)
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) (n : ℤ) :
    Lib.sigmaOf (periodicMinusDeviation38 ψ) n = lamMinus ψ n := by
  unfold Lib.sigmaOf periodicMinusDeviation38
  rw [l2SequenceOf_apply38 _ hsM]
  ring

theorem excludedPairedFactors_eq_mulG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (z : ℂ) :
    excludedPairedFactors38 ψ n z = fun m =>
      Lib.omitFactor n (periodicPlusDeviation38 ψ) z m *
        Lib.omitFactor n (periodicMinusDeviation38 ψ) z m := by
  funext m
  by_cases hm : m = n
  · simp [excludedPairedFactors38, Lib.omitFactor, hm]
  · simp only [excludedPairedFactors38, Lib.omitFactor, hm, ite_false,
      pairedFactors_eq_mul38, Lib.prodFactor, plus_sigmaG ψ hsP, minus_sigmaG ψ hsM]

theorem exterior_multipliableG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (z : ℂ) :
    Multipliable (excludedPairedFactors38 ψ n z) (symmetricIcc ℤ) := by
  rw [excludedPairedFactors_eq_mulG ψ hsP hsM]
  exact (Lib.multipliable_omit n (periodicPlusDeviation38 ψ) z).mul
    (Lib.multipliable_omit n (periodicMinusDeviation38 ψ) z)

theorem exterior_eq_omitProductsG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (z : ℂ) :
    exteriorFactor38 ψ n z = Lib.omitProd n (periodicPlusDeviation38 ψ) z *
      Lib.omitProd n (periodicMinusDeviation38 ψ) z := by
  have hp := Lib.multipliable_omit n (periodicPlusDeviation38 ψ) z
  have hm := Lib.multipliable_omit n (periodicMinusDeviation38 ψ) z
  unfold exteriorFactor38
  rw [excludedPairedFactors_eq_mulG ψ hsP hsM]
  simp only [Lib.omitFactor]
  rw [hp.tprod_mul hm]
  unfold Lib.omitProd
  simp only [one_div]
  ring

theorem exterior_entireG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) (n : ℤ) :
    AnalyticOnNhd ℂ (exteriorFactor38 ψ n) univ := by
  have he : exteriorFactor38 ψ n = fun z =>
      Lib.omitProd n (periodicPlusDeviation38 ψ) z * Lib.omitProd n (periodicMinusDeviation38 ψ) z :=
    funext (exterior_eq_omitProductsG ψ hsP hsM n)
  rw [he]
  intro z _
  exact (Lib.analyticAt_omitProd_line n (periodicPlusDeviation38 ψ) z).mul
    (Lib.analyticAt_omitProd_line n (periodicMinusDeviation38 ψ) z)

theorem pairedProduct_eq_mulG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) (z : ℂ) :
    pairedProduct38 ψ z = singleProduct38 (lamPlus ψ) z * singleProduct38 (lamMinus ψ) z := by
  have hp := (Lib.product_entire (lamPlus ψ) hsP).1 z
  have hm := (Lib.product_entire (lamMinus ψ) hsM).1 z
  simpa only [pairedProduct38, singleProduct38, pairedFactors_eq_mul38] using hp.tprod_mul hm

theorem exterior_perChar_factorG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (z : ℂ) :
    perChar ψ z = -4 * (lamPlus ψ n - z) * (lamMinus ψ n - z) * exteriorFactor38 ψ n z := by
  have hp : singleProduct38 (lamPlus ψ) z =
      (lamPlus ψ n - z) * Lib.omitProd n (periodicPlusDeviation38 ψ) z := by
    simpa only [Lib.prodFactor, plus_sigmaG ψ hsP, singleProduct38] using
      Lib.entProd_eq_mul_omitProd n (periodicPlusDeviation38 ψ) z
  have hm : singleProduct38 (lamMinus ψ) z =
      (lamMinus ψ n - z) * Lib.omitProd n (periodicMinusDeviation38 ψ) z := by
    simpa only [Lib.prodFactor, minus_sigmaG ψ hsM, singleProduct38] using
      Lib.entProd_eq_mul_omitProd n (periodicMinusDeviation38 ψ) z
  rw [NlsGge.Atomic.G1053S3.perChar_eq_periodicProductG]
  change -4 * pairedProduct38 ψ z = _
  rw [pairedProduct_eq_mulG ψ hsP hsM, hp, hm, exterior_eq_omitProductsG ψ hsP hsM]
  ring

theorem exterior_inner_error_boundsG (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (z : ℂ)
    (hz : z ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8)) (b K : ℝ)
    (hb : ‖Lib.omitProd n (periodicPlusDeviation38 ψ) z * Lib.omitProd n (periodicMinusDeviation38 ψ) z -
      (Lib.sincAt n z) ^ 2‖ ≤ b ∧
      ‖deriv (fun w => Lib.omitProd n (periodicPlusDeviation38 ψ) w *
          Lib.omitProd n (periodicMinusDeviation38 ψ) w) z -
        deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ b)
    (hK : ‖(Lib.sincAt n z) ^ 2 - 1‖ ≤ K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ∧
      ‖deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖) :
    ‖exteriorFactor38 ψ n z - 1‖ ≤ b + K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ∧
      ‖deriv (exteriorFactor38 ψ n) z‖ ≤ b + K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
  have hval : ‖exteriorFactor38 ψ n z - (Lib.sincAt n z) ^ 2‖ ≤ b := by
    rw [exterior_eq_omitProductsG ψ hsP hsM]
    exact hb.1
  have heD : deriv (exteriorFactor38 ψ n) z = deriv (fun w =>
      Lib.omitProd n (periodicPlusDeviation38 ψ) w * Lib.omitProd n (periodicMinusDeviation38 ψ) w) z :=
    congrArg (fun f : ℂ → ℂ => deriv f z) (funext (exterior_eq_omitProductsG ψ hsP hsM n))
  have hder := hb.2
  rw [← heD] at hder
  constructor
  · have he : exteriorFactor38 ψ n z - 1 =
        (exteriorFactor38 ψ n z - (Lib.sincAt n z) ^ 2) + ((Lib.sincAt n z) ^ 2 - 1) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hval hK.1)
  · exact (norm_le_norm_sub_add (deriv (exteriorFactor38 ψ n) z)
      (deriv (fun w => (Lib.sincAt n w) ^ 2) z)).trans (add_le_add hder hK.2)

theorem dev_norms_localG (φ0 : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ φ ∈ U,
      Summable (fun n : ℤ => ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      ‖periodicPlusDeviation38 φ‖ ≤ K ∧ ‖periodicMinusDeviation38 φ‖ ≤ K := by
  obtain ⟨U, hU, B, hB, h⟩ := periodic_l2G φ0
  refine ⟨U, hU, B + 1, by positivity, fun φ hφ => ?_⟩
  have hsP : Summable (fun n : ℤ => ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
    (h φ hφ).1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => le_add_of_nonneg_left (sq_nonneg _))
  have hsM : Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
    (h φ hφ).1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => le_add_of_nonneg_right (sq_nonneg _))
  have hp : ‖periodicPlusDeviation38 φ‖ ^ 2 ≤ B := by
    rw [periodicPlusDeviation38, l2SequenceOf_norm_sq38 _ hsP]
    exact (hsP.tsum_le_tsum
      (fun n => le_add_of_nonneg_left (sq_nonneg _)) (h φ hφ).1).trans (h φ hφ).2
  have hm : ‖periodicMinusDeviation38 φ‖ ^ 2 ≤ B := by
    rw [periodicMinusDeviation38, l2SequenceOf_norm_sq38 _ hsM]
    exact (hsM.tsum_le_tsum
      (fun n => le_add_of_nonneg_right (sq_nonneg _)) (h φ hφ).1).trans (h φ hφ).2
  refine ⟨hsP, hsM, ?_, ?_⟩ <;> nlinarith [norm_nonneg (periodicPlusDeviation38 φ),
    norm_nonneg (periodicMinusDeviation38 φ), sq_nonneg B]

end GraphRoute


theorem ext_near_sinc (φ0 : PotPair) {η : ℝ} (hη : 0 < η) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ0 ∧ ∃ N : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, (N : ℤ) < |n| →
      ∀ z ∈ closedBall (countingCenter38 n) (Real.pi / 4),
        ‖exteriorFactor38 ψ n z - sincSquareProfile38 (z - countingCenter38 n)‖ ≤ η := by
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) (Real.pi / 4)).exists_bound_of_continuousOn
    Complex.continuous_sin.continuousOn
  set M1 : ℝ := max M0 1 with hM1def
  have hM1pos : 0 < M1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM1 : ∀ w : ℂ, ‖w‖ ≤ Real.pi / 4 → ‖Complex.sin w‖ ≤ M1 := fun w hw =>
    (hM0 w (by simpa using hw)).trans (le_max_left _ _)
  have hpi := Real.pi_pos
  set W : ℝ := Real.pi / 4 with hWdef
  have hWpos : 0 < W := by positivity
  set p0 : ℝ := (Real.pi / 8) ^ 2 with hp0def
  have hp0 : 0 < p0 := by positivity
  set r : ℝ := min (Real.pi / 8) (η * p0 * W / (6 * M1 ^ 2)) with hrdef
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hr8 : r ≤ Real.pi / 8 := min_le_left _ _
  have hr2 : r ≤ η * p0 * W / (6 * M1 ^ 2) := min_le_right _ _
  have hr4 : r ≤ Real.pi / 4 := by linarith
  set ε : ℝ := 2 * η * p0 / M1 ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨V1, hV1, N1, hV⟩ := roots_in_small_ball φ0 hr hr4
  obtain ⟨U1, hU1, R1, h1⟩ := perChar_asympG φ0 ε hε
  obtain ⟨UL, hUL, KL, hKL, hL⟩ := dev_norms_localG φ0
  obtain ⟨K, hK⟩ := exists_nat_gt ((R1 + Real.pi) / Real.pi)
  refine ⟨V1 ∩ (U1 ∩ UL), inter_mem hV1 (inter_mem hU1 hUL), max K N1, fun ψ hψ n hn z hz => ?_⟩
  obtain ⟨hψV, hψU, hψL⟩ := hψ
  have hsP := (hL ψ hψL).1
  have hsM := (hL ψ hψL).2.1
  have hnK : (K : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_left _ _) hn
  have hnN1 : (N1 : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_right _ _) hn
  obtain ⟨-, -, hP1, hM1', -⟩ := hV ψ hψV n hnN1
  have ha : ‖lamPlus ψ n - countingCenter38 n‖ < r := mem_ball_iff_norm.mp hP1
  have hb : ‖lamMinus ψ n - countingCenter38 n‖ < r := mem_ball_iff_norm.mp hM1'
  have hAn : AnalyticOnNhd ℂ (fun z => exteriorFactor38 ψ n z -
      sincSquareProfile38 (z - countingCenter38 n)) univ := fun z _ =>
    (exterior_entireG ψ hsP hsM n z (mem_univ _)).sub
      ((sincSquareProfile_entire38 _ (mem_univ _)).comp (analyticAt_id.sub analyticAt_const))
  refine bound_closedBall_of_sphere hAn (countingCenter38 n) hWpos (B := η) ?_ z hz
  intro z hz
  have hz' : ‖z - countingCenter38 n‖ = W := by simpa only [mem_sphere, dist_eq_norm] using hz
  set w : ℂ := z - countingCenter38 n with hw
  set a : ℂ := lamPlus ψ n - countingCenter38 n with ha_def
  set b : ℂ := lamMinus ψ n - countingCenter38 n with hb_def
  set P : ℂ := (lamPlus ψ n - z) * (lamMinus ψ n - z) with hP
  have hPe : P = (a - w) * (b - w) := by
    simp only [hP, ha_def, hb_def, hw]; ring
  have hlow1 : Real.pi / 8 ≤ ‖a - w‖ := by
    have h := norm_sub_norm_le w a
    rw [norm_sub_rev w a] at h
    linarith
  have hlow2 : Real.pi / 8 ≤ ‖b - w‖ := by
    have h := norm_sub_norm_le w b
    rw [norm_sub_rev w b] at h
    linarith
  have hPlow : p0 ≤ ‖P‖ := by
    rw [hPe, norm_mul, hp0def]
    nlinarith [hlow1, hlow2, hpi]
  have hPw : ‖P - w ^ 2‖ ≤ 3 * r * W := by
    have he : P - w ^ 2 = -(a + b) * w + a * b := by rw [hPe]; ring
    rw [he]
    calc ‖-(a + b) * w + a * b‖ ≤ ‖-(a + b) * w‖ + ‖a * b‖ := norm_add_le _ _
      _ ≤ 2 * r * W + r * W := by
        rw [norm_mul, norm_neg, norm_mul, hz']
        have hab : ‖a + b‖ ≤ 2 * r := by
          have := norm_add_le a b
          linarith
        have h1' := mul_le_mul hab le_rfl hWpos.le (by positivity)
        have h2' : ‖a‖ * ‖b‖ ≤ r * W := by
          have hbW : ‖b‖ ≤ W := by linarith
          exact mul_le_mul ha.le hbW (norm_nonneg _) hr.le
        linarith
      _ = 3 * r * W := by ring
  have hwne : z ≠ (n : ℂ) * (Real.pi : ℂ) := by
    intro h0
    have : ‖z - countingCenter38 n‖ = 0 := by rw [h0]; simp [countingCenter38]
    rw [hz'] at this
    linarith
  have hS : sincSquareProfile38 (z - countingCenter38 n) = Complex.sin z ^ 2 / w ^ 2 := by
    have := sincAt_square_translate38 n z
    change sincSquareProfile38 (z - (n : ℂ) * (Real.pi : ℂ)) = _
    rw [← this]
    simp [Lib.sincAt, hwne, div_pow, hw, countingCenter38]
  have hext : exteriorFactor38 ψ n z = perChar ψ z / (-4 * P) := by
    have hPne : P ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hp0 hPlow)
    have hf := exterior_perChar_factorG ψ hsP hsM n z
    rw [eq_div_iff (mul_ne_zero (by norm_num) hPne)]
    rw [hf, hP]
    ring
  rw [hS, hext]
  have hchi : ‖perChar ψ z + 4 * Complex.sin z ^ 2‖ ≤ ε * M1 ^ 2 := by
    have hh := h1 ψ hψU z (sphere_norm_gt hK hnK hz) (fun k => counting_small_sphere_separated38 n hz k)
    have he : perChar ψ z + 4 * Complex.sin z ^ 2 = perChar ψ z - (-4 * Complex.sin z ^ 2) := by ring
    rw [he]
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ hε.le)
    have hs : ‖Complex.sin z‖ ≤ M1 := by
      rw [norm_sin_translate n z]
      exact hM1 _ (show ‖w‖ ≤ W from hz'.le)
    exact pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hsb : ‖Complex.sin z ^ 2‖ ≤ M1 ^ 2 := by
    rw [norm_pow]
    have hs : ‖Complex.sin z‖ ≤ M1 := by
      rw [norm_sin_translate n z]
      exact hM1 _ (show ‖w‖ ≤ W from hz'.le)
    exact pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hE := E_bound (perChar ψ z) (Complex.sin z ^ 2) P w hp0 hPlow hWpos hz' hchi hsb hPw
  refine hE.trans ?_
  have t1 : ε * M1 ^ 2 / (4 * p0) = η / 2 := by
    simp only [hεdef]; field_simp; ring
  have t2 : M1 ^ 2 * (3 * r * W) / (p0 * W ^ 2) ≤ η / 2 := by
    have h6 : 3 * r * W * M1 ^ 2 ≤ 3 * (η * p0 * W / (6 * M1 ^ 2)) * W * M1 ^ 2 := by
      have := mul_le_mul_of_nonneg_right hr2 (by positivity : 0 ≤ 3 * W * M1 ^ 2)
      nlinarith [this]
    have h7 : 3 * (η * p0 * W / (6 * M1 ^ 2)) * W * M1 ^ 2 = η * p0 * W ^ 2 / 2 := by
      field_simp; ring
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h6, h7]
  linarith


theorem lamDot_eq_lamG (φ : PotPair) : lamDot φ = lamG φ := by
  obtain ⟨N, hN⟩ := exists_cutoffG φ
  rw [lamDot_eq_candidate38 φ hN, lamG_eq hN]

theorem hasDerivAt_perChar_factor (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (z0 : ℂ) :
    HasDerivAt (perChar ψ)
      ((-4 * ((-1) * (lamMinus ψ n - z0) + (lamPlus ψ n - z0) * (-1))) * exteriorFactor38 ψ n z0 +
        (-4 * ((lamPlus ψ n - z0) * (lamMinus ψ n - z0))) *
          deriv (exteriorFactor38 ψ n) z0) z0 := by
  have hfac : perChar ψ = fun z => -4 * ((lamPlus ψ n - z) * (lamMinus ψ n - z)) *
      exteriorFactor38 ψ n z := by
    funext z
    rw [exterior_perChar_factorG ψ hsP hsM n z]
    ring
  have hext_d : HasDerivAt (exteriorFactor38 ψ n) (deriv (exteriorFactor38 ψ n) z0) z0 :=
    ((exterior_entireG ψ hsP hsM n z0 (mem_univ _)).differentiableAt).hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => lamPlus ψ n - z) (-1) z0 := (hasDerivAt_id z0).const_sub _
  have h2 : HasDerivAt (fun z : ℂ => lamMinus ψ n - z) (-1) z0 := (hasDerivAt_id z0).const_sub _
  have hprod := ((h1.mul h2).const_mul (-4 : ℂ)).mul hext_d
  rw [hfac]
  convert hprod using 1

theorem hasDerivAt_perChar_sq (ψ : PotPair) (z0 : ℂ) :
    HasDerivAt (perChar ψ) (2 * NlsGge.GK38.discrim ψ z0 * deriv (NlsGge.GK38.discrim ψ) z0) z0 := by
  have hΔ : HasDerivAt (NlsGge.GK38.discrim ψ) (deriv (NlsGge.GK38.discrim ψ) z0) z0 :=
    ((analyticOnNhd_discrim_z ψ) z0 (mem_univ _)).differentiableAt.hasDerivAt
  have h := (hΔ.pow 2).sub_const 4
  have hfun : perChar ψ = fun z => NlsGge.GK38.discrim ψ z ^ 2 - 4 := funext (perChar_eq ψ)
  rw [hfun]
  convert h using 1
  simp

theorem critical_core (ψ : PotPair)
    (hsP : Summable (fun n : ℤ => ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (hsM : Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (n : ℤ) (r Mq : ℝ)
    (hΔ0 : deriv (NlsGge.GK38.discrim ψ) (lamDot ψ n) = 0)
    (hlam : lamDot ψ n ∈ ball (countingCenter38 n) r)
    (hP : lamPlus ψ n ∈ ball (countingCenter38 n) r)
    (hM : lamMinus ψ n ∈ ball (countingCenter38 n) r)
    (huniq : ∀ z1 ∈ ball (countingCenter38 n) (Real.pi / 4),
      ∀ z2 ∈ ball (countingCenter38 n) (Real.pi / 4),
        deriv (NlsGge.GK38.discrim ψ) z1 = 0 → deriv (NlsGge.GK38.discrim ψ) z2 = 0 → z1 = z2)
    (hr4 : r ≤ Real.pi / 4)
    (hq : ‖exteriorFactor38 ψ n (lamDot ψ n) - 1‖ ≤ 1 / 4)
    (hqp : ‖deriv (exteriorFactor38 ψ n) (lamDot ψ n)‖ ≤ Mq) (hrM : 2 * r * Mq ≤ 1 / 4) :
    lamDot ψ n - (lamPlus ψ n + lamMinus ψ n) / 2 =
      (lamPlus ψ n - lamMinus ψ n) ^ 2 *
        (deriv (exteriorFactor38 ψ n) (lamDot ψ n) /
          (4 * (2 * exteriorFactor38 ψ n (lamDot ψ n) +
            (lamDot ψ n - (lamPlus ψ n + lamMinus ψ n) / 2) *
              deriv (exteriorFactor38 ψ n) (lamDot ψ n)))) ∧
    ‖deriv (exteriorFactor38 ψ n) (lamDot ψ n) /
          (4 * (2 * exteriorFactor38 ψ n (lamDot ψ n) +
            (lamDot ψ n - (lamPlus ψ n + lamMinus ψ n) / 2) *
              deriv (exteriorFactor38 ψ n) (lamDot ψ n)))‖ ≤
      ‖deriv (exteriorFactor38 ψ n) (lamDot ψ n)‖ / 4 := by
  set a := lamPlus ψ n with ha
  set b := lamMinus ψ n with hb
  set z0 := lamDot ψ n with hz0
  set q := exteriorFactor38 ψ n z0 with hqdef
  set qp := deriv (exteriorFactor38 ψ n) z0 with hqpdef
  set d : ℂ := z0 - (a + b) / 2 with hd
  set g : ℂ := (a - b) ^ 2 with hg
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at hq
    linarith
  have hc : 2 * d * q + (d ^ 2 - g / 4) * qp = 0 := by
    have hu := (hasDerivAt_perChar_factor ψ hsP hsM n z0).unique (hasDerivAt_perChar_sq ψ z0)
    rw [hΔ0, mul_zero] at hu
    simp only [hqdef, hqpdef, hd, hg, ha, hb] at hu ⊢
    linear_combination (-1 / 4 : ℂ) * hu
  have hcollapsed : g = 0 → d = 0 := by
    intro hg0
    have hab : a = b := by
      have : a - b = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hg0
      exact sub_eq_zero.mp this
    have hu := (hasDerivAt_perChar_factor ψ hsP hsM n a).unique (hasDerivAt_perChar_sq ψ a)
    have hlhs : (-4 * ((-1) * (lamMinus ψ n - a) + (lamPlus ψ n - a) * (-1))) * exteriorFactor38 ψ n a +
        (-4 * ((lamPlus ψ n - a) * (lamMinus ψ n - a))) * deriv (exteriorFactor38 ψ n) a = 0 := by
      rw [← hb, ← ha, ← hab]
      ring
    rw [hlhs] at hu
    have hroot : perChar ψ a = 0 := (lamSeq_enumeration38 ψ).1 (2 * n + 1)
    have hΔa : NlsGge.GK38.discrim ψ a ≠ 0 := by
      intro h0
      have : perChar ψ a = -4 := by rw [perChar_eq, h0]; norm_num
      rw [hroot] at this
      norm_num at this
    have hΔd : deriv (NlsGge.GK38.discrim ψ) a = 0 := by
      have h2 : 2 * NlsGge.GK38.discrim ψ a * deriv (NlsGge.GK38.discrim ψ) a = 0 := hu.symm
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (by simpa using h3) hΔa
      · exact h3
    have hPball : a ∈ ball (countingCenter38 n) (Real.pi / 4) :=
      ball_subset_ball hr4 hP
    have hZball : z0 ∈ ball (countingCenter38 n) (Real.pi / 4) := ball_subset_ball hr4 hlam
    have heq := huniq a hPball z0 hZball hΔd hΔ0
    rw [hd, ← heq, ← hab]
    ring
  obtain ⟨hden, hdeq⟩ := critical_denominator_algebra38 d g q qp hqne hc hcollapsed
  -- size of d
  have hnd : ‖d‖ ≤ 2 * r := by
    have h1 : ‖z0 - countingCenter38 n‖ < r := mem_ball_iff_norm.mp hlam
    have h2 : ‖a - countingCenter38 n‖ < r := mem_ball_iff_norm.mp hP
    have h3 : ‖b - countingCenter38 n‖ < r := mem_ball_iff_norm.mp hM
    have he : d = (z0 - countingCenter38 n) - ((a - countingCenter38 n) + (b - countingCenter38 n)) / 2 := by
      rw [hd]; ring
    rw [he]
    calc _ ≤ ‖z0 - countingCenter38 n‖ + ‖((a - countingCenter38 n) + (b - countingCenter38 n)) / 2‖ :=
          norm_sub_le _ _
      _ ≤ r + r := by
        refine add_le_add h1.le ?_
        rw [norm_div]
        have := norm_add_le (a - countingCenter38 n) (b - countingCenter38 n)
        have h22 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h22]
        linarith
      _ = 2 * r := by ring
  have hqn : 3 / 4 ≤ ‖q‖ := by
    have h := norm_sub_norm_le 1 q
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hlow : 1 ≤ ‖2 * q + d * qp‖ := by
    have h1 : ‖(2 : ℂ) * q‖ - ‖d * qp‖ ≤ ‖2 * q + d * qp‖ := by
      have := norm_sub_norm_le (2 * q) (-(d * qp))
      rw [norm_neg, sub_neg_eq_add] at this
      exact this
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; simp
    have h3 : ‖d * qp‖ ≤ 1 / 4 := by
      rw [norm_mul]
      have := mul_le_mul hnd hqp (norm_nonneg _) ((norm_nonneg d).trans hnd)
      nlinarith [this, hrM]
    linarith
  refine ⟨hdeq, ?_⟩
  rw [norm_div, norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)


theorem G1054_main_core : ((
  ∀ φ0 : PotPair, ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ V ∈ nhds φ0, ∀ φ ∈ V, ∃ a : ℤ → ℂ,
    (∀ n : ℤ, (N : ℤ) ≤ |n| →
      lamDot φ n - (lamPlus φ n + lamMinus φ n) / 2 = (lamPlus φ n - lamMinus φ n) ^ 2 * a n) ∧
    (∀ F : Finset ℤ, (∀ n ∈ F, (N : ℤ) ≤ |n|) → ∑ n ∈ F, ‖a n‖ ^ 2 ≤ C)
  : Prop)) := by
  intro φ0
  obtain ⟨Ks, hKs, hSinc⟩ := sinc_square_inner_bound38
  obtain ⟨UK, hUK, K, hK0, hNorm⟩ := dev_norms_localG φ0
  obtain ⟨B, hB0, hPair⟩ := paired_omit_cauchy38 K hK0
  obtain ⟨Ud, hUd, D, hD0, hDev⟩ := critical_l2G φ0
  have hpi := Real.pi_pos
  set Mq : ℝ := B + 2 with hMq
  have hMqpos : 0 < Mq := by positivity
  set r : ℝ := min (Real.pi / 8) (min (1 / (8 * Ks)) (1 / (8 * Mq))) with hrdef
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hr8 : r ≤ Real.pi / 8 := min_le_left _ _
  have hrKs : r ≤ 1 / (8 * Ks) := (min_le_right _ _).trans (min_le_left _ _)
  have hrMq : r ≤ 1 / (8 * Mq) := (min_le_right _ _).trans (min_le_right _ _)
  have hr4 : r ≤ Real.pi / 4 := by linarith
  have hKsr : Ks * r ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_left hrKs hKs.le
    have h2 : Ks * (1 / (8 * Ks)) = 1 / 8 := by field_simp
    linarith
  have hrM : 2 * r * Mq ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right hrMq hMqpos.le
    have h2 : 1 / (8 * Mq) * Mq = 1 / 8 := by field_simp
    nlinarith
  obtain ⟨V1, hV1, N1, hV⟩ := roots_in_small_ball φ0 hr hr4
  obtain ⟨V2, hV2, N2, hE⟩ := ext_near_sinc φ0 (η := 1 / 8) (by norm_num)
  refine ⟨max N1 N2 + 1, (B + Ks ^ 2 * D) / 8 + 1, by positivity, V1 ∩ (V2 ∩ (UK ∩ Ud)),
    inter_mem hV1 (inter_mem hV2 (inter_mem hUK hUd)), fun ψ hψ => ?_⟩
  obtain ⟨hψ1, hψ2, hψK, hψd⟩ := hψ
  obtain ⟨b, hb, hbs, hbB⟩ := hPair (periodicPlusDeviation38 ψ) (periodicMinusDeviation38 ψ)
    (hNorm ψ hψK).2.2.1 (hNorm ψ hψK).2.2.2
  have hsP := (hNorm ψ hψK).1
  have hsM := (hNorm ψ hψK).2.1
  obtain ⟨hDs, hDt⟩ := hDev ψ hψd
  rw [← lamDot_eq_lamG ψ] at hDs hDt
  let A : ℤ → ℂ := fun n =>
    deriv (exteriorFactor38 ψ n) (lamDot ψ n) /
      (4 * (2 * exteriorFactor38 ψ n (lamDot ψ n) +
        (lamDot ψ n - (lamPlus ψ n + lamMinus ψ n) / 2) *
          deriv (exteriorFactor38 ψ n) (lamDot ψ n)))
  have bB : ∀ n : ℤ, b n ≤ B + 1 := by
    intro n
    have h1 : b n ^ 2 ≤ ∑' k : ℤ, b k ^ 2 := hbs.le_tsum n (fun j _ => sq_nonneg _)
    nlinarith [sq_nonneg (b n - 1), (hb n).1]
  have key : ∀ n : ℤ, ((max N1 N2 : ℕ) : ℤ) < |n| →
      lamDot ψ n - (lamPlus ψ n + lamMinus ψ n) / 2 = (lamPlus ψ n - lamMinus ψ n) ^ 2 * A n ∧
      ‖A n‖ ≤ (b n + Ks * ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖) / 4 := by
    intro n hn
    have hn1 : (N1 : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_left N1 N2) hn
    have hn2 : (N2 : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_right N1 N2) hn
    obtain ⟨-, hlam, hP, hM, huniq⟩ := hV ψ hψ1 n hn1
    have hΔ0 : deriv (NlsGge.GK38.discrim ψ) (lamDot ψ n) = 0 := (lamDot_enumeration38 ψ).1 n
    have hz8 : lamDot ψ n ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8) :=
      ball_subset_ball hr8 hlam
    have hz4 : lamDot ψ n ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) :=
      ball_subset_ball hr4 hlam
    have hzr : ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ < r := mem_ball_iff_norm.mp hlam
    have hext := hE ψ hψ2 n hn2 (lamDot ψ n)
      (ball_subset_closedBall (ball_subset_ball hr4 hlam))
    have hS := (hSinc n (lamDot ψ n) hz4).1
    rw [sincAt_square_translate38 n (lamDot ψ n)] at hS
    have hq : ‖exteriorFactor38 ψ n (lamDot ψ n) - 1‖ ≤ 1 / 4 := by
      have he : exteriorFactor38 ψ n (lamDot ψ n) - 1 =
          (exteriorFactor38 ψ n (lamDot ψ n) -
            sincSquareProfile38 (lamDot ψ n - countingCenter38 n)) +
          (sincSquareProfile38 (lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)) - 1) := by
        simp only [countingCenter38]; ring
      rw [he]
      refine (norm_add_le _ _).trans ?_
      have h3 : Ks * ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 8 := by
        have := mul_le_mul_of_nonneg_left hzr.le hKs.le
        linarith
      linarith
    have hbb := ((hb n).2 (lamDot ψ n) hz8)
    have herr := exterior_inner_error_boundsG ψ hsP hsM n (lamDot ψ n) hz8 (b n) Ks hbb
      (hSinc n (lamDot ψ n) hz4)
    have hqp : ‖deriv (exteriorFactor38 ψ n) (lamDot ψ n)‖ ≤ Mq := by
      refine herr.2.trans ?_
      have h3 : Ks * ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 8 := by
        have := mul_le_mul_of_nonneg_left hzr.le hKs.le
        linarith
      have := bB n
      rw [hMq]
      linarith
    obtain ⟨h1, h2⟩ := critical_core ψ hsP hsM n r Mq hΔ0 hlam hP hM huniq hr4 hq hqp hrM
    refine ⟨h1, h2.trans ?_⟩
    have := herr.2
    linarith
  refine ⟨fun n => if ((max N1 N2 : ℕ) : ℤ) < |n| then A n else 0, ?_, ?_⟩
  · intro n hn
    have hn' : ((max N1 N2 : ℕ) : ℤ) < |n| := by
      have : ((max N1 N2 + 1 : ℕ) : ℤ) ≤ |n| := hn
      push_cast at this ⊢
      omega
    simp only [if_pos hn']
    exact (key n hn').1
  · intro F hF
    have hterm : ∀ n ∈ F, ‖(if ((max N1 N2 : ℕ) : ℤ) < |n| then A n else 0)‖ ^ 2 ≤
        (b n ^ 2 + Ks ^ 2 * ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) / 8 := by
      intro n hnF
      have hn' : ((max N1 N2 : ℕ) : ℤ) < |n| := by
        have : ((max N1 N2 + 1 : ℕ) : ℤ) ≤ |n| := hF n hnF
        push_cast at this ⊢
        omega
      simp only [if_pos hn']
      have hk := (key n hn').2
      have hAn : 0 ≤ ‖A n‖ := norm_nonneg _
      have hsq := pow_le_pow_left₀ hAn hk 2
      refine hsq.trans ?_
      nlinarith [sq_nonneg (b n - Ks * ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖)]
    calc _ ≤ ∑ n ∈ F, (b n ^ 2 + Ks ^ 2 * ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) / 8 :=
          Finset.sum_le_sum hterm
      _ = ((∑ n ∈ F, b n ^ 2) + Ks ^ 2 * ∑ n ∈ F, ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) / 8 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (B + Ks ^ 2 * D) / 8 := by
          have h1 : ∑ n ∈ F, b n ^ 2 ≤ B := (hbs.sum_le_tsum F (fun _ _ => sq_nonneg _)).trans hbB
          have h2 : ∑ n ∈ F, ‖lamDot ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤ D :=
            (hDs.sum_le_tsum F (fun _ _ => sq_nonneg _)).trans hDt
          have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg Ks)
          linarith
      _ ≤ (B + Ks ^ 2 * D) / 8 + 1 := by linarith

end

end NlsGge.Atomic.G1054S3

namespace NlsGge.Atomic.G1054S3.Final

set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

theorem G1054_main : ((
  ∀ φ0 : PotPair, ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ V ∈ nhds φ0, ∀ φ ∈ V, ∃ a : ℤ → ℂ,
    (∀ n : ℤ, (N : ℤ) ≤ |n| →
      lamDot φ n - (lamPlus φ n + lamMinus φ n) / 2 = (lamPlus φ n - lamMinus φ n) ^ 2 * a n) ∧
    (∀ F : Finset ℤ, (∀ n ∈ F, (N : ℤ) ≤ |n|) → ∑ n ∈ F, ‖a n‖ ^ 2 ≤ C)
  : Prop)) := NlsGge.Atomic.G1054S3.G1054_main_core


end NlsGge.Atomic.G1054S3.Final
