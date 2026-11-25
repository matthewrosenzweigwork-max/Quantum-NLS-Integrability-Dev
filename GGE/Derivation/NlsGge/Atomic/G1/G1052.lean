import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.G1.G1040
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraProbe
import NlsGge.Atomic.G2.G2005
import NlsGge.Atomic.G2.G2006
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.GK38.Lib.EntireProductsGrowth
import NlsGge.GK38.Lib.EntireProductsCircle
import NlsGge.GK38.ProductReprRatio
import NlsGge.GK38.PeriodicAsymptotics
import NlsGge.GK38.PeriodicLabellingFreeLabels
import NlsGge.Atomic.G1.G1050

/- G1-052 production: the G1-050 private copy (G1050S2 namespace tree, verbatim) of the reviewed candidate is replaced by `import NlsGge.Atomic.G1.G1050`. -/



/-! ============================================================================
G1-052 COMMAND01 graph-route proof (proof development, AUTHOR; not self-reviewed).  Imported (`NlsGge.Atomic.G1.G1050`, namespace G1050S2): proof development's G1050_PROOF_T2 (K47 = G1-047 with its G1-017 kit,
K20 = G1-020 with the G1-019 copy K20.K19, K10 = G2-010, the G1-050 critical infrastructure `critical_asymp`, `critical_roots_sine_l2G`, `product_growthG`).
Route (GK Prop 6.7, as the accepted production proof `periodic_l2_summable38` but with the asymptotic inputs swapped for the graph route):
  perChar_asymp (off-disc comparison)    -> `perChar_asympG`   from K47.G1047_whole,
  discrimDeriv_asymp (off-disc)          -> `critical_asymp`   from K47.G1047_whole (G1050 copy),
  fundPair_seq_l2 (at t = 1)             -> `perChar_roots_sine_l2G` from K20.K19.G1019_whole,
  simultaneous_counting_lemma38          -> `simultaneous_counting_lemmaG`, labelling_local_bounds38 -> `labelling_local_boundsG`,
  spectral_local_l2_38 (periodic part)   -> `periodic_l2G`.
KEPT production infrastructure (no asymptotic input): the counting strict-comparison/Rouche lemmas, the label cutoff invariance, `localized_sine_l2_38`,
`perChar_zero_sine_le38`.
============================================================================ -/

namespace NlsGge.Atomic.G1052S3

open Filter Topology SummationFilter Set Metric NlsGge.GK38 NlsGge.Atomic.Volterra NlsGge.SpectralFoundations NlsGge.Pilot
open NlsGge.Atomic.G1050S2
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem bridge1 (φ : PotPair) (z : ℂ) :
    (∑' m : ℕ, potentialVolterraTerm38 φ z m 1) = monodromyPair φ z :=
  NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one ⟨zero_le_one, le_rfl⟩

theorem perChar_asympG (φ₀ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R < ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ε * ‖Complex.sin z‖ ^ 2 := by
  obtain ⟨U, hU, Λ, h⟩ := K47.G1047_whole φ₀ (ε / 4) (by positivity)
  refine ⟨U, hU, Λ, fun φ hφ z hz hsep => ?_⟩
  have hsep' : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := hsep
  obtain ⟨-, h2, -⟩ := h φ hφ z hz hsep'
  have hs : Complex.sin z ≠ 0 := counting_sin_ne_zero38 hsep
  have h2' : ‖(discrim φ z ^ 2 - 4) / (-4 * Complex.sin z ^ 2) - 1‖ ≤ ε / 4 := h2
  have hne : (-4 : ℂ) * Complex.sin z ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  have e : perChar φ z - (-4 * Complex.sin z ^ 2) =
      ((discrim φ z ^ 2 - 4) / (-4 * Complex.sin z ^ 2) - 1) * (-4 * Complex.sin z ^ 2) := by
    change discrim φ z ^ 2 - 4 - (-4 * Complex.sin z ^ 2) = _
    field_simp
    ring
  rw [e, norm_mul]
  have hn : ‖(-4 : ℂ) * Complex.sin z ^ 2‖ = 4 * ‖Complex.sin z‖ ^ 2 := by
    rw [norm_mul, norm_pow]; simp
  rw [hn]
  have := mul_le_mul_of_nonneg_right h2' (by positivity : (0 : ℝ) ≤ 4 * ‖Complex.sin z‖ ^ 2)
  calc _ ≤ ε / 4 * (4 * ‖Complex.sin z‖ ^ 2) := this
    _ = ε * ‖Complex.sin z‖ ^ 2 := by ring

theorem simultaneous_counting_lemmaG (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ,
      ∀ φ : PotPair, φ ∈ U →
        RootCountingAt38 (perChar φ) 2 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N := by
  obtain ⟨U₁, hU₁, R₁, herr₁⟩ := perChar_asympG φ₀ 1 one_pos
  obtain ⟨U₂, hU₂, R₂, herr₂⟩ := critical_asymp φ₀ (1 / 4) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (max R₁ R₂ / Real.pi)
  let N : ℕ := K + 1
  have hN : 0 < N := Nat.succ_pos K
  have hRN : max R₁ R₂ < countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, N, fun φ hφ => ?_⟩
  have hcmp₁ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
    intro z hz hsep
    apply counting_strict_comparison38
    · simpa only [one_mul] using herr₁ φ hφ.1 z (lt_of_lt_of_le ((le_max_left _ _).trans_lt hRN) hz) hsep
    · exact hsep
  have hcmp₂ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖deriv (discrim φ) z - deriv (NlsGge.GK38.discrim 0) z‖ < ‖deriv (NlsGge.GK38.discrim 0) z‖ := by
    intro z hz hsep
    have hs : Complex.sin z ≠ 0 := counting_sin_ne_zero38 hsep
    have h := herr₂ φ hφ.2 z (lt_of_lt_of_le ((le_max_right _ _).trans_lt hRN) hz) hsep
    have hpos : 0 < ‖(-2 : ℂ) * Complex.sin z‖ :=
      norm_pos_iff.mpr (mul_ne_zero (by norm_num) hs)
    rw [discrimDeriv_zero38]
    calc ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤ (1 / 4) * ‖(-2 : ℂ) * Complex.sin z‖ := h
      _ < ‖(-2 : ℂ) * Complex.sin z‖ := by linarith
  have hsphere := counting_radius_mem_sphere38 N
  have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
  have hsep := counting_central_sphere_separated38 N hsphere
  obtain ⟨hs₁, hc₁, he₁⟩ := periodic_counting_at38 φ N hcmp₁
  obtain ⟨hs₂, hc₂, he₂⟩ := critical_counting_at38 φ N hcmp₂
  constructor
  · refine ⟨hN, analyticOnNhd_perChar_z φ,
      ⟨_, counting_ne_zero_of_comparison38 (hcmp₁ _ hnorm hsep)⟩,
      counting_zeroMult_support_finite38 φ, hs₁, ?_, he₁⟩
    omega
  · refine ⟨hN, analyticOnNhd_discrimDeriv38 φ,
      ⟨_, critical_ne_zero_of_comparison38 (hcmp₂ _ hnorm hsep)⟩,
      critical_zeroMult_support_finite38 φ, hs₂, ?_, he₂⟩
    simpa only [one_mul] using hc₂


open scoped Matrix.Norms.Elementwise in
theorem elem_le_of (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 ≤ r) (h : ∀ i j, ‖A i j‖ ≤ r) :
    @norm (Matrix (Fin 2) (Fin 2) ℂ) Matrix.normedAddCommGroup.toNorm A ≤ r :=
  (Matrix.norm_le_iff hr).2 h

theorem perChar_roots_sine_l2G (R c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      (∀ n : ℤ, perChar φ (υ n) = 0) →
      Summable (fun n : ℤ => ‖Complex.sin (υ n)‖ ^ 2) ∧
        (∑' n : ℤ, ‖Complex.sin (υ n)‖ ^ 2) ≤ C := by
  obtain ⟨C0, hC⟩ := K20.K19.G1019_whole (2 * |R|) c
  let A : ℝ := Real.exp c * (Real.exp c + 1)
  refine ⟨A ^ 2 * max C0 0, by positivity, fun φ hφ υ hshift hroot => ?_⟩
  have hR : Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ 2 * |R| := by
    have h1 : ‖φ.1‖ ≤ |R| := (norm_fst_le φ).trans (hφ.trans (le_abs_self _))
    have h2 : ‖φ.2‖ ≤ |R| := (norm_snd_le φ).trans (hφ.trans (le_abs_self _))
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg φ.1, norm_nonneg φ.2, abs_nonneg R]
  obtain ⟨hs, ht⟩ := hC φ υ hR hshift 1 zero_le_one le_rfl
  have hpoint (n : ℤ) : ‖Complex.sin (υ n)‖ ^ 2 ≤
      A ^ 2 * ‖(∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) - freeZsFundamentalComplex (υ n) 1‖ ^ 2 := by
    have him : |(υ n).im| ≤ c := by
      have he : (υ n - (n : ℂ) * (Real.pi : ℂ)).im = (υ n).im := by simp
      rw [← he]
      exact (Complex.abs_im_le_norm _).trans (hshift n)
    have h := perChar_zero_sine_le38 φ (υ n) c hc him (hroot n)
    have hD : fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ - freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩ =
        (∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) - freeZsFundamentalComplex (υ n) 1 := by
      rw [bridge1, ← freeE_eq]
      rfl
    rw [hD] at h
    have hel := elem_le_of ((∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) - freeZsFundamentalComplex (υ n) 1)
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) - freeZsFundamentalComplex (υ n) 1‖
      (norm_nonneg _) (fun i j => K47.entry_le_l2 _ i j)
    have h3 : ‖Complex.sin (υ n)‖ ≤ A * ‖(∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) -
        freeZsFundamentalComplex (υ n) 1‖ :=
      h.trans (mul_le_mul_of_nonneg_left hel (by positivity))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hfin (T : Finset ℤ) : ∑ n ∈ T, ‖Complex.sin (υ n)‖ ^ 2 ≤ A ^ 2 * max C0 0 := by
    calc _ ≤ ∑ n ∈ T, A ^ 2 * ‖(∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) -
          freeZsFundamentalComplex (υ n) 1‖ ^ 2 := Finset.sum_le_sum (fun n _ => hpoint n)
      _ = A ^ 2 * (∑ n ∈ T, ‖(∑' m : ℕ, potentialVolterraTerm38 φ (υ n) m 1) -
          freeZsFundamentalComplex (υ n) 1‖ ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((hs.sum_le_tsum T (fun n _ => sq_nonneg _)).trans (ht.trans (le_max_left _ _))) (by positivity)
  have hsm := summable_of_sum_le (fun n : ℤ => sq_nonneg ‖Complex.sin (υ n)‖) hfin
  exact ⟨hsm, hsm.tsum_le_of_sum_le hfin⟩

theorem labelling_local_boundsG (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
    ∀ φ : PotPair, φ ∈ U →
      (∀ n : ℤ,
        ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4) ∧
      (∀ n : ℤ, (N : ℤ) < |n| →
        ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 ∧
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
  obtain ⟨U, hU, N, hN⟩ := simultaneous_counting_lemmaG φ₀
  refine ⟨U, hU, N, (hN φ₀ (mem_of_mem_nhds hU)).1.1, fun φ hφ => ?_⟩
  obtain ⟨hp, hd⟩ := hN φ hφ
  have hm (n : ℤ) := periodicCandidate_shift_bound38 hp (2 * n)
  have hp' (n : ℤ) := periodicCandidate_shift_bound38 hp (2 * n + 1)
  have heP := lamSeq_eq_candidate38 φ hp
  have hminus (n : ℤ) :
      ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| → ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
    simpa only [lamMinus, heP, (periodic_index_pair38 n).1, countingCenter38] using hm n
  have hplus (n : ℤ) :
      ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| → ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
    simpa only [lamPlus, heP, (periodic_index_pair38 n).2.1, countingCenter38] using hp' n
  exact ⟨fun n => ⟨(hminus n).1, (hplus n).1⟩, fun n hn => ⟨(hminus n).2 hn, (hplus n).2 hn⟩⟩

theorem periodic_l2G (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, (‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ≤ C := by
  obtain ⟨U, hU, N, _hN, hloc⟩ := labelling_local_boundsG φ₀
  let b : ℝ := 2 * (N : ℝ) * Real.pi + Real.pi / 4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let R : ℝ := ‖φ₀‖ + 1
  obtain ⟨Cp, hCp, hp⟩ := perChar_roots_sine_l2G R b hb
  let T : ℝ := ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * b ^ 2
  let K : ℝ := Real.pi / 2 + 1
  let Bp : ℝ := T + K ^ 2 * Cp
  have hBp : 0 ≤ Bp := by dsimp [Bp, T]; positivity
  refine ⟨U ∩ ball φ₀ 1, inter_mem hU (ball_mem_nhds φ₀ zero_lt_one), 2 * Bp, by positivity, fun φ hφ => ?_⟩
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
  obtain ⟨hsM, htM⟩ := hp φ hR (lamMinus φ) (fun n => (hshift n).1) hmRoot
  obtain ⟨hsP, htP⟩ := hp φ hR (lamPlus φ) (fun n => (hshift n).2) hpRoot
  have hm := localized_sine_l2_38 (lamMinus φ) N b Cp hb hCp
    (fun n => (hshift n).1) (fun n hn => ((hfar n hn).1).le) hsM htM
  have hp' := localized_sine_l2_38 (lamPlus φ) N b Cp hb hCp
    (fun n => (hshift n).2) (fun n hn => ((hfar n hn).2).le) hsP htP
  refine ⟨hm.1.add hp'.1, ?_⟩
  rw [hm.1.tsum_add hp'.1]
  have hh := add_le_add hm.2 hp'.2
  change _ ≤ Bp + Bp at hh
  linarith

theorem G1052_main :
((
  (∀ φ₀ : PotPair, ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, ∀ ψ ∈ V,
    Summable (fun n : ℤ => ‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 + ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
    (∑' n : ℤ, (‖lamMinus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 + ‖lamPlus ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ≤ C) ∧
  (∀ n : ℤ, lamMinus (0 : PotPair) n = (n : ℂ) * (Real.pi : ℂ) ∧ lamPlus (0 : PotPair) n = (n : ℂ) * (Real.pi : ℂ))
  : Prop)) := by
  refine ⟨fun φ₀ => ?_, fun n => ?_⟩
  · obtain ⟨U, hU, C, -, h⟩ := periodic_l2G φ₀
    exact ⟨U, hU, C, h⟩
  · exact ⟨by rw [lamMinus_zero38]; rfl, by rw [lamPlus_zero38]; rfl⟩

end

end NlsGge.Atomic.G1052S3
