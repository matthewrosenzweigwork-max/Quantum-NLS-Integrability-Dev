import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS031Analytic

/- KSPS-031 SHARP → LAURENT, PURE CORE (proof development, AUTHOR; not reviewed). Intended target
   NlsGge/ThirdConsultation/KSPS/KSPS031SharpLaurentCore.lean, namespace NlsGge.ThirdConsultation.KSPS031SL.
   Pure algebra for wiring `KSPS.nonresonant_WKB_coefficients_sharp` into `M016CL.coeff_match_littleO`
   (see M016LITTLEO_WIRING.md, steps 4–7):
   * sum_conv: Σ_{k<K+1} a_k (z⁻¹)^k = Σ_{k∈[1,K]} c_k/(2iz)^k for a_0 = 0, a_k = c_k/(2i)^k;
   * sharp_expr_eq: P + i(θ_N + i(2i)^{-(N+1)} c_{N+1} x^{-(N+1)}) = (P + ix) − Σ_{k<N+2} a_k (x⁻¹)^k,
     θ_N = x + i Σ_{k∈[1,N]} (2ix)^{-k} c_k (the literal wkbPhase body);
   * exterior_of_disc: the disc bound at w = 0 for the chart w ↦ (if w = 0 then 0 else G w⁻¹)
     gives, for every K ≤ m, ‖G z − Σ_{k∈[1,K]} c_k/(2iz)^k‖ ≤ C/‖z‖^(K+1) for ‖z‖ ≥ R;
   * halfNode_inv_seq: w_n = ((n+M)+1/2)π)⁻¹ is nonzero and tends to 0. -/
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS031SL
noncomputable section

/-- The coefficient sequence of the w-chart: a_0 = 0, a_k = c_k / (2i)^k. -/
theorem sum_conv (c : ℕ → ℂ) (K : ℕ) (z : ℂ) (hz : z ≠ 0) :
    ∑ k ∈ Finset.range (K + 1), (if k = 0 then 0 else c k / (2 * Complex.I) ^ k) * z⁻¹ ^ k =
      ∑ k ∈ Finset.Icc 1 K, c k / (2 * Complex.I * z) ^ k := by
  have h2I : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1),
      if_neg (Nat.succ_ne_zero K), mul_pow, inv_pow]
    congr 1
    field_simp
    ring

/-- The sharp head's expression is the w-chart residual. -/
theorem sharp_expr_eq (N : ℕ) (c : ℕ → ℂ) (x P : ℂ) (hx : x ≠ 0) :
    P + Complex.I * ((x + Complex.I * ∑ k ∈ Finset.Icc 1 N,
          (2 * Complex.I * x) ^ (-(k : ℤ)) * c k) +
        Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * c (N + 1) *
          x ^ (-((N + 1 : ℕ) : ℤ))) =
      (P + Complex.I * x) -
        ∑ k ∈ Finset.range (N + 1 + 1), (if k = 0 then 0 else c k / (2 * Complex.I) ^ k) * x⁻¹ ^ k := by
  rw [sum_conv c (N + 1) x hx, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  have hterm : ∀ k ∈ Finset.Icc 1 N, (2 * Complex.I * x) ^ (-(k : ℤ)) * c k =
      c k / (2 * Complex.I * x) ^ k := by
    intro k _
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  have hlast : Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * c (N + 1) *
      x ^ (-((N + 1 : ℕ) : ℤ)) = Complex.I * (c (N + 1) / (2 * Complex.I * x) ^ (N + 1)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow, div_eq_mul_inv, mul_inv]
    ring
  rw [hlast]
  linear_combination ((∑ k ∈ Finset.Icc 1 N, c k / (2 * Complex.I * x) ^ k) +
    c (N + 1) / (2 * Complex.I * x) ^ (N + 1)) * Complex.I_sq

/-- Exterior Laurent bounds, every order K ≤ m, from the disc bound of the w-chart. -/
theorem exterior_of_disc (G : ℂ → ℂ) (c : ℕ → ℂ) (m : ℕ) (C' r : ℝ) (hC' : 0 ≤ C') (hr : 0 < r)
    (hdisc : ∀ w : ℂ, ‖w‖ < r →
      ‖(if w = 0 then 0 else G w⁻¹) -
        ∑ k ∈ Finset.range (m + 1), (if k = 0 then 0 else c k / (2 * Complex.I) ^ k) * w ^ k‖ ≤
        C' * ‖w‖ ^ (m + 1)) :
    ∀ K : ℕ, K ≤ m → ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖G z - ∑ k ∈ Finset.Icc 1 K, c k / (2 * Complex.I * z) ^ k‖ ≤ C / ‖z‖ ^ (K + 1) := by
  intro K hK
  set a : ℕ → ℂ := fun k => if k = 0 then 0 else c k / (2 * Complex.I) ^ k with ha
  set A : ℝ := ∑ k ∈ Finset.range (m + 1), ‖a k‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C' + A, max 1 (2 / r), by linarith, lt_of_lt_of_le one_pos (le_max_left _ _),
    fun z hzR => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hzR
  have hz2 : 2 / r ≤ ‖z‖ := (le_max_right _ _).trans hzR
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hw0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hwn : ‖z⁻¹‖ = ‖z‖⁻¹ := norm_inv z
  have hwr : ‖z⁻¹‖ < r := by
    rw [hwn]
    have : 2 / r ≤ ‖z‖ := hz2
    rw [div_le_iff₀ hr] at this
    rw [inv_lt_comm₀ hzpos hr, ← one_div, div_lt_iff₀ hr]
    linarith
  have hd := hdisc z⁻¹ hwr
  rw [if_neg hw0, inv_inv] at hd
  -- split the sum at K+1
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => a k * z⁻¹ ^ k) (by omega : K + 1 ≤ m + 1)
  have hconv := sum_conv c K z hz0
  have htail : ‖∑ k ∈ Finset.Ico (K + 1) (m + 1), a k * z⁻¹ ^ k‖ ≤ A / ‖z‖ ^ (K + 1) := by
    calc ‖∑ k ∈ Finset.Ico (K + 1) (m + 1), a k * z⁻¹ ^ k‖
        ≤ ∑ k ∈ Finset.Ico (K + 1) (m + 1), ‖a k * z⁻¹ ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico (K + 1) (m + 1), ‖a k‖ / ‖z‖ ^ (K + 1) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : K + 1 ≤ k := (Finset.mem_Ico.1 hk).1
          rw [norm_mul, norm_pow, hwn, inv_pow, ← div_eq_mul_inv]
          apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          exact pow_le_pow_right₀ hz1 hk1
      _ ≤ ∑ k ∈ Finset.range (m + 1), ‖a k‖ / ‖z‖ ^ (K + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2)
            (fun _ _ _ => by positivity)
      _ = A / ‖z‖ ^ (K + 1) := by rw [hA, Finset.sum_div]
  have hmain : ‖G z - ∑ k ∈ Finset.range (m + 1), a k * z⁻¹ ^ k‖ ≤ C' / ‖z‖ ^ (K + 1) := by
    refine hd.trans ?_
    rw [hwn, inv_pow, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left hC' (by positivity)
    exact pow_le_pow_right₀ hz1 (by omega)
  have e : G z - ∑ k ∈ Finset.Icc 1 K, c k / (2 * Complex.I * z) ^ k =
      (G z - ∑ k ∈ Finset.range (m + 1), a k * z⁻¹ ^ k) +
        ∑ k ∈ Finset.Ico (K + 1) (m + 1), a k * z⁻¹ ^ k := by
    rw [← hconv, ← hsplit]
    ring
  rw [e]
  calc _ ≤ ‖G z - ∑ k ∈ Finset.range (m + 1), a k * z⁻¹ ^ k‖ +
        ‖∑ k ∈ Finset.Ico (K + 1) (m + 1), a k * z⁻¹ ^ k‖ := norm_add_le _ _
    _ ≤ C' / ‖z‖ ^ (K + 1) + A / ‖z‖ ^ (K + 1) := add_le_add hmain htail
    _ = (C' + A) / ‖z‖ ^ (K + 1) := by ring

/-- The inverted half-node sequence. -/
theorem halfNode_inv_seq (M : ℕ) :
    (∀ n : ℕ, ((((((n : ℤ) + (M : ℤ) : ℤ) : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ))⁻¹) ≠ 0) ∧
    Tendsto (fun n : ℕ => ((((((n : ℤ) + (M : ℤ) : ℤ) : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ))⁻¹))
      atTop (𝓝 0) := by
  refine ⟨fun n => inv_ne_zero (fun h => ?_), ?_⟩
  · have h1 := NlsGge.ThirdConsultation.KSPS031Analytic.one_le_norm_halfNode_expr ((n : ℤ) + M)
    rw [h, norm_zero] at h1
    norm_num at h1
  · refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat 1)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := NlsGge.ThirdConsultation.KSPS031Analytic.natAbs_le_norm_halfNode_expr ((n : ℤ) + M)
    have hab : (((n : ℤ) + (M : ℤ)).natAbs : ℝ) = (n : ℝ) + M := by
      have e : ((n : ℤ) + (M : ℤ)) = ((n + M : ℕ) : ℤ) := by push_cast; ring
      rw [e, Int.natAbs_natCast]
      push_cast
      ring
    rw [hab] at h1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hpos : 0 < (n : ℝ) := by linarith
    rw [norm_inv, inv_le_comm₀ (by linarith) (by positivity), one_div, inv_inv]
    linarith

end
end NlsGge.ThirdConsultation.KSPS031SL
