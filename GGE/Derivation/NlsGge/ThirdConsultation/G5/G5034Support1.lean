import Mathlib
import NlsGge.GK38.Lib.EntireProductsCircle

/- G5-034 SUPPORT 1 (proof development, AUTHOR; not self-reviewed). Supporting module for G5-034, NOT the packet theorem.
   Generic tail estimates on the spectral circles ‖z‖ = Nπ + π/2 for root shifts t : ℤ → ℂ with ℓ² data:
   (a) the shifted roots σ_k = kπ + t_k avoid the circle for all large N (circle_tail_avoid);
   (b) the series Σ_k b_k/(σ_k - z) with b ∈ ℓ² is bounded uniformly on those circles (circle_tail_bound).
   Uses only landed GK38 Lib circle estimates: circDist, half_le_circDist, circDist_pos, pi_mul_dd_le,
   halfInvSq, summable_halfInvSq, halfInvSq_nonneg, summable_inv_circDist_sq, tsum_inv_circDist_sq_le.
   Hypotheses are only the root-shift identity, the uniform bound on the shifts and ℓ² summability.
   The packet (G5034.lean) instantiates σ, t, b with psiRootAt, p2Extend38 and the G5-033 coefficients. -/
set_option autoImplicit false

open Filter Topology
open NlsGge.GK38.Lib

namespace NlsGge.ThirdConsultation.G5034Support1
noncomputable section

/-- The norm of `k π` is `|k| π`, with `|k| = k.natAbs`. -/
theorem norm_intCast_mul_pi (k : ℤ) :
    ‖(k : ℂ) * (Real.pi : ℂ)‖ = (k.natAbs : ℝ) * Real.pi := by
  rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    abs_cast_eq]

/-- Only finitely many modes carry a shift of size at least `π/4`. -/
theorem tail_index_bound (t : ℤ → ℂ) (ht : Summable fun k : ℤ => ‖t k‖ ^ 2) :
    ∃ K : ℕ, ∀ k : ℤ, K < k.natAbs → ‖t k‖ < Real.pi / 4 := by
  have hpi4 : (0 : ℝ) < (Real.pi / 4) ^ 2 := by positivity
  have hev := ht.tendsto_cofinite_zero.eventually (gt_mem_nhds hpi4)
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨K, hK⟩ := (hev.image fun k : ℤ => k.natAbs).bddAbove
  refine ⟨K, fun k hk => ?_⟩
  have hsq : ‖t k‖ ^ 2 < (Real.pi / 4) ^ 2 := by
    by_contra h
    have hmem : k ∈ {x : ℤ | ¬ ‖t x‖ ^ 2 < (Real.pi / 4) ^ 2} := h
    have hle : k.natAbs ≤ K := hK (Set.mem_image_of_mem _ hmem)
    omega
  nlinarith [norm_nonneg (t k), Real.pi_pos]

/-- Lower bounds for the denominators on the circle `‖z‖ = Nπ + π/2` for all modes `k`:
a bounded-index mode has denominator at least `π/2`, and a tail mode has denominator at least
`(π/2) · circDist N k`. -/
theorem denominator_lower (σ t : ℤ → ℂ) (hσ : ∀ k, σ k = (k : ℂ) * (Real.pi : ℂ) + t k)
    (T : ℝ) (hT : ∀ k, ‖t k‖ ≤ T) (K : ℕ) (hK : ∀ k : ℤ, K < k.natAbs → ‖t k‖ < Real.pi / 4)
    (N : ℕ) (hN : (K : ℝ) * Real.pi + T ≤ (N : ℝ) * Real.pi)
    (z : ℂ) (hz : ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2) (k : ℤ) :
    (k.natAbs ≤ K → Real.pi / 2 ≤ ‖σ k - z‖) ∧
      (K < k.natAbs → Real.pi / 2 * circDist N k ≤ ‖σ k - z‖) := by
  have hpi := Real.pi_pos
  constructor
  · intro hk
    have hnorm : ‖(k : ℂ) * (Real.pi : ℂ)‖ ≤ (K : ℝ) * Real.pi := by
      rw [norm_intCast_mul_pi]
      have hk' : (k.natAbs : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk
      exact mul_le_mul_of_nonneg_right hk' hpi.le
    have hσn : ‖σ k‖ ≤ (K : ℝ) * Real.pi + T := by
      rw [hσ k]
      exact (norm_add_le _ _).trans (add_le_add hnorm (hT k))
    have h1 := norm_sub_norm_le z (σ k)
    rw [norm_sub_rev] at h1
    linarith
  · intro hk
    have hcd := circDist_pos N k
    have hhalf := half_le_circDist N k
    have htk := hK k hk
    have hpk := pi_mul_dd_le hz k
    have heq : (k : ℂ) * (Real.pi : ℂ) - z = (σ k - z) - t k := by
      rw [hσ k]; ring
    have htri : ‖(k : ℂ) * (Real.pi : ℂ) - z‖ ≤ ‖σ k - z‖ + ‖t k‖ := by
      rw [heq]; exact norm_sub_le _ _
    nlinarith [mul_le_mul_of_nonneg_left hhalf hpi.le]

/-- For a bounded-index mode, `(K + 1/2)² · (k + 1/2)⁻² ≥ 1`. -/
theorem one_le_sq_mul_halfInvSq (K : ℕ) (k : ℤ) (hk : k.natAbs ≤ K) :
    1 ≤ ((K : ℝ) + 1 / 2) ^ 2 * halfInvSq k := by
  have h1 : k ≤ (K : ℤ) := by omega
  have h2 : -(K : ℤ) ≤ k := by omega
  have h1' : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
  have h2' : -(K : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
  have hne : (k : ℝ) + 1 / 2 ≠ 0 := by
    intro h
    have h'' : ((2 * k + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    have h' : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h''
    omega
  have hpos : 0 < ((k : ℝ) + 1 / 2) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hle : ((k : ℝ) + 1 / 2) ^ 2 ≤ ((K : ℝ) + 1 / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1') (by linarith : (0 : ℝ) ≤ (K : ℝ) + k + 1)]
  unfold halfInvSq
  rw [mul_one_div, le_div_iff₀ hpos]
  linarith

/-- Pointwise inverse-square bound, uniform in the circle radius index `N`. -/
theorem inv_sq_majorant (σ t : ℤ → ℂ) (hσ : ∀ k, σ k = (k : ℂ) * (Real.pi : ℂ) + t k)
    (T : ℝ) (hT : ∀ k, ‖t k‖ ≤ T) (K : ℕ) (hK : ∀ k : ℤ, K < k.natAbs → ‖t k‖ < Real.pi / 4)
    (N : ℕ) (hN : (K : ℝ) * Real.pi + T ≤ (N : ℝ) * Real.pi)
    (z : ℂ) (hz : ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2) (k : ℤ) :
    1 / ‖σ k - z‖ ^ 2 ≤ (4 / Real.pi ^ 2) *
      (((K : ℝ) + 1 / 2) ^ 2 * halfInvSq k + 1 / circDist N k ^ 2) := by
  obtain ⟨h1, h2⟩ := denominator_lower σ t hσ T hT K hK N hN z hz k
  have hpi := Real.pi_pos
  have hH : 0 ≤ halfInvSq k := halfInvSq_nonneg k
  have hC : 0 ≤ 1 / circDist N k ^ 2 := by positivity
  have hA : 0 ≤ ((K : ℝ) + 1 / 2) ^ 2 * halfInvSq k := mul_nonneg (by positivity) hH
  have hc : (0 : ℝ) ≤ 4 / Real.pi ^ 2 := by positivity
  by_cases hk : k.natAbs ≤ K
  · have hD : Real.pi / 2 ≤ ‖σ k - z‖ := h1 hk
    have hsq : (Real.pi / 2) ^ 2 ≤ ‖σ k - z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hD 2
    have hinv : 1 / ‖σ k - z‖ ^ 2 ≤ 1 / (Real.pi / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hsq
    have hone := one_le_sq_mul_halfInvSq K k hk
    have heq : 1 / (Real.pi / 2) ^ 2 = (4 / Real.pi ^ 2) * 1 := by ring
    calc 1 / ‖σ k - z‖ ^ 2 ≤ 1 / (Real.pi / 2) ^ 2 := hinv
      _ = (4 / Real.pi ^ 2) * 1 := heq
      _ ≤ (4 / Real.pi ^ 2) * (((K : ℝ) + 1 / 2) ^ 2 * halfInvSq k + 1 / circDist N k ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
  · have hk' : K < k.natAbs := by omega
    have hD := h2 hk'
    have hcd := circDist_pos N k
    have hpos : 0 < Real.pi / 2 * circDist N k := mul_pos (by positivity) hcd
    have hsq : (Real.pi / 2 * circDist N k) ^ 2 ≤ ‖σ k - z‖ ^ 2 :=
      pow_le_pow_left₀ hpos.le hD 2
    have hinv : 1 / ‖σ k - z‖ ^ 2 ≤ 1 / (Real.pi / 2 * circDist N k) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hpos 2) hsq
    calc 1 / ‖σ k - z‖ ^ 2 ≤ 1 / (Real.pi / 2 * circDist N k) ^ 2 := hinv
      _ = (4 / Real.pi ^ 2) * (1 / circDist N k ^ 2) := by ring
      _ ≤ (4 / Real.pi ^ 2) * (((K : ℝ) + 1 / 2) ^ 2 * halfInvSq k + 1 / circDist N k ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hc

/-- Avoidance: for all large `N`, no shifted root `σ k` lies on the circle `‖z‖ = Nπ + π/2`. -/
theorem circle_tail_avoid (σ t : ℤ → ℂ) (hσ : ∀ k, σ k = (k : ℂ) * (Real.pi : ℂ) + t k)
    (T : ℝ) (hT : ∀ k, ‖t k‖ ≤ T) (ht : Summable fun k : ℤ => ‖t k‖ ^ 2) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ z : ℂ, ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2 →
      ∀ k : ℤ, z ≠ σ k := by
  obtain ⟨K, hK⟩ := tail_index_bound t ht
  have hT0 : 0 ≤ T := (norm_nonneg _).trans (hT 0)
  have hpi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨K + ⌈T / Real.pi⌉₊, fun N hN z hz k hzk => ?_⟩
  have hNK : (K : ℝ) + T / Real.pi ≤ (N : ℝ) := by
    have h1 : ((K + ⌈T / Real.pi⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 := Nat.le_ceil (T / Real.pi)
    push_cast at h1
    linarith
  have hNπ : (K : ℝ) * Real.pi + T ≤ (N : ℝ) * Real.pi := by
    have h := mul_le_mul_of_nonneg_right hNK hpi.le
    have hTπ : T / Real.pi * Real.pi = T := by field_simp
    nlinarith [h, hTπ]
  obtain ⟨h1, h2⟩ := denominator_lower σ t hσ T hT K hK N hNπ z hz k
  have hD : 0 < ‖σ k - z‖ := by
    by_cases hk : k.natAbs ≤ K
    · linarith [h1 hk]
    · have hcd := circDist_pos N k
      have hh := h2 (by omega)
      have hpos : 0 < Real.pi / 2 * circDist N k := mul_pos (by positivity) hcd
      linarith
  rw [← hzk, sub_self, norm_zero] at hD
  exact lt_irrefl _ hD

/-- Uniform bound: for all large `N` and every `z` on the circle, the ℓ² series
`Σ_k b_k/(σ_k - z)` has norm bounded by a constant independent of `N` and `z`. -/
theorem circle_tail_bound (σ t b : ℤ → ℂ) (hσ : ∀ k, σ k = (k : ℂ) * (Real.pi : ℂ) + t k)
    (T : ℝ) (hT : ∀ k, ‖t k‖ ≤ T) (ht : Summable fun k : ℤ => ‖t k‖ ^ 2)
    (hb : Summable fun k : ℤ => ‖b k‖ ^ 2) :
    ∃ N₁ : ℕ, ∃ B : ℝ, ∀ N : ℕ, N₁ ≤ N → ∀ z : ℂ, ‖z‖ = (N : ℝ) * Real.pi + Real.pi / 2 →
      ‖∑' k : ℤ, b k / (σ k - z)‖ ≤ B := by
  obtain ⟨K, hK⟩ := tail_index_bound t ht
  have hT0 : 0 ≤ T := (norm_nonneg _).trans (hT 0)
  have hpi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨K + ⌈T / Real.pi⌉₊, (1 / 2) * (∑' k : ℤ, ‖b k‖ ^ 2) +
      ((4 / Real.pi ^ 2) * ((K : ℝ) + 1 / 2) ^ 2 / 2) * (∑' k : ℤ, halfInvSq k) +
      ((4 / Real.pi ^ 2) / 2) * (2 * ∑' k : ℤ, halfInvSq k), fun N hN z hz => ?_⟩
  have hNK : (K : ℝ) + T / Real.pi ≤ (N : ℝ) := by
    have h1 : ((K + ⌈T / Real.pi⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 := Nat.le_ceil (T / Real.pi)
    push_cast at h1
    linarith
  have hNπ : (K : ℝ) * Real.pi + T ≤ (N : ℝ) * Real.pi := by
    have h := mul_le_mul_of_nonneg_right hNK hpi.le
    have hTπ : T / Real.pi * Real.pi = T := by field_simp
    nlinarith [h, hTπ]
  have hDpos : ∀ k : ℤ, 0 < ‖σ k - z‖ := by
    intro k
    obtain ⟨h1, h2⟩ := denominator_lower σ t hσ T hT K hK N hNπ z hz k
    have hpi2 : 0 < Real.pi / 2 := by positivity
    by_cases hk : k.natAbs ≤ K
    · linarith [h1 hk]
    · have hcd := circDist_pos N k
      have hh := h2 (by omega)
      have hpos : 0 < Real.pi / 2 * circDist N k := mul_pos hpi2 hcd
      linarith
  have hG := ((hb.hasSum.mul_left (1 / 2)).add
    (summable_halfInvSq.hasSum.mul_left ((4 / Real.pi ^ 2) * ((K : ℝ) + 1 / 2) ^ 2 / 2))).add
    ((summable_inv_circDist_sq N).hasSum.mul_left ((4 / Real.pi ^ 2) / 2))
  have hgle : ∀ k : ℤ, ‖b k / (σ k - z)‖ ≤ (1 / 2) * ‖b k‖ ^ 2 +
      (4 / Real.pi ^ 2) * ((K : ℝ) + 1 / 2) ^ 2 / 2 * halfInvSq k +
      (4 / Real.pi ^ 2) / 2 * (1 / circDist N k ^ 2) := by
    intro k
    have hm := inv_sq_majorant σ t hσ T hT K hK N hNπ z hz k
    have hD := hDpos k
    have hy : (1 / ‖σ k - z‖) ^ 2 = 1 / ‖σ k - z‖ ^ 2 := by ring
    have hAM : ‖b k‖ * (1 / ‖σ k - z‖) ≤
        (1 / 2) * ‖b k‖ ^ 2 + (1 / 2) * (1 / ‖σ k - z‖) ^ 2 := by
      nlinarith [sq_nonneg (‖b k‖ - 1 / ‖σ k - z‖)]
    have hdiv : ‖b k‖ / ‖σ k - z‖ = ‖b k‖ * (1 / ‖σ k - z‖) := by ring
    rw [norm_div, hdiv]
    nlinarith [hAM, hm, hy]
  refine le_trans (tsum_of_norm_bounded hG hgle) ?_
  have hS : ∑' m : ℤ, 1 / circDist N m ^ 2 ≤ 2 * ∑' k : ℤ, halfInvSq k :=
    tsum_inv_circDist_sq_le N
  have hc2 : 0 ≤ (4 / Real.pi ^ 2) / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS hc2]

end
end NlsGge.ThirdConsultation.G5034Support1
