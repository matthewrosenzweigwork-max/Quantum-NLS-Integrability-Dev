import Mathlib
import NlsGge.Birkhoff.W09Approx38
import NlsGge.Birkhoff.W08Compact38

                                                                                           
                                                                          
                                                                                         
                                                                                           
                                                                                           

open NlsGge.Pilot NlsGge.Birkhoff Filter
open scoped Topology

namespace NlsGge.Atomic.R123

variable {lower upper : ℝ}

/-- R123.01: for n outside the symmetric window, |n| is at least N+1. -/
theorem abs_cast_ge_succ_of_not_mem (N : ℕ) (n : ℤ)
    (hn : n ∉ symmetricModes N) : (N : ℝ) + 1 ≤ |(n : ℝ)| := by
  have hz : (N : ℤ) + 1 ≤ |n| := by
    unfold symmetricModes at hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  rw [← Int.cast_abs]
  exact_mod_cast hz

/-- R123.02: sharpened scalar weight comparison outside the window. -/
theorem tail_weight_le (c : BoundedCoefficients lower upper)
    (s : ℝ) (N : ℕ) (n : ℤ) (hn : n ∉ symmetricModes N) :
    fullModeWeight c s n ≤
      (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 * fullModeWeight c (s - 1) n := by
  rw [fullModeWeight_pred38 c s n]
  have hsq : 1 + ((N : ℝ) + 1) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by
    have h1 := abs_cast_ge_succ_of_not_mem N n hn
    have h2 : ((N : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have h3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (N : ℝ) + 1) h1 2
      rwa [sq_abs] at h3
    linarith
  have hJ : (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 = (1 + ((N : ℝ) + 1) ^ 2)⁻¹ := by
    rw [inv_pow, japaneseBracket_sq38]
    norm_num
  have hinv : (1 + (n : ℝ) ^ 2)⁻¹ ≤ (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 := by
    rw [hJ]
    exact inv_anti₀ (by positivity) hsq
  have hw := fullModeWeight_pos c (s - 1) n
  calc fullModeWeight c (s - 1) n * (1 + (n : ℝ) ^ 2)⁻¹
      = (1 + (n : ℝ) ^ 2)⁻¹ * fullModeWeight c (s - 1) n := by ring
    _ ≤ (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 * fullModeWeight c (s - 1) n :=
        mul_le_mul_of_nonneg_right hinv hw.le

/-- R123.03: pointwise tail norm for the inclusion. -/
theorem inclusion_tail_apply_le (c : BoundedCoefficients lower upper)
    (s : ℝ) (N : ℕ) (y : ECarrier38 c (s - 1)) :
    ‖eInclCLM38 c (by linarith : s - 1 ≤ s) y -
      projE38 c s N (eInclCLM38 c (by linarith : s - 1 ≤ s) y)‖ ≤
      (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ * ‖y‖ := by
  have hJ0 : 0 ≤ (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ :=
    inv_nonneg.2 (japaneseBracket_pos _).le
  set a := eInclCLM38 c (by linarith : s - 1 ≤ s) y -
      projE38 c s N (eInclCLM38 c (by linarith : s - 1 ≤ s) y) with ha
  have hcoe : ∀ n, eCoe38 c s a n =
      if n ∈ symmetricModes N then 0 else eCoe38 c (s - 1) y n := by
    intro n
    have e1 : eCoe38 c s a n = eCoe38 c s (eInclCLM38 c (by linarith : s - 1 ≤ s) y) n -
        eCoe38 c s (projE38 c s N (eInclCLM38 c (by linarith : s - 1 ≤ s) y)) n := rfl
    rw [e1, eCoe38_projE38, eCoe38_eInclCLM38]
    split_ifs <;> simp
  have hsy : Summable fun n : ℤ => fullModeWeight c (s - 1) n * ‖eCoe38 c (s - 1) y n‖ ^ 2 :=
    (mem_seqE38_iff c (s - 1) _).1 (eCoe38_mem c (s - 1) y)
  have hsa : Summable fun n : ℤ => fullModeWeight c s n * ‖eCoe38 c s a n‖ ^ 2 :=
    (mem_seqE38_iff c s _).1 (eCoe38_mem c s a)
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hJ0 (norm_nonneg _))).1 ?_
  rw [norm_sq_eCarrier38, mul_pow, norm_sq_eCarrier38 c (s - 1) y]
  have hsum : Summable fun n : ℤ => (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 *
      (fullModeWeight c (s - 1) n * ‖eCoe38 c (s - 1) y n‖ ^ 2) := hsy.mul_left _
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) hsa hsum
  rw [hcoe n]
  split_ifs with hn
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (fullModeWeight_pos c _ n).le (sq_nonneg _))
  · calc fullModeWeight c s n * ‖eCoe38 c (s - 1) y n‖ ^ 2
        ≤ ((japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 * fullModeWeight c (s - 1) n) *
            ‖eCoe38 c (s - 1) y n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (tail_weight_le c s N n hn) (sq_nonneg _)
      _ = (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ ^ 2 *
            (fullModeWeight c (s - 1) n * ‖eCoe38 c (s - 1) y n‖ ^ 2) := by ring

/-- R123.04: operator-norm form of the sharpened tail estimate. -/
theorem inclusion_tail_opNorm_le (c : BoundedCoefficients lower upper)
    (s : ℝ) (N : ℕ) :
    ‖eInclCLM38 c (by linarith : s - 1 ≤ s) -
      (projE38 c s N).comp (eInclCLM38 c (by linarith : s - 1 ≤ s))‖ ≤
      (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.2 (japaneseBracket_pos _).le) (fun y => ?_)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  exact inclusion_tail_apply_le c s N y

/-- R123.05: the range of the head projection is finite dimensional. -/
theorem finiteDimensional_range_projE (c : BoundedCoefficients lower upper)
    (s : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (projE38 c s N).toLinearMap) := by
  let g : ECarrier38 c s →ₗ[ℝ] (↥(symmetricModes N) → ℂ) :=
    { toFun := fun x n => eCoe38 c s x n
      map_add' := fun x y => rfl
      map_smul' := fun a x => by
        funext n
        simp [eSmul_apply38, Complex.real_smul] }
  refine Module.Finite.of_injective (g.domRestrict (LinearMap.range (projE38 c s N).toLinearMap)) ?_
  intro x y hxy
  apply Subtype.ext
  apply eExt38 c s
  funext n
  obtain ⟨x', hx'⟩ := x.2
  obtain ⟨y', hy'⟩ := y.2
  by_cases hn : n ∈ symmetricModes N
  · exact congrFun hxy ⟨n, hn⟩
  · have e1 : eCoe38 c s x.1 n = 0 := by
      rw [← hx']
      show eCoe38 c s (projE38 c s N x') n = 0
      rw [eCoe38_projE38, if_neg hn]
    have e2 : eCoe38 c s y.1 n = 0 := by
      rw [← hy']
      show eCoe38 c s (projE38 c s N y') n = 0
      rw [eCoe38_projE38, if_neg hn]
    rw [e1, e2]

/-- R123.06: the heads converge in operator norm (accepted unshifted tail bound). -/
theorem inclusion_heads_tendsto (c : BoundedCoefficients lower upper) (s : ℝ) :
    Tendsto (fun N : ℕ => (projE38 c s N).comp
      (eInclCLM38 c (by linarith : s - 1 ≤ s))) atTop
      (𝓝 (eInclCLM38 c (by linarith : s - 1 ≤ s))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) tendsto_tailFactor38
  rw [norm_sub_rev]
  exact norm_tail_eIncl_le38 c s N

/-- R123.07: main assembly (design statement `weightedInclusion_tail_and_compact`). -/
theorem weightedInclusion_tail_and_compact
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    let j := eInclCLM38 c (by linarith : s - 1 ≤ s)
    (∀ N : ℕ, ‖j - (projE38 c s N).comp j‖ ≤
      (japaneseBracket ((N + 1 : ℕ) : ℤ))⁻¹) ∧
    Tendsto (fun N : ℕ => (projE38 c s N).comp j) atTop (𝓝 j) ∧
    IsCompactOperator j := by
  intro j
  refine ⟨fun N => inclusion_tail_opNorm_le c s N, inclusion_heads_tendsto c s, ?_⟩
  refine isCompactOperator_of_tendsto (inclusion_heads_tendsto c s)
    (Eventually.of_forall (fun N => ?_))
  have := finiteDimensional_range_projE c s N
  let g : ECarrier38 c (s - 1) →L[ℝ] LinearMap.range (projE38 c s N).toLinearMap :=
    ((projE38 c s N).comp j).codRestrict (LinearMap.range (projE38 c s N).toLinearMap)
      (fun y => ⟨j y, rfl⟩)
  have h1 : IsCompactOperator (LinearMap.range (projE38 c s N).toLinearMap).subtypeL :=
    isCompactOperator_of_locallyCompactSpace_rng _
  exact h1.comp_clm g

end NlsGge.Atomic.R123
