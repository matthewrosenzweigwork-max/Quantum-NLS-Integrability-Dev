import NlsGge.Weights.ReservedTail
/-! Scalar weights-only core of F:lem:coercivity (v2 §12.1), spec W-F06b. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

/-- Target 1: at `r = H^(1/4)` the weight term is `β_j (√H)^j`. -/
lemma weightTerm_quarter38 (c : ℕ → ℝ) (H : ℝ) (hH : 0 ≤ H) (j : ℕ) :
    weightTerm c (H^(1/4 : ℝ)) j = coefficient c j * (Real.sqrt H)^j := by
  unfold weightTerm
  congr 1
  rw [← Real.rpow_mul_natCast hH, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hH]
  congr 1
  push_cast
  ring

/-- Target 2: the reserved tail `Σ_{j≥2} β_j (√H)^j` has sum `W(H^(1/4)) - β₀ - β₁√H`. -/
lemma reserved_tail_hasSum38 (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (H : ℝ) (hH : 0 ≤ H) :
    HasSum (fun j : ℕ => coefficient c (j+2) * (Real.sqrt H)^(j+2))
      (weight c (H^(1/4 : ℝ)) - coefficient c 0 - coefficient c 1 * Real.sqrt H) := by
  have h := weight_tail_hasSum lower upper c hlower hbound hupper (H^(1/4 : ℝ))
  have hq : ∀ j : ℕ, weightTerm c (H^(1/4 : ℝ)) (j+2) =
      coefficient c (j+2) * (Real.sqrt H)^(j+2) := fun j => weightTerm_quarter38 c H hH (j+2)
  have e : coefficient c 1 * (H^(1/4 : ℝ))^2 = coefficient c 1 * Real.sqrt H := by
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hH]
    congr 1
    norm_num
  rw [e] at h
  simpa only [hq] using h

/-- Target 3: `β_{j+1} ≤ (up/lo) β_j`. -/
lemma coefficient_succ_le38 (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (j : ℕ) :
    coefficient c (j+1) ≤ (upper/lower) * coefficient c j := by
  unfold coefficient
  have hf : (0 : ℝ) < (Nat.factorial j : ℝ) ^ 4 := by positivity
  have hf1 : (Nat.factorial j : ℝ) ^ 4 ≤ (Nat.factorial (j+1) : ℝ) ^ 4 := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hcj : c (j+1) ≤ (upper/lower) * c j := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlower]
    nlinarith [hupper (j+1), hbound j, hlower, hbound (j+1), mul_le_mul_of_nonneg_right (hbound j) (le_trans hlower.le (hbound (j+1))) ]
  have hc1 : 0 ≤ c (j+1) := hlower.le.trans (hbound _)
  have hu : 0 ≤ upper/lower * c j := mul_nonneg (div_nonneg ((hlower.trans_le (hbound 0)).le.trans (hupper 0)) hlower.le) (hlower.le.trans (hbound _))
  calc c (j+1) / (Nat.factorial (j+1) : ℝ)^4 ≤ c (j+1) / (Nat.factorial j : ℝ)^4 :=
        div_le_div_of_nonneg_left hc1 hf hf1
    _ ≤ (upper/lower * c j) / (Nat.factorial j : ℝ)^4 :=
        div_le_div_of_nonneg_right hcj hf.le
    _ = _ := by ring

/-- Target 4: scalar coercivity of the reserved tail. -/
theorem reservedCoercivityScalar38 (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper) (a : ℝ) (ha : 0 < a) :
    ∃ growth R₀ : ℝ, 0 < growth ∧ 1 ≤ R₀ ∧
      ∀ c : ℕ → ℝ, (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ R H : ℝ, R₀ ≤ R → a * R^2 ≤ H →
        HasSum (fun j : ℕ => coefficient c (j+2) * (Real.sqrt H)^(j+2))
          (weight c (H^(1/4 : ℝ)) - coefficient c 0 - coefficient c 1 * Real.sqrt H) ∧
        growth * Real.exp (growth * R^(1/4 : ℝ)) ≤
          ∑' j : ℕ, coefficient c (j+2) * (Real.sqrt H)^(j+2) := by
  obtain ⟨g, R₀, hg, hR₀, h⟩ := weight_uniform_reserved_tail_norm_growth lower upper hlower hlu a ha
  refine ⟨g, R₀, hg, hR₀, fun c hb hu R H hR hH => ?_⟩
  have hH0 : 0 ≤ H := le_trans (mul_nonneg ha.le (sq_nonneg R)) hH
  have hs := reserved_tail_hasSum38 lower upper c hlower hb hu H hH0
  exact ⟨hs, by rw [hs.tsum_eq]; exact h c hb hu R H hR hH⟩

end NlsGge.Weights
