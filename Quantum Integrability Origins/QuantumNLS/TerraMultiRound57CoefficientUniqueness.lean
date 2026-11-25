import QuantumNLS.TerraMultiRound57Tail

/-! Uniqueness of finite complex inverse-power asymptotic coefficients. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57CoefficientUniqueness

/-- If a finite inverse-power polynomial is little-oh of its final power,
all its coefficients vanish. -/
theorem inverse_power_coefficients_zero (N : ℕ) (c : ℕ → ℂ)
    (h : (fun Y : ℝ => ∑ i ∈ Finset.range (N + 1), (Y⁻¹ ^ i) • c i)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N)) :
    ∀ j ≤ N, c j = 0 := by
  have hz : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hp (i j : ℕ) (hij : j < i) :
      (fun Y : ℝ => (Y⁻¹ ^ i) • c i) =o[atTop] (fun Y : ℝ => Y⁻¹ ^ j) := by
    have hpow := (isLittleO_pow_pow (𝕜 := ℝ) hij).comp_tendsto hz
    simpa using hpow.smul_isBigO (isBigO_const_one ℝ (c i) atTop)
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hscale : (fun Y : ℝ => Y⁻¹ ^ N) =O[atTop] (fun Y : ℝ => Y⁻¹ ^ j) := by
      rcases lt_or_eq_of_le hj with hlt | heq
      · exact ((isLittleO_pow_pow (𝕜 := ℝ) hlt).comp_tendsto hz).isBigO
      · subst N
        exact isBigO_refl _ _
    have hpoly := h.trans_isBigO hscale
    have hhigh : (fun Y : ℝ => ∑ i ∈ Finset.Ico (j + 1) (N + 1), (Y⁻¹ ^ i) • c i)
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ j) := by
      have hh : ∀ i ∈ Finset.Ico (j + 1) (N + 1),
          (fun Y : ℝ => (Y⁻¹ ^ i) • c i) =o[atTop] (fun Y : ℝ => Y⁻¹ ^ j) := by
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        exact hp i j (by omega)
      convert IsLittleO.sum hh using 1
      funext Y
      simp only [Finset.sum_apply]
    have hone : (fun Y : ℝ => (Y⁻¹ ^ j) • c j) =o[atTop] (fun Y : ℝ => Y⁻¹ ^ j) := by
      have hh := hpoly.sub hhigh
      convert hh using 1
      · funext Y
        have hlo : (∑ i ∈ Finset.range j, (Y⁻¹ ^ i) • c i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hi' := Finset.mem_range.mp hi
          rw [ih i hi' (by omega)]
          simp
        have hsplit := Finset.sum_range_add_sum_Ico (fun i => (Y⁻¹ ^ i) • c i) (show j + 1 ≤ N + 1 by omega)
        rw [Finset.sum_range_succ, hlo, zero_add] at hsplit
        rw [← hsplit]
        simp
    by_contra hc
    have hbound := hone.bound (half_pos (norm_pos_iff.mpr hc))
    have hpos : ∀ᶠ Y : ℝ in atTop, 0 < Y := eventually_gt_atTop 0
    have hbad : ∀ᶠ Y : ℝ in atTop, False := by
      filter_upwards [hbound, hpos] with Y hb hY
      have hYpow : 0 < ‖Y⁻¹ ^ j‖ := norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero hY.ne'))
      have hcn : 0 < ‖c j‖ := norm_pos_iff.mpr hc
      simp only [norm_smul] at hb
      nlinarith
    obtain ⟨_, hfalse⟩ := hbad.exists
    exact hfalse

/-- Two finite inverse-power expansions of the same function, both with a
little-oh remainder at their final order, have identical coefficients. -/
theorem inverse_power_coefficients_unique (N : ℕ) (f : ℝ → ℂ) (c d : ℕ → ℂ)
    (hc : (fun Y : ℝ => f Y - ∑ i ∈ Finset.range (N + 1), (Y⁻¹ ^ i) • c i)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N))
    (hd : (fun Y : ℝ => f Y - ∑ i ∈ Finset.range (N + 1), (Y⁻¹ ^ i) • d i)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N)) :
    ∀ j ≤ N, c j = d j := by
  have hdiff : (fun Y : ℝ => ∑ i ∈ Finset.range (N + 1), (Y⁻¹ ^ i) • (c i - d i))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N) := by
    have hh := hd.sub hc
    convert hh using 1
    funext Y
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  intro j hj
  exact sub_eq_zero.mp (inverse_power_coefficients_zero N (fun i => c i - d i) hdiff j hj)

#print axioms inverse_power_coefficients_zero
#print axioms inverse_power_coefficients_unique
end QuantumNLS.TerraMultiRound57CoefficientUniqueness
