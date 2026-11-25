import NlsGge.Spectral.ReservedCoercivityScalar38V1

/-!
# NEW-F06: abstract reserved-energy coercivity (spec W-F06b target 4)

For any nonnegative sequence `Q` with `√H^{j+1} ≤ Q j` for `j ≥ 1` (the moment inequality
F:eq:moment, supplied on the plane by W-F06a) and `H ≥ a R²`, the reserved series
`Σ_{j≥0} β_{j+1} Q j` (F:eq:B) is at least `g e^{g R^{1/4}}` for `R ≥ R₀`.
The `j = 0` term is dropped as nonnegative, as in v2 F:eq:EBH.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Weights

theorem reservedCoercivityAbstract38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up)
    (a : ℝ) (ha : 0 < a) :
    ∃ g R₀ : ℝ, 0 < g ∧ 1 ≤ R₀ ∧
      ∀ c : ℕ → ℝ, (∀ j, lo ≤ c j) → (∀ j, c j ≤ up) →
      ∀ R H : ℝ, R₀ ≤ R → a * R ^ 2 ≤ H →
      ∀ Q : ℕ → ℝ, (∀ j, 0 ≤ Q j) → (∀ j, 1 ≤ j → Real.sqrt H ^ (j + 1) ≤ Q j) →
      Summable (fun j => coefficient c (j + 1) * Q j) →
        g * Real.exp (g * R ^ (1 / 4 : ℝ)) ≤ ∑' j, coefficient c (j + 1) * Q j := by
  obtain ⟨g, R₀, hg, hR₀, h⟩ := reservedCoercivityScalar38 lo up hl hlu a ha
  refine ⟨g, R₀, hg, hR₀, fun c hb hu R H hR hH Q hQ0 hQ hsum => ?_⟩
  obtain ⟨hs, hlow⟩ := h c hb hu R H hR hH
  have hcoef : ∀ j, 0 ≤ coefficient c j := fun j => by
    unfold coefficient
    have := lt_of_lt_of_le hl (hb j)
    positivity
  rw [hsum.tsum_eq_zero_add]
  have hshift : Summable (fun k : ℕ => coefficient c (k + 1 + 1) * Q (k + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have hcmp : ∑' k : ℕ, coefficient c (k + 2) * Real.sqrt H ^ (k + 2) ≤
      ∑' k : ℕ, coefficient c (k + 1 + 1) * Q (k + 1) := by
    refine Summable.tsum_le_tsum (fun k => ?_) hs.summable hshift
    exact mul_le_mul_of_nonneg_left (hQ (k + 1) (by omega)) (hcoef _)
  have h0 : 0 ≤ coefficient c (0 + 1) * Q 0 := mul_nonneg (hcoef _) (hQ0 0)
  linarith

end NlsGge.Weights
