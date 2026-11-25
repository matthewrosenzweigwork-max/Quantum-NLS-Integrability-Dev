import Mathlib
import NlsGge.Atomic.M.M014

/- M-015 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Head VERBATIM from Pro round 14 ("### M-015"; the round-14 text prints no change to
   the round-13 head).  Route: M-014 gives higherAction u n (2m+1) = (2/pi) int_{lam-}^{lam+} x^(2m) v; nonnegativity from v >= 0 and even power;
   the point zeta is the weighted mean-value theorem (min/max of x^(2m) on the closed gap and the intermediate value theorem; the
   collapsed gap case W = 0 takes zeta = lam-). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M015Aux
noncomputable section

theorem weighted_mean_value (g v : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hv0 : ∀ x ∈ Icc a b, 0 ≤ v x) :
    ∃ ζ ∈ Icc a b, (∫ x in a..b, g x * v x) = g ζ * ∫ x in a..b, v x := by
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.mpr hab⟩
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn hne hg
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hg
  have hvi : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab
  have hgvi : IntervalIntegrable (fun x => g x * v x) volume a b :=
    (hg.mul hv).intervalIntegrable_of_Icc hab
  have hlow : g xm * ∫ x in a..b, v x ≤ ∫ x in a..b, g x * v x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab (hvi.const_mul _) hgvi
    intro x hx
    exact mul_le_mul_of_nonneg_right (hmin hx) (hv0 x hx)
  have hup : (∫ x in a..b, g x * v x) ≤ g xM * ∫ x in a..b, v x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hgvi (hvi.const_mul _)
    intro x hx
    exact mul_le_mul_of_nonneg_right (hmax hx) (hv0 x hx)
  have hW : 0 ≤ ∫ x in a..b, v x := intervalIntegral.integral_nonneg hab hv0
  rcases hW.eq_or_lt with hW0 | hWp
  · refine ⟨a, left_mem_Icc.mpr hab, ?_⟩
    rw [← hW0] at hlow hup ⊢
    linarith
  · set W := ∫ x in a..b, v x with hWdef
    set r := (∫ x in a..b, g x * v x) / W with hr
    have hr1 : g xm ≤ r := by rw [hr, le_div_iff₀ hWp]; exact hlow
    have hr2 : r ≤ g xM := by rw [hr, div_le_iff₀ hWp]; exact hup
    have hsub : uIcc xm xM ⊆ Icc a b := Set.uIcc_subset_Icc hxm hxM
    have hcont : ContinuousOn g (uIcc xm xM) := hg.mono hsub
    have hr_mem : r ∈ uIcc (g xm) (g xM) := Set.mem_uIcc.mpr (Or.inl ⟨hr1, hr2⟩)
    obtain ⟨ζ, hζ, hgζ⟩ := intermediate_value_uIcc hcont hr_mem
    refine ⟨ζ, hsub hζ, ?_⟩
    rw [hgζ, hr]
    field_simp

end
end NlsGge.ThirdConsultation.M015Aux

namespace NlsGge.ThirdConsultation.M

theorem odd_action_mean_value
    (u : PhysicalL2) (n : ℤ) (m : ℕ) :
  0 ≤ higherAction u n (2*m+1) ∧
  ∃ zeta : ℝ, zeta ∈ closedGap u n ∧
    higherAction u n (2*m+1) =
      zeta^(2*m) * action u n := by
  obtain ⟨-, -, -, -, h5⟩ := higher_action_gap_integral u n (2 * m + 1) (by omega)
  have e : 2 * m + 1 - 1 = 2 * m := by omega
  rw [e] at h5
  have hord : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
    obtain ⟨x, hx⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
    rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2] at hx
    exact hx.1.trans hx.2
  have h5' : higherAction u n (2 * m + 1) = (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        x ^ (2 * m) * actualGapHeightE02_38 u x := h5
  have hact : action u n = (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        actualGapHeightE02_38 u x := rfl
  refine ⟨?_, ?_⟩
  · rw [h5']
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg hord (fun x _ =>
      mul_nonneg ((even_two_mul m).pow_nonneg x) (actualGapHeightE02_38_nonneg u x))
  · obtain ⟨ζ, hζ, hmv⟩ := M015Aux.weighted_mean_value (fun x : ℝ => x ^ (2 * m))
      (actualGapHeightE02_38 u) (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) hord
      (continuous_pow _).continuousOn (continuous_actualGapHeightE02_38 u).continuousOn
      (fun x _ => actualGapHeightE02_38_nonneg u x)
    refine ⟨ζ, hζ, ?_⟩
    rw [h5', hact, hmv]
    ring

end NlsGge.ThirdConsultation.M
