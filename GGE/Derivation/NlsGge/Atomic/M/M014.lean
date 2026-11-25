import Mathlib
import NlsGge.Atomic.M.M010Host
import NlsGge.Atomic.M.M014Host
import NlsGge.Atomic.M.M014Support1

/- M-014 PRODUCTION01 (proof development, AUTHOR; not reviewed).  First two theorem heads of "### M-014" (round 14) VERBATIM:
   `higher_action_gap_integral`, `complex_higher_action_real`.  The third head `hierarchy_trace_real_restriction` needs M-018 (Pro:
   "may depend on M018") and is NOT in this file.  Route (differs from Pro's prose, see M014_ROUTE.md): level-k version of the landed
   k = 1 ellipse-deformation chain (M014Support1) instead of integration by parts with the M009 primitive. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M014Aux
noncomputable section

theorem sphere_subset_cutDomain (u : PhysicalL2) (n : ℤ) :
    Metric.sphere (discC (realSlice u) n) (discR (realSlice u) n) ⊆
      actionCutDomain38 (realSlice u) := by
  have hf := isolating_family38 (realSlice u) (realSlice_mem_gkW u)
  simpa only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul] using
    action_contour_sphere_subset38 (realSlice u) (discC (realSlice u)) (discC (realSlice u))
      (discR (realSlice u)) (discR (realSlice u)) hf hf n 0 ⟨le_rfl, zero_le_one⟩

theorem discR_pos (u : PhysicalL2) (n : ℤ) : 0 < discR (realSlice u) n := by
  have hf := isolating_family38 (realSlice u) (realSlice_mem_gkW u)
  obtain ⟨κ, N, hg, _⟩ := hf
  exact (hg.1 n).1

end
end NlsGge.ThirdConsultation.M014Aux

namespace NlsGge.ThirdConsultation.M

theorem higher_action_gap_integral (u : PhysicalL2)
    (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (∀ z : ℂ, z ∈ Metric.sphere (discC (realSlice u) n)
        (discR (realSlice u) n) → canonRoot38 (realSlice u) z ≠ 0) ∧
    CircleIntegrable
      (fun z : ℂ => z ^ k * deriv (discrim (realSlice u)) z /
        canonRoot38 (realSlice u) z)
      (discC (realSlice u) n) (discR (realSlice u) n) ∧
    IntervalIntegrable
      (fun x : ℝ => x ^ (k - 1) * spectralHeight u n x) volume
      (periodicMinus u n) (periodicPlus u n) ∧
    complexHigherAction (realSlice u) n k =
      (((2 / Real.pi) * ∫ x in periodicMinus u n..periodicPlus u n,
        x ^ (k - 1) * spectralHeight u n x : ℝ) : ℂ) ∧
    higherAction u n k =
      (2 / Real.pi) * ∫ x in periodicMinus u n..periodicPlus u n,
        x ^ (k - 1) * spectralHeight u n x := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hsub := M014Aux.sphere_subset_cutDomain u n
  have hr := M014Aux.discR_pos u n
  have hpm : (m + 1 - 1) = m := by omega
  have hfun : (fun z : ℂ => z ^ (m + 1) * deriv (discrim (realSlice u)) z /
      canonRoot38 (realSlice u) z) = fun z : ℂ => z ^ (m + 1) *
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z) := by
    funext z; rw [mul_div_assoc]
  have hcirc := M014Aux.contour_pow_family_real u n m
  have hmain : NlsGge.GKDefinitionDesign.higherAction (m + 1) (realSlice u) n =
      (((m + 1 : ℕ) : ℂ)) * ((((2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        x ^ m * actualGapHeightE02_38 u x : ℝ)) : ℂ) := by
    unfold NlsGge.GKDefinitionDesign.higherAction
    rw [hfun, hcirc]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hcomplex : complexHigherAction (realSlice u) n (m + 1) =
      (((2 / Real.pi) * ∫ x in periodicMinus u n..periodicPlus u n,
        x ^ (m + 1 - 1) * spectralHeight u n x : ℝ) : ℂ) := by
    unfold complexHigherAction
    rw [dif_pos hk, hmain, hpm]
    have hk0 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
    rfl
  refine ⟨?_, ?_, ?_, hcomplex, ?_⟩
  · intro z hz
    exact canonRoot_ne_zero38 (realSlice u) (realSlice_mem_gkW u) z (hsub hz)
  · rw [hfun]
    have hfan : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (m + 1) *
        (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z))
        (actionCutDomain38 (realSlice u)) := by
      intro z hz
      exact ((analyticAt_id (z := z)).pow (m + 1)).mul
        (NlsGge.GK38.ActionUpperArc.quotient_analytic u z hz)
    exact ContinuousOn.circleIntegrable hr.le (hfan.continuousOn.mono hsub)
  · rw [hpm]
    exact ((continuous_pow m).mul (continuous_actualGapHeightE02_38 u)).intervalIntegrable _ _
  · have hG : NlsGge.GKDefinitionDesign.higherAction (m + 1) (realSlice u) n =
        ((m + 1 : ℕ) : ℂ) * complexHigherAction (realSlice u) n (m + 1) := by
      unfold complexHigherAction
      rw [dif_pos hk]
      have hk0 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      field_simp
    unfold higherAction
    rw [dif_pos hk, hG, hcomplex, hpm]
    have : ((m + 1 : ℕ) : ℂ) * (((2 / Real.pi) * ∫ x in periodicMinus u n..periodicPlus u n,
        x ^ m * spectralHeight u n x : ℝ) : ℂ) =
        ((((m + 1 : ℕ) : ℝ) * ((2 / Real.pi) * ∫ x in periodicMinus u n..periodicPlus u n,
        x ^ m * spectralHeight u n x) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
    have hk0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    field_simp

theorem complex_higher_action_real
    (u : PhysicalL2) (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (complexHigherAction (realSlice u) n k).im = 0 ∧
    complexHigherAction (realSlice u) n k = (higherAction u n k : ℂ) := by
  obtain ⟨-, -, -, h4, h5⟩ := higher_action_gap_integral u n k hk
  rw [h4, h5]
  exact ⟨Complex.ofReal_im _, rfl⟩

end NlsGge.ThirdConsultation.M
