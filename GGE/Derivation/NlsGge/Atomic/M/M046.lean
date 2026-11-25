import Mathlib
import NlsGge.Atomic.M.M001
import NlsGge.Atomic.LIB.LIB086
import NlsGge.GK38.MolnarActionHolder

/- M-046 PRODUCTION (proof development, AUTHOR; not reviewed).  Target NlsGge/Atomic/M/M046.lean, namespace
   NlsGge.ThirdConsultation.M.  Heads: Pro round 10 section 2 (response commit 178f84d6, file
   handoff/definitions_followup_20261030/PRO_DEFINITION_RESPONSE_FP80_10.md), verbatim: the unconditional
   ENNReal moment inequality and the finite-moment real wrapper.  The ENNReal definition
   actionWeightedSumENNReal is already landed in NlsGge/Atomic/M/M001.lean with the round 10 body; it is not
   re-hosted here.  Route: unconditional ENNReal case split.  If A_m = infinity, then A_0 is nonzero, so the
   right side is infinity.  If A_m is finite, then A_0 and A_1 are finite, the landed real Holder HasSum theorem
   applies, and the real inequality is transported to ENNReal by ofReal. -/
set_option autoImplicit false

open scoped ENNReal BigOperators
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.M

theorem m046_term_nonneg (u : PhysicalL2) (j : ℕ) (n : ℤ) :
    0 ≤ molnarWeight j n ^ 2 * action u n :=
  mul_nonneg (sq_nonneg _) (NlsGge.GKDefinitionDesign.realActionNonneg38 u n)

theorem m046_real_nonneg (u : PhysicalL2) (j : ℕ) :
    0 ≤ actionWeightedSum j u :=
  tsum_nonneg fun n => m046_term_nonneg u j n

theorem m046_weight_le (j k : ℕ) (hjk : j ≤ k) (n : ℤ) :
    molnarWeight j n ^ 2 ≤ molnarWeight k n ^ 2 := by
  have h1 : (1 : ℝ) ≤ 1 + |2 * Real.pi * (n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
  have hj : molnarWeight j n ≤ molnarWeight k n := pow_le_pow_right₀ h1 hjk
  have hnn : 0 ≤ molnarWeight j n := by
    unfold molnarWeight
    positivity
  exact pow_le_pow_left₀ hnn hj 2

theorem m046_pow_weight (m : ℕ) (n : ℤ) :
    (molnarWeight 1 n ^ 2) ^ m = molnarWeight m n ^ 2 := by
  unfold molnarWeight
  rw [pow_one, ← pow_mul, ← pow_mul, mul_comm (2 : ℕ) m]

theorem m046_enn_le (j k : ℕ) (hjk : j ≤ k) (u : PhysicalL2) :
    actionWeightedSumENNReal j u ≤ actionWeightedSumENNReal k u := by
  unfold actionWeightedSumENNReal
  exact ENNReal.tsum_le_tsum fun n =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (m046_weight_le j k hjk n)
      (NlsGge.GKDefinitionDesign.realActionNonneg38 u n))

theorem m046_summable (j : ℕ) (u : PhysicalL2)
    (hne : actionWeightedSumENNReal j u ≠ ⊤) :
    Summable (fun n : ℤ => molnarWeight j n ^ 2 * action u n) :=
  NlsGge.Atomic.LIB086.summable_of_tsum_ofReal_ne_top
    (f := fun n : ℤ => molnarWeight j n ^ 2 * action u n)
    (fun n => m046_term_nonneg u j n) hne

theorem m046_ofReal_eq (j : ℕ) (u : PhysicalL2)
    (hs : Summable (fun n : ℤ => molnarWeight j n ^ 2 * action u n)) :
    ENNReal.ofReal (actionWeightedSum j u) = actionWeightedSumENNReal j u := by
  unfold actionWeightedSum actionWeightedSumENNReal
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => m046_term_nonneg u j n) hs

theorem m046_A0_ne_zero (u : PhysicalL2) (m : ℕ)
    (hfin : actionWeightedSumENNReal m u = ⊤) :
    actionWeightedSumENNReal 0 u ≠ 0 := by
  intro h0
  unfold actionWeightedSumENNReal at h0
  have hterm : ∀ n : ℤ, ENNReal.ofReal (molnarWeight 0 n ^ 2 * action u n) = 0 :=
    ENNReal.tsum_eq_zero.mp h0
  have hz : ∀ n : ℤ, action u n = 0 := by
    intro n
    have h1 : molnarWeight 0 n ^ 2 * action u n ≤ 0 := ENNReal.ofReal_eq_zero.mp (hterm n)
    have hw0 : molnarWeight 0 n ^ 2 = 1 := by simp [molnarWeight]
    rw [hw0, one_mul] at h1
    exact le_antisymm h1 (NlsGge.GKDefinitionDesign.realActionNonneg38 u n)
  have hAm : actionWeightedSumENNReal m u = 0 := by
    unfold actionWeightedSumENNReal
    simp [hz]
  exact ENNReal.top_ne_zero (hfin.symm.trans hAm)

theorem m046_real_holder (u : PhysicalL2) (m : ℕ) (hm : 1 ≤ m)
    (hs0 : Summable (fun n : ℤ => molnarWeight 0 n ^ 2 * action u n))
    (hs1 : Summable (fun n : ℤ => molnarWeight 1 n ^ 2 * action u n))
    (hsm : Summable (fun n : ℤ => molnarWeight m n ^ 2 * action u n)) :
    actionWeightedSum 1 u ^ m ≤
      actionWeightedSum m u * actionWeightedSum 0 u ^ (m - 1) := by
  have hM : HasSum (fun n : ℤ => action u n) (actionWeightedSum 0 u) := by
    have hfun : (fun n : ℤ => action u n) =
        (fun n : ℤ => molnarWeight 0 n ^ 2 * action u n) := by
      funext n
      simp [molnarWeight]
    rw [hfun]
    exact hs0.hasSum
  have hA : HasSum (fun n : ℤ => action u n * molnarWeight 1 n ^ 2)
      (actionWeightedSum 1 u) := by
    have hfun : (fun n : ℤ => action u n * molnarWeight 1 n ^ 2) =
        (fun n : ℤ => molnarWeight 1 n ^ 2 * action u n) := by
      funext n
      exact mul_comm _ _
    rw [hfun]
    exact hs1.hasSum
  have hX : HasSum (fun n : ℤ => action u n * (molnarWeight 1 n ^ 2) ^ m)
      (actionWeightedSum m u) := by
    have hfun : (fun n : ℤ => action u n * (molnarWeight 1 n ^ 2) ^ m) =
        (fun n : ℤ => molnarWeight m n ^ 2 * action u n) := by
      funext n
      rw [m046_pow_weight m n]
      exact mul_comm _ _
    rw [hfun]
    exact hsm.hasSum
  have key := NlsGge.GK38.MolnarBounds38.molnar_weighted_holder_hasSum38 m hm
    (fun n : ℤ => action u n) (fun n : ℤ => molnarWeight 1 n ^ 2)
    (fun n => NlsGge.GKDefinitionDesign.realActionNonneg38 u n)
    (fun n => sq_nonneg (molnarWeight 1 n))
    (actionWeightedSum 0 u) (actionWeightedSum 1 u) (actionWeightedSum m u) hM hA hX
  rw [mul_comm (actionWeightedSum m u)]
  exact key

theorem action_weight_log_convex_finite
    (u : PhysicalL2) (m : ℕ) (hm : 1 ≤ m)
    (hfinite : actionWeightedSumENNReal m u ≠ ⊤) :
    Summable (fun n : ℤ => molnarWeight 0 n ^ 2 * action u n) ∧
    Summable (fun n : ℤ => molnarWeight 1 n ^ 2 * action u n) ∧
    Summable (fun n : ℤ => molnarWeight m n ^ 2 * action u n) ∧
    actionWeightedSum 1 u ^ m ≤
      actionWeightedSum m u * actionWeightedSum 0 u ^ (m - 1) := by
  have hs0 := m046_summable 0 u
    (ne_top_of_le_ne_top hfinite (m046_enn_le 0 m (Nat.zero_le m) u))
  have hs1 := m046_summable 1 u (ne_top_of_le_ne_top hfinite (m046_enn_le 1 m hm u))
  have hsm := m046_summable m u hfinite
  exact ⟨hs0, hs1, hsm, m046_real_holder u m hm hs0 hs1 hsm⟩

theorem action_weight_log_convex
    (u : PhysicalL2) (m : ℕ) (hm : 1 ≤ m) :
    actionWeightedSumENNReal 1 u ^ m ≤
      actionWeightedSumENNReal m u *
        actionWeightedSumENNReal 0 u ^ (m - 1) := by
  by_cases hfin : actionWeightedSumENNReal m u = ⊤
  · have hA0 := m046_A0_ne_zero u m hfin
    rw [hfin, ENNReal.top_mul (ENNReal.pow_ne_zero hA0 (m - 1))]
    exact le_top
  · obtain ⟨hs0, hs1, hsm, hreal⟩ := action_weight_log_convex_finite u m hm hfin
    rw [← m046_ofReal_eq 1 u hs1, ← m046_ofReal_eq m u hsm, ← m046_ofReal_eq 0 u hs0,
      ← ENNReal.ofReal_pow (m046_real_nonneg u 1), ← ENNReal.ofReal_pow (m046_real_nonneg u 0),
      ← ENNReal.ofReal_mul (m046_real_nonneg u m)]
    exact ENNReal.ofReal_le_ofReal hreal

end NlsGge.ThirdConsultation.M
