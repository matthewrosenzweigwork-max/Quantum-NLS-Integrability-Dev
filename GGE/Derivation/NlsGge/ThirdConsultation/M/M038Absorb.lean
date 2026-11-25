import Mathlib

/- proof development M038Absorb (AUTHOR; not self-reviewed). Host for the M-038 absorption algebra.
   Mathlib only. Target host module NlsGge/ThirdConsultation/M/M038Absorb.lean.
   young_rpow: weighted AM-GM with a free scale, for N^(2-s) B^((2m+1)s) <= eta N^2 + D B^(4m+2).
   young_sum: finite-sum form (cardinality times eta N^2 plus one power of B). -/
set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M.M038Absorb

theorem young_rpow (m : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (κ η : ℝ) (hκ : 0 ≤ κ) (hη : 0 < η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N B : ℝ, 0 ≤ N → 0 ≤ B →
      κ * (N ^ (2 - s) * B ^ ((2 * (m : ℝ) + 1) * s)) ≤
        η * N ^ 2 + D * B ^ (4 * m + 2) := by
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = κ + 1 := ⟨_, rfl⟩
  have hκ'0 : 0 < κ' := by rw [hκ']; linarith
  have hκκ' : κ ≤ κ' := by rw [hκ']; linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 - s / 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = s / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hw0 : 0 < w := by rw [hw]; linarith
  have hθw : θ + w = 1 := by rw [hθ, hw]; ring
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = κ' * θ / η := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos (mul_pos hκ'0 hθ0) hη
  have hκθne : κ' * θ ≠ 0 := (mul_pos hκ'0 hθ0).ne'
  have hηne : η ≠ 0 := hη.ne'
  have htκ : κ' * θ / t = η := by
    rw [ht, div_div_eq_mul_div, mul_div_cancel_left₀ η hκθne]
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = κ' * w * t ^ (θ / w) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (mul_nonneg hκ'0.le hw0.le) (Real.rpow_nonneg ht0.le _)
  refine ⟨D, hD0, fun N B hN hB => ?_⟩
  have hX : 0 ≤ N ^ 2 := sq_nonneg N
  have hY : 0 ≤ B ^ (4 * m + 2) := pow_nonneg hB _
  have hPnn : 0 ≤ N ^ (2 - s) * B ^ ((2 * (m : ℝ) + 1) * s) :=
    mul_nonneg (Real.rpow_nonneg hN _) (Real.rpow_nonneg hB _)
  have h1 : (N ^ 2) ^ θ = N ^ (2 - s) := by
    rw [hθ, ← Real.rpow_natCast, ← Real.rpow_mul hN]
    congr 1
    push_cast
    ring
  have h2 : (B ^ (4 * m + 2)) ^ w = B ^ ((2 * (m : ℝ) + 1) * s) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hB]
    congr 1
    push_cast
    ring
  have hp₁ : 0 ≤ N ^ 2 / t := div_nonneg hX ht0.le
  have hp₂ : 0 ≤ t ^ (θ / w) * B ^ (4 * m + 2) :=
    mul_nonneg (Real.rpow_nonneg ht0.le _) hY
  have hAM := Real.geom_mean_le_arith_mean2_weighted hθ0.le hw0.le hp₁ hp₂ hθw
  have hkey : (N ^ 2 / t) ^ θ * (t ^ (θ / w) * B ^ (4 * m + 2)) ^ w =
      (N ^ 2) ^ θ * (B ^ (4 * m + 2)) ^ w := by
    have htθ : t ^ θ ≠ 0 := (Real.rpow_pos_of_pos ht0 θ).ne'
    rw [Real.div_rpow hX ht0.le, Real.mul_rpow (Real.rpow_nonneg ht0.le _) hY,
      ← Real.rpow_mul ht0.le, div_mul_cancel₀ θ hw0.ne', div_mul_eq_mul_div, div_eq_iff htθ]
    ring
  have hκP : κ' * ((N ^ 2) ^ θ * (B ^ (4 * m + 2)) ^ w) ≤
      κ' * (θ * (N ^ 2 / t) + w * (t ^ (θ / w) * B ^ (4 * m + 2))) := by
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left hAM hκ'0.le
  have hκθ : κ' * (θ * (N ^ 2 / t)) = η * N ^ 2 := by
    have e : κ' * (θ * (N ^ 2 / t)) = (κ' * θ / t) * N ^ 2 := by ring
    rw [e, htκ]
  have hsum : κ' * (θ * (N ^ 2 / t) + w * (t ^ (θ / w) * B ^ (4 * m + 2))) =
      η * N ^ 2 + D * B ^ (4 * m + 2) := by
    rw [mul_add, hκθ, hD]
    ring
  calc κ * (N ^ (2 - s) * B ^ ((2 * (m : ℝ) + 1) * s))
      ≤ κ' * (N ^ (2 - s) * B ^ ((2 * (m : ℝ) + 1) * s)) :=
        mul_le_mul_of_nonneg_right hκκ' hPnn
    _ = κ' * ((N ^ 2) ^ θ * (B ^ (4 * m + 2)) ^ w) := by rw [h1, h2]
    _ ≤ κ' * (θ * (N ^ 2 / t) + w * (t ^ (θ / w) * B ^ (4 * m + 2))) := hκP
    _ = η * N ^ 2 + D * B ^ (4 * m + 2) := hsum

theorem young_sum (m : ℕ) {ι : Type*} [DecidableEq ι] (S : Finset ι) (s κ : ι → ℝ)
    (hκ : ∀ i ∈ S, 0 ≤ κ i) (hs0 : ∀ i ∈ S, 0 < s i) (hs1 : ∀ i ∈ S, s i ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N B : ℝ, 0 ≤ N → 0 ≤ B →
      ∑ i ∈ S, κ i * (N ^ (2 - s i) * B ^ ((2 * (m : ℝ) + 1) * s i)) ≤
        (S.card : ℝ) * (η * N ^ 2) + D * B ^ (4 * m + 2) := by
  revert hκ hs0 hs1
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ _
    refine ⟨0, le_refl _, fun N B _ hB => ?_⟩
    simp
  | insert a S ha ih =>
    intro hκ hs0 hs1
    have hκa : 0 ≤ κ a := hκ a (Finset.mem_insert_self a S)
    have hs0a : 0 < s a := hs0 a (Finset.mem_insert_self a S)
    have hs1a : s a ≤ 1 := hs1 a (Finset.mem_insert_self a S)
    obtain ⟨Da, hDa0, hDa⟩ := young_rpow m (s a) hs0a hs1a (κ a) η hκa hη
    obtain ⟨DS, hDS0, hDS⟩ := ih (fun i hi => hκ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hs0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hs1 i (Finset.mem_insert_of_mem hi))
    refine ⟨Da + DS, add_nonneg hDa0 hDS0, fun N B hN hB => ?_⟩
    have h1 := hDa N B hN hB
    have h2 := hDS N B hN hB
    have hB4 : 0 ≤ B ^ (4 * m + 2) := pow_nonneg hB _
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    nlinarith [h1, h2, hB4]

end NlsGge.ThirdConsultation.M.M038Absorb

end
