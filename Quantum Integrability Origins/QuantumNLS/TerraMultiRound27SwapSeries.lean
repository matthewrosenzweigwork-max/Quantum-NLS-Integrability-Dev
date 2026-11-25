import QuantumNLS.TerraMultiRound27SwapCompression

/-! Swap covariance passes through the inverse-square-root series. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.LocalSpectral.Round27
open Round23 Round26

/-- A small complex-linear operator commuting with swap-conjugation has an
inverse-square-root series that commutes with the same anti-linear involution. -/
theorem invSqrtM_swap (A : E2 →L[ℂ] E2) (hA : ‖A - 1‖ < 1)
    (h : ∀ v, A (swapConj v) = swapConj (A v)) (v : E2) :
    invSqrtM A (swapConj v) = swapConj (invSqrtM A v) := by
  have hsub (w : E2) : (A - 1) (swapConj w) = swapConj ((A - 1) w) := by
    change A (swapConj w) - swapConj w = swapConj (A w - w)
    have hs : swapConj (A w - w) = swapConj (A w) - swapConj w :=
      swapFiberReal.map_sub (A w) w
    rw [hs, h w]
  have hp (k : ℕ) (w : E2) : ((A - 1) ^ k) (swapConj w) = swapConj (((A - 1) ^ k) w) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [pow_succ', mul_apply_eq_comp, hsub, ih]
  have hs := summable_invSqrtM hA
  have h1 := (ContinuousLinearMap.apply ℂ E2 v).map_tsum hs
  have h2 := (ContinuousLinearMap.apply ℂ E2 (swapConj v)).map_tsum hs
  have h3 := swapFiberReal.toContinuousLinearMap.map_tsum
    ((ContinuousLinearMap.apply ℂ E2 v).summable hs)
  simp only [ContinuousLinearMap.apply_apply] at h1 h2 h3
  change swapConj (∑' k : ℕ, ((invSqrtCoeff k : ℂ) • (A - 1) ^ k) v) =
    ∑' k : ℕ, swapConj (((invSqrtCoeff k : ℂ) • (A - 1) ^ k) v) at h3
  unfold invSqrtM
  rw [h1, h2, h3]
  apply tsum_congr
  intro k
  simp only [smul_apply, hp]
  change (invSqrtCoeff k) • swapFiberReal (((A - 1) ^ k) v) =
    swapFiberReal ((invSqrtCoeff k) • (((A - 1) ^ k) v))
  exact (map_smul swapFiberReal (invSqrtCoeff k) _).symm

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.invSqrtM_swap
