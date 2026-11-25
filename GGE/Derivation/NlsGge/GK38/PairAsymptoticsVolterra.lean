import NlsGge.GK38.PairAnalyticOp

/-!
# F5: the first Volterra forcing and weighted propagation

GK Lemma 2.1: estimates for `M-E` follow from the oscillatory first forcing `V E`.
The inhomogeneous Volterra bound is proved using the accepted factorial iterate
estimate, by iterating the same integral equation and summing the exponential
series. This supplies the exponential amplification of the Gronwall argument.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-- The first, oscillatory Volterra forcing `F = V E`. -/
def pairForce38 (φ : PotPair) (z : ℂ) : PairCont38 :=
  volterraP φ z (freeFundP z)

theorem pairForce38_entry (φ : PotPair) (z : ℂ)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    pairForce38 φ z t i j =
      ∫ s : ℝ in 0..(t : ℝ),
        (freeE z ((t : ℝ) - 2 * s) * potCoeff38 φ s) i j := by
  have hK : Continuous (fun s : ℝ => freeE z ((t : ℝ) - s)) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have hint := intervalIntegrable_triple_entry φ hK
    (continuous_ext38 (freeFundP z)) i j
  unfold pairForce38
  rw [volterraP_apply, volterraFun_apply]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le zero_le_one] using uIcc_zero_subset t.2 hs
  change (freeE z ((t : ℝ) - s) * potCoeff38 φ s * ext38 (freeFundP z) s) i j =
    (freeE z ((t : ℝ) - 2 * s) * potCoeff38 φ s) i j
  rw [ext38_of_mem _ hs']
  change (freeE z ((t : ℝ) - s) * potCoeff38 φ s * freeE z s) i j = _
  rw [mul_assoc, ← freeE_neg_mul_potCoeff38, ← mul_assoc, ← freeE_add]
  congr 3
  ring

/-- Truncated Neumann identity for a general inhomogeneous Volterra equation. -/
theorem volterra_solution_eq_sum (φ : PotPair) (z : ℂ) (H N : PairCont38)
    (hN : N = H + volterraP φ z N) (n : ℕ) :
    N = (∑ k ∈ Finset.range n, (volterraP φ z ^ k) H) +
      (volterraP φ z ^ n) N := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : (volterraP φ z ^ n) N =
        (volterraP φ z ^ n) H + (volterraP φ z ^ (n + 1)) N := by
      conv_lhs => rw [hN]
      rw [map_add, pow_succ, mul_apply_eq_comp]
    rw [Finset.sum_range_succ, add_assoc, ← heq]
    exact ih

/-- A weighted bound on the forcing propagates through the Volterra resolvent. -/
theorem norm_volterra_solution_entry_le_weighted
    (φ : PotPair) (z : ℂ) (H N : PairCont38) (γ : ℝ)
    (_hγ : 0 ≤ γ)
    (hH : ∀ s : ℝ, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖H ⟨s, hs⟩ i j‖ ≤ Real.exp (|z.im| * s) * γ)
    (hN : N = H + volterraP φ z N)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖N t i j‖ ≤ Real.exp (|z.im| * (t : ℝ) + potPrim38 φ (t : ℝ)) * γ := by
  let W : ℝ := potPrim38 φ t
  have hbound (n : ℕ) : ‖N t i j‖ ≤
      Real.exp (|z.im| * (t : ℝ)) *
        (∑ k ∈ Finset.range n, W ^ k / k.factorial) * γ +
      Real.exp (|z.im| * (t : ℝ)) * (W ^ n / n.factorial) * ‖N‖ := by
    have heq := congrArg (fun G : PairCont38 => G t i j)
      (volterra_solution_eq_sum φ z H N hN n)
    simp only [ContinuousMap.add_apply, Pi.add_apply, ContinuousMap.coe_sum,
      Finset.sum_apply] at heq
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Finset.mul_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
      exact norm_volterra_pow_entry_le_weighted φ z k H γ hH t.2 i j
    · exact norm_volterra_pow_entry_le φ z n N t.2 i j
  have hlim := ((NormedSpace.expSeries_div_hasSum_exp W).tendsto_sum_nat.const_mul
    (Real.exp (|z.im| * (t : ℝ)))).mul_const γ
  rw [← Real.exp_eq_exp_ℝ] at hlim
  have hrem := ((FloorSemiring.tendsto_pow_div_factorial_atTop W).const_mul
    (Real.exp (|z.im| * (t : ℝ)))).mul_const ‖N‖
  have hle := ge_of_tendsto' (hlim.add hrem) hbound
  simpa only [mul_zero, zero_mul, add_zero, ← Real.exp_add, W] using hle

/-- The difference from the free solution solves the equation with first forcing `V E`. -/
theorem fundCont_sub_free_eq (φ : PotPair) (z : ℂ) :
    fundContP φ z - freeFundP z = pairForce38 φ z +
      volterraP φ z (fundContP φ z - freeFundP z) := by
  rw [map_sub]
  unfold pairForce38
  have h := fundCont_eq_add φ z
  linear_combination h

end

end NlsGge.GK38
