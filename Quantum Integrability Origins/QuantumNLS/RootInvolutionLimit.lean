import QuantumNLS.RootInvolutionCommutator
import QuantumNLS.RootPlacementBound

/-!
# R-C4F43CA8 `thm:root-involution`, part (2B): the double limit of the scaled commutator expectations

Source: `source/chapters/foundations/ROOT_transfer_involution.tex:98` (proof of the zero Poisson bracket).
Realized inputs (frozen): `RootInvolutionCommutator.limSeq_sum_eq_zero` (2A, `69cdf2df`), `RootOverlapLimit.root_overlap_limit`
(accepted R-32EBD5C1 fixed-order limit to `pbC`), `RootOverlapLimit.root_overlap_bound` (accepted N-uniform bound
`N ‖[Q_p A, Q_q B]‖ ≤ 2pq‖A‖‖B‖`), `RootPlacementBound.norm_physicalKernel_le` (`‖K_{r,z}‖ ≤ 2(Im z)^{-r}`),
`HighMomentsRank.fallR_bounds` (`1 − r(r−1)/(2N) ≤ θ_{N,r} ≤ 1` for `r ≤ N`).

Proved here (standard axioms only):
* `norm_limSeq_le`: `‖limSeq_{p,q}(A,B)(u) N‖ ≤ 2pq‖A‖‖B‖` for every unit `u` and `p, q ≤ N` (uniform in `N`).
* `fallR_tendsto`: `θ_{N,r} → 1` as `N → ∞`; `cf_tendsto`: the coefficients `c_j(N) → κ^{j+1}`.
* `double_limit_zero`: for `0 ≤ κ < Im z`, `κ < Im w` and unit `u`,
  `Σ'_{(n,m)} κ^{n+1} κ^{m+1} pbC(K_{n+1,z}, K_{m+1,w})(u) = 0`
  (dominated convergence over `ℕ × ℕ`, domination `8(n+1)(m+1)(κ/Im z)^{n+1}(κ/Im w)^{m+1}`).

Conjugate pairs (2D) and the series interchange (2C) are NOT here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology

namespace QuantumNLS.RootInvolutionLimit

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.NormalizedTransfer QuantumNLS.RootOverlapLimit QuantumNLS.RootOverlapCommutator
  QuantumNLS.HighMomentsRank QuantumNLS.RootInvolutionCommutator QuantumNLS.RootPlacementBound
  QuantumNLS.SymplecticBracket

variable (L : ℝ) [Fact (0 < L)]

/-- **N-uniform bound** on the scaled commutator expectation (from R-32EBD5C1's bound). -/
theorem norm_limSeq_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel (L2T L) p) (B : BoundedSymmetricKernel (L2T L) q) (u : L2T L)
    (hu : ‖u‖ = 1) :
    ‖limSeq p q A B u N‖ ≤ 2 * ((p : ℝ) * q) * ‖A‖ * ‖B‖ := by
  unfold limSeq
  rw [dif_pos ⟨hp, hq⟩]
  have hvn : ‖(htpow N u : HilbertTensorPower ℂ (L2T L) N)‖ = 1 := by
    rw [norm_htpow, hu, one_pow]
  have hxn : ‖(⟨(htpow N u : HilbertTensorPower ℂ (L2T L) N), htpow_mem_symSector N u⟩ :
      SymSector ℂ (L2T L) N)‖ = 1 := hvn
  have hcoe : ∀ y : SymSector ℂ (L2T L) N,
      ‖(y : HilbertTensorPower ℂ (L2T L) N)‖ = ‖y‖ := fun y => rfl
  have hE : ‖ExN N p q hp hq A B u‖ ≤ ‖CommQ N p q hp hq A B‖ := by
    unfold ExN
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hvn, one_mul, hcoe]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [hxn, mul_one]
  have hb := root_overlap_bound N p q hp hq A B
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ‖(-Complex.I) * (N : ℂ) * ExN N p q hp hq A B u‖
      = (N : ℝ) * ‖ExN N p q hp hq A B u‖ := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_natCast, one_mul]
    _ ≤ (N : ℝ) * ‖CommQ N p q hp hq A B‖ := mul_le_mul_of_nonneg_left hE hNr
    _ ≤ 2 * ((p : ℝ) * q) * ‖A‖ * ‖B‖ := hb

/-- `θ_{N,r} → 1`. -/
theorem fallR_tendsto (r : ℕ) : Tendsto (fun N : ℕ => fallR N r) atTop (𝓝 1) := by
  have h2 : Tendsto (fun N : ℕ => (2 * (N : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h3 : Tendsto (fun N : ℕ => (r : ℝ) * ((r : ℝ) - 1) / (2 * (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have hlow : Tendsto (fun N : ℕ => 1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * (N : ℝ))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · refine eventually_atTop.2 ⟨r + 1, fun N hN => ?_⟩
    exact (fallR_bounds N (by omega) r (by omega)).2.1
  · refine eventually_atTop.2 ⟨r + 1, fun N hN => ?_⟩
    exact (fallR_bounds N (by omega) r (by omega)).2.2

/-- The coefficient `c_j(N) = κ^{j+1} θ_{N,j+1}` tends to `κ^{j+1}`. -/
theorem cf_tendsto (κ : ℝ) (j : ℕ) :
    Tendsto (fun N : ℕ => cf κ N j) atTop (𝓝 ((κ ^ (j + 1) : ℝ) : ℂ)) := by
  have h := (fallR_tendsto (j + 1)).const_mul (κ ^ (j + 1))
  have h' : Tendsto (fun N : ℕ => ((κ ^ (j + 1) * fallR N (j + 1) : ℝ) : ℂ)) atTop
      (𝓝 (((κ ^ (j + 1) * 1 : ℝ) : ℂ))) := (Complex.continuous_ofReal.tendsto _).comp h
  simp only [cf]
  simpa only [mul_one] using h'

/-- Summability of `(n+1) r^{n+1}` for `0 ≤ r < 1`. -/
theorem summable_aux (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1)) := by
  have hr' : ‖r‖ < 1 := by rw [Real.norm_of_nonneg h0]; exact h1
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ (1 : ℕ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr'
  have h3 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 : ℕ) * r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr h2
  refine h3.congr (fun n => ?_)
  push_cast
  ring

/-- The `(n,m)` term of the double series at particle number `N`. -/
def Tn (κ : ℝ) (N : ℕ) (z w : ℂ) (u : L2T L) (nm : ℕ × ℕ) : ℂ :=
  cf κ N nm.1 * cf κ N nm.2 *
    limSeq (nm.1 + 1) (nm.2 + 1) (orderedKernel L (nm.1 + 1) z) (orderedKernel L (nm.2 + 1) w) u N

/-- The finite sums of `Tn` vanish for every `N ≥ 1`. -/
theorem tsum_Tn_eq_zero (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ)
    (hN : 0 < N) : ∑' nm : ℕ × ℕ, Tn L κ N z w u nm = 0 := by
  rw [tsum_eq_sum (s := Finset.range N ×ˢ Finset.range N)]
  · rw [Finset.sum_product]
    simp only [Finset.sum_range]
    exact limSeq_sum_eq_zero L κ hκ N hN z w u hu
  · rintro ⟨n, m⟩ hnm
    have h1 : ¬ (n + 1 ≤ N ∧ m + 1 ≤ N) := by
      intro h
      apply hnm
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    unfold Tn limSeq
    rw [dif_neg h1, mul_zero]


/-- **Domination of the `(n,m)` term** (uniform in `N ≥ 1`):
`‖Tn_N(n,m)‖ ≤ 8 (n+1)(m+1) (κ/Im z)^{n+1} (κ/Im w)^{m+1}`. -/
theorem norm_Tn_le (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ) (hN : 0 < N) (z w : ℂ) (hz : κ < z.im)
    (hw : κ < w.im) (u : L2T L) (hu : ‖u‖ = 1) (nm : ℕ × ℕ) :
    ‖Tn L κ N z w u nm‖ ≤
      8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
        (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1))) := by
  obtain ⟨n, m⟩ := nm
  have hη : 0 < z.im := lt_of_le_of_lt hκ hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ hw
  have hr : 0 ≤ κ / z.im := div_nonneg hκ hη.le
  have hr' : 0 ≤ κ / w.im := div_nonneg hκ hη'.le
  have hRHS : 0 ≤ 8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) *
      (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) :=
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hr _))
      (mul_nonneg (by positivity) (pow_nonneg hr' _)))
  by_cases h1 : n + 1 ≤ N ∧ m + 1 ≤ N
  · obtain ⟨hf0, -, hf1⟩ := fallR_bounds N hN (n + 1) h1.1
    obtain ⟨hg0, -, hg1⟩ := fallR_bounds N hN (m + 1) h1.2
    have hc1 : ‖cf κ N n‖ ≤ κ ^ (n + 1) := by
      unfold cf
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg hκ _) hf0)]
      exact mul_le_of_le_one_right (pow_nonneg hκ _) hf1
    have hc2 : ‖cf κ N m‖ ≤ κ ^ (m + 1) := by
      unfold cf
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg hκ _) hg0)]
      exact mul_le_of_le_one_right (pow_nonneg hκ _) hg1
    have hl := norm_limSeq_le L N (n + 1) (m + 1) h1.1 h1.2 (orderedKernel L (n + 1) z)
      (orderedKernel L (m + 1) w) u hu
    have hA : ‖orderedKernel L (n + 1) z‖ ≤ 2 * (z.im)⁻¹ ^ (n + 1) :=
      norm_physicalKernel_le (L := L) (by omega) z hη
    have hB : ‖orderedKernel L (m + 1) w‖ ≤ 2 * (w.im)⁻¹ ^ (m + 1) :=
      norm_physicalKernel_le (L := L) (by omega) w hη'
    have e1 : (κ / z.im) ^ (n + 1) = κ ^ (n + 1) * (z.im)⁻¹ ^ (n + 1) := by
      rw [div_eq_mul_inv, mul_pow]
    have e2 : (κ / w.im) ^ (m + 1) = κ ^ (m + 1) * (w.im)⁻¹ ^ (m + 1) := by
      rw [div_eq_mul_inv, mul_pow]
    have hα : κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖ ≤ 2 * (κ / z.im) ^ (n + 1) := by
      rw [e1]
      calc κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖
          ≤ κ ^ (n + 1) * (2 * (z.im)⁻¹ ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hA (pow_nonneg hκ _)
        _ = 2 * (κ ^ (n + 1) * (z.im)⁻¹ ^ (n + 1)) := by ring
    have hβ : κ ^ (m + 1) * ‖orderedKernel L (m + 1) w‖ ≤ 2 * (κ / w.im) ^ (m + 1) := by
      rw [e2]
      calc κ ^ (m + 1) * ‖orderedKernel L (m + 1) w‖
          ≤ κ ^ (m + 1) * (2 * (w.im)⁻¹ ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hB (pow_nonneg hκ _)
        _ = 2 * (κ ^ (m + 1) * (w.im)⁻¹ ^ (m + 1)) := by ring
    have hnA : 0 ≤ κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖ := by positivity
    have hnB : 0 ≤ κ ^ (m + 1) * ‖orderedKernel L (m + 1) w‖ := by positivity
    have hpq : (0 : ℝ) ≤ 2 * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) := by positivity
    calc ‖Tn L κ N z w u (n, m)‖
        = ‖cf κ N n‖ * ‖cf κ N m‖ *
            ‖limSeq (n + 1) (m + 1) (orderedKernel L (n + 1) z) (orderedKernel L (m + 1) w) u N‖ := by
          unfold Tn
          rw [norm_mul, norm_mul]
      _ ≤ κ ^ (n + 1) * κ ^ (m + 1) *
            (2 * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) * ‖orderedKernel L (n + 1) z‖ *
              ‖orderedKernel L (m + 1) w‖) :=
          mul_le_mul (mul_le_mul hc1 hc2 (norm_nonneg _) (pow_nonneg hκ _)) hl
            (norm_nonneg _) (mul_nonneg (pow_nonneg hκ _) (pow_nonneg hκ _))
      _ = (κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖) * (κ ^ (m + 1) * ‖orderedKernel L (m + 1) w‖) *
            (2 * (((n : ℝ) + 1)) * ((m : ℝ) + 1)) := by push_cast; ring
      _ ≤ (2 * (κ / z.im) ^ (n + 1)) * (2 * (κ / w.im) ^ (m + 1)) *
            (2 * (((n : ℝ) + 1)) * ((m : ℝ) + 1)) := by
          refine mul_le_mul (mul_le_mul hα hβ hnB (by positivity)) le_rfl ?_ (by positivity)
          positivity
      _ = 8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) *
            (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) := by ring
  · have h0 : Tn L κ N z w u (n, m) = 0 := by
      show cf κ N n * cf κ N m * limSeq (n + 1) (m + 1) (orderedKernel L (n + 1) z)
        (orderedKernel L (m + 1) w) u N = 0
      unfold limSeq
      rw [dif_neg h1, mul_zero]
    rw [h0, norm_zero]
    exact hRHS

/-- **Double limit of the scaled commutator expectations** (the zero-bracket identity before the series
interchange). For `0 ≤ κ < Im z`, `κ < Im w` and a unit `u`:
`Σ'_{(n,m)} κ^{n+1} κ^{m+1} pbC(K_{n+1,z}, K_{m+1,w})(u) = 0`. -/
theorem double_limit_zero (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im)
    (u : L2T L) (hu : ‖u‖ = 1) :
    ∑' nm : ℕ × ℕ, ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
      pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
        (kernelProductSymbol (orderedKernel L (nm.2 + 1) w)) u = 0 := by
  have hκ0 : 0 ≤ κ := hκ.le
  have hη : 0 < z.im := lt_of_le_of_lt hκ0 hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ0 hw
  have hr : 0 ≤ κ / z.im := div_nonneg hκ0 hη.le
  have hr' : 0 ≤ κ / w.im := div_nonneg hκ0 hη'.le
  have hr1 : κ / z.im < 1 := (div_lt_one hη).mpr hz
  have hr1' : κ / w.im < 1 := (div_lt_one hη').mpr hw
  have hsf := summable_aux (κ / z.im) hr hr1
  have hsg := summable_aux (κ / w.im) hr' hr1'
  have hsum : Summable (fun nm : ℕ × ℕ => 8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
      (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1)))) :=
    ((hsf.mul_of_nonneg hsg
      (fun n => mul_nonneg (by positivity) (pow_nonneg hr _))
      (fun m => mul_nonneg (by positivity) (pow_nonneg hr' _))).mul_left 8)
  have hpt : ∀ nm : ℕ × ℕ, Tendsto (fun N : ℕ => Tn L κ N z w u nm) atTop
      (𝓝 (((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
          (kernelProductSymbol (orderedKernel L (nm.2 + 1) w)) u)) := by
    intro nm
    exact ((cf_tendsto κ nm.1).mul (cf_tendsto κ nm.2)).mul
      (root_overlap_limit (nm.1 + 1) (nm.2 + 1) (orderedKernel L (nm.1 + 1) z)
        (orderedKernel L (nm.2 + 1) w) u hu)
  have hbd : ∀ᶠ N : ℕ in atTop, ∀ nm : ℕ × ℕ, ‖Tn L κ N z w u nm‖ ≤
      8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
        (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1))) :=
    eventually_atTop.2 ⟨1, fun N hN nm => norm_Tn_le L κ hκ0 N (by omega) z w hz hw u hu nm⟩
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpt hbd
  have hz0 : Tendsto (fun N : ℕ => ∑' nm : ℕ × ℕ, Tn L κ N z w u nm) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (tsum_Tn_eq_zero L κ hκ z w u hu N (by omega)).symm
  exact (tendsto_nhds_unique hz0 hlim).symm

end QuantumNLS.RootInvolutionLimit

#print axioms QuantumNLS.RootInvolutionLimit.norm_limSeq_le
#print axioms QuantumNLS.RootInvolutionLimit.fallR_tendsto
#print axioms QuantumNLS.RootInvolutionLimit.cf_tendsto
#print axioms QuantumNLS.RootInvolutionLimit.norm_Tn_le
#print axioms QuantumNLS.RootInvolutionLimit.double_limit_zero
