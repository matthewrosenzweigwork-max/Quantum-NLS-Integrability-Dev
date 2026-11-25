import QuantumNLS.RootPlacementBound
import QuantumNLS.NormalizedTransfer

/-!
# DEF-048 (symbol clause): convergence of the scalar product symbol on `Im z > κ`
(`ROOT_spectral_measure.tex`, `eq:root-symbol`: "The series converges absolutely and locally uniformly")

With the sharp kernel bound `‖K_{r,z}‖ ≤ 2 (Im z)^{-r}` of `RootPlacementBound` (R-FFA8D3F2), the terms of
`s(z;u) = 1 + e^{izL} + Σ_{r≥1} κ^r ⟨u^{⊗r}, K_{r,z} u^{⊗r}⟩` satisfy
`|κ^r ⟨u^{⊗r}, K_{r,z} u^{⊗r}⟩| ≤ 2 (κ/Im z)^r`.  Hence, for `0 ≤ κ < Im z` and unit `u`:
* the series converges absolutely (`summable_norm_symbolTerm`) and `productSymbol` is its sum
  (`hasSum_symbolTerm`);
* on every half-plane `Im z ≥ η₀ > κ` the partial sums converge uniformly (`tendstoUniformlyOn_symbol`), and on
  the open half-plane `Im z > κ` locally uniformly (`tendstoLocallyUniformlyOn_symbol`);
* the tail is `≤ 2 (κ/η)^{n+1}/(1 − κ/η)` (`norm_tail_symbol_le`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace QuantumNLS.RootSymbolConvergence

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
open QuantumNLS.NormalizedTransfer QuantumNLS.RootPlacementBound

variable {L : ℝ} [Fact (0 < L)]

/-- Term bound: `|κ^r ⟨u^{⊗r}, K_{r,z} u^{⊗r}⟩| ≤ 2 (κ/Im z)^r` for `r ≥ 1`, `Im z > 0`. -/
theorem norm_symbolTerm_le (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hη : 0 < z.im) {r : ℕ} (hr : 1 ≤ r) :
    ‖symbolTerm L κ u z r‖ ≤ 2 * (κ / z.im) ^ r := by
  have hK := norm_physicalKernel_le (L := L) hr z hη
  have hw : ‖QuantumNLS.HighMomentsOps.wvec r u‖ = 1 := QuantumNLS.HighMomentsFinal.norm_wvec u hu r
  have hk : ‖kernelProductSymbol (orderedKernel L r z) u‖ ≤ 2 * (z.im)⁻¹ ^ r := by
    have h1 : kernelProductSymbol (orderedKernel L r z) u =
        ⟪QuantumNLS.HighMomentsOps.wvec r u,
          orderedKernel L r z (QuantumNLS.HighMomentsOps.wvec r u)⟫_ℂ := rfl
    rw [h1]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hw, one_mul]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [hw, mul_one]
    exact hK
  unfold symbolTerm
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ r)]
  calc κ ^ r * ‖kernelProductSymbol (orderedKernel L r z) u‖ ≤ κ ^ r * (2 * (z.im)⁻¹ ^ r) :=
        mul_le_mul_of_nonneg_left hk (pow_nonneg hκ r)
    _ = 2 * (κ / z.im) ^ r := by rw [div_pow, div_eq_mul_inv (κ ^ r), inv_pow]; ring

theorem summable_geom (κ η : ℝ) (hκ : 0 ≤ κ) (h : κ < η) :
    Summable (fun j : ℕ => 2 * (κ / η) ^ (j + 1)) := by
  have hη : 0 < η := lt_of_le_of_lt hκ h
  have h1 : κ / η < 1 := (div_lt_one hη).mpr h
  have h0 : 0 ≤ κ / η := div_nonneg hκ hη.le
  have := (summable_geometric_of_lt_one h0 h1).mul_left (2 * (κ / η))
  refine this.congr (fun j => ?_)
  ring

/-- **Absolute convergence** of the symbol series on `Im z > κ`. -/
theorem summable_norm_symbolTerm (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : κ < z.im) : Summable (fun j : ℕ => ‖symbolTerm L κ u z (j + 1)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_symbolTerm_le κ hκ u hu z (lt_of_le_of_lt hκ hz) (by omega))
    (summable_geom κ z.im hκ hz)

theorem hasSum_symbolTerm (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : κ < z.im) :
    HasSum (fun j : ℕ => symbolTerm L κ u z (j + 1))
      (productSymbol L κ u z - 1 - Complex.exp (Complex.I * z * L)) := by
  have h := (summable_norm_symbolTerm κ hκ u hu z hz).of_norm.hasSum
  unfold productSymbol
  have : (1 + Complex.exp (Complex.I * z * L) + ∑' j : ℕ, symbolTerm L κ u z (j + 1)) - 1 -
      Complex.exp (Complex.I * z * L) = ∑' j : ℕ, symbolTerm L κ u z (j + 1) := by ring
  rw [this]
  exact h

/-- Tail bound of the series. -/
theorem norm_tail_symbol_le (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ)
    (hz : κ < z.im) (n : ℕ) :
    ‖∑' j : ℕ, symbolTerm L κ u z (j + n + 1)‖ ≤
      2 * (κ / z.im) ^ (n + 1) / (1 - κ / z.im) := by
  have hη : 0 < z.im := lt_of_le_of_lt hκ hz
  have h1 : κ / z.im < 1 := (div_lt_one hη).mpr hz
  have h0 : 0 ≤ κ / z.im := div_nonneg hκ hη.le
  have hg : HasSum (fun j : ℕ => 2 * (κ / z.im) ^ (j + n + 1))
      (2 * (κ / z.im) ^ (n + 1) / (1 - κ / z.im)) := by
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left (2 * (κ / z.im) ^ (n + 1))
    convert this using 1
    · funext j; ring
    · field_simp
  exact tsum_of_norm_bounded hg (fun j => norm_symbolTerm_le κ hκ u hu z hη (by omega))

/-- Uniform convergence of the partial sums on `Im z ≥ η₀ > κ`. -/
theorem tendstoUniformlyOn_symbol (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) (η₀ : ℝ)
    (h : κ < η₀) :
    TendstoUniformlyOn (fun (N : ℕ) (z : ℂ) => ∑ j ∈ Finset.range N, symbolTerm L κ u z (j + 1))
      (fun z => ∑' j : ℕ, symbolTerm L κ u z (j + 1)) atTop {z : ℂ | η₀ ≤ z.im} := by
  refine tendstoUniformlyOn_tsum_nat (summable_geom κ η₀ hκ h) (fun n z hz => ?_)
  have hη : η₀ ≤ z.im := hz
  have hz0 : 0 < z.im := lt_of_le_of_lt hκ (lt_of_lt_of_le h hη)
  refine (norm_symbolTerm_le κ hκ u hu z hz0 (by omega)).trans ?_
  have hη0 : 0 < η₀ := lt_of_le_of_lt hκ h
  have : κ / z.im ≤ κ / η₀ := div_le_div_of_nonneg_left hκ hη0 hη
  have := pow_le_pow_left₀ (div_nonneg hκ hz0.le) this (n + 1)
  linarith

/-- **Local uniform convergence** of the symbol series on the open half-plane `Im z > κ`. -/
theorem tendstoLocallyUniformlyOn_symbol (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (hu : ‖u‖ = 1) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (z : ℂ) => ∑ j ∈ Finset.range N, symbolTerm L κ u z (j + 1))
      (fun z => ∑' j : ℕ, symbolTerm L κ u z (j + 1)) atTop {z : ℂ | κ < z.im} := by
  intro v hv x hx
  have hx' : κ < x.im := hx
  set η₀ := (κ + x.im) / 2 with hη₀
  have hκη : κ < η₀ := by rw [hη₀]; linarith
  have hη₀x : η₀ < x.im := by rw [hη₀]; linarith
  refine ⟨{z : ℂ | η₀ ≤ z.im}, ?_, tendstoUniformlyOn_symbol κ hκ u hu η₀ hκη v hv⟩
  apply mem_nhdsWithin_of_mem_nhds
  have hopen : IsOpen {z : ℂ | η₀ < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact Filter.mem_of_superset (hopen.mem_nhds hη₀x) (fun z (hz : η₀ < z.im) => show η₀ ≤ z.im from le_of_lt hz)

#print axioms norm_symbolTerm_le
#print axioms summable_norm_symbolTerm
#print axioms hasSum_symbolTerm
#print axioms tendstoLocallyUniformlyOn_symbol

end QuantumNLS.RootSymbolConvergence
