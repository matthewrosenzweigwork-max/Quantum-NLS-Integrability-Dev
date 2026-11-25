import QuantumNLS.PhysicalTensor

/-!
# R-36C23346 clause (c), Part C-2a: pure-state marginal bound `‖γ^{(k)}_{Uψ} − γ^{(k)}_ψ‖₁ ≤ 2‖(U−1)ψ‖`

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex` (clause (c) of `QG:lem:haar-linear-tail`, marginal estimate).
Realized objects used read-only (frozen): `TraceClass.traceNorm_reducedDensity_sub_le` (stability of reduced densities,
`‖γ_ψ − γ_φ‖₁ ≤ ‖ψ − φ‖ (‖ψ‖ + ‖φ‖)`), `PhysicalTensor.reducedDensityN` (DEF-030 partial trace over the last `N − k`
factors), `PhysicalTensor.physUnitary` (U2 bridge `(L²𝕋)^{⊗̂N} ≃ₗᵢ L²(𝕋^N)`).

Proved here (standard axioms only):
* `traceNorm_reducedDensityN_sub_le`: `‖γ^{(k)}_ψ − γ^{(k)}_φ‖₁ ≤ ‖ψ − φ‖ (‖ψ‖ + ‖φ‖)` in every sector `N`.
* `traceNorm_reducedDensityN_isometry_sub_le`: for a linear isometry `U` and unit `ψ`,
  `‖γ^{(k)}_{Uψ} − γ^{(k)}_ψ‖₁ ≤ 2 ‖(U − 1)ψ‖`; real-valued form `toReal_traceNorm_reducedDensityN_isometry_sub_le`.
* `traceNorm_physMarginal_isometry_sub_le`: the same bound on the physical carrier `L²(𝕋_L^N)`, with
  `γ^{(k)}_F := reducedDensityN N k hk (physUnitary.symm F)` (`physMarginal`).

Clause (c) remains OPEN (step (2) N-uniform generator bound and step (3) kinetic compactness); see the report.
-/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.PhysicalTensor

namespace QuantumNLS.MarginalPureState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Stability of the DEF-030 marginal in sector `N`: `‖γ^{(k)}_ψ − γ^{(k)}_φ‖₁ ≤ ‖ψ − φ‖ (‖ψ‖ + ‖φ‖)`. -/
theorem traceNorm_reducedDensityN_sub_le (N k : ℕ) (hk : k ≤ N)
    (ψ φ : HilbertTensorPower ℂ E N) :
    traceNorm (reducedDensityN N k hk ψ - reducedDensityN N k hk φ) ≤
      ENNReal.ofReal (‖ψ - φ‖ * (‖ψ‖ + ‖φ‖)) := by
  have h := traceNorm_reducedDensity_sub_le
    (splitIsometry k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm ψ))
    (splitIsometry k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm φ))
  have key : ∀ a b : HilbertTensorPower ℂ E N,
      ‖splitIsometry k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm a) -
        splitIsometry k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm b)‖ = ‖a - b‖ := by
    intro a b
    rw [← map_sub, LinearIsometryEquiv.norm_map, ← map_sub, LinearIsometryEquiv.norm_map]
  have hna : ‖splitIsometry k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm ψ)‖ = ‖ψ‖ := by
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  have hnb : ‖splitIsometry k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm φ)‖ = ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  rw [key ψ φ, hna, hnb] at h
  unfold reducedDensityN reducedDensityPower
  exact h

/-- **Pure-state marginal bound.** For a unit vector `ψ` and a linear isometry `U`,
`‖γ^{(k)}_{Uψ} − γ^{(k)}_ψ‖₁ ≤ 2 ‖(U − 1)ψ‖`. -/
theorem traceNorm_reducedDensityN_isometry_sub_le (N k : ℕ) (hk : k ≤ N)
    (U : HilbertTensorPower ℂ E N →L[ℂ] HilbertTensorPower ℂ E N)
    (hU : ∀ x, ‖U x‖ = ‖x‖) (ψ : HilbertTensorPower ℂ E N) (hψ : ‖ψ‖ = 1) :
    traceNorm (reducedDensityN N k hk (U ψ) - reducedDensityN N k hk ψ) ≤
      ENNReal.ofReal (2 * ‖(U - ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E N)) ψ‖) := by
  refine (traceNorm_reducedDensityN_sub_le N k hk (U ψ) ψ).trans (le_of_eq ?_)
  rw [hU ψ, hψ, sub_apply, ContinuousLinearMap.id_apply, norm_sub_rev]
  ring_nf

/-- Real-valued form of the pure-state bound: `‖γ^{(k)}_{Uψ} − γ^{(k)}_ψ‖₁ ≤ 2 ‖(U − 1)ψ‖` (as reals). -/
theorem toReal_traceNorm_reducedDensityN_isometry_sub_le (N k : ℕ) (hk : k ≤ N)
    (U : HilbertTensorPower ℂ E N →L[ℂ] HilbertTensorPower ℂ E N)
    (hU : ∀ x, ‖U x‖ = ‖x‖) (ψ : HilbertTensorPower ℂ E N) (hψ : ‖ψ‖ = 1) :
    (traceNorm (reducedDensityN N k hk (U ψ) - reducedDensityN N k hk ψ)).toReal ≤
      2 * ‖(U - ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E N)) ψ‖ :=
  ENNReal.toReal_le_of_le_ofReal (mul_nonneg zero_le_two (norm_nonneg _))
    (traceNorm_reducedDensityN_isometry_sub_le N k hk U hU ψ hψ)

end QuantumNLS.MarginalPureState

section Physical

open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.PhysicalTensor
  QuantumNLS.MarginalPureState

variable (L : ℝ) [Fact (0 < L)]

namespace QuantumNLS.MarginalPureState

/-- The physical marginal of `F ∈ L²(𝕋_L^N)`: `γ^{(k)}_F := γ^{(k)}_{physUnitary⁻¹ F}`. -/
def physMarginal (N k : ℕ) (hk : k ≤ N) (F : L2TN L N) :
    HilbertTensorPower ℂ (L2T L) k →L[ℂ] HilbertTensorPower ℂ (L2T L) k :=
  reducedDensityN N k hk ((physUnitary (L := L) (N := N)).symm F)

/-- Physical pure-state bound on `L²(𝕋_L^N)`: for an isometry `U` of `L²(𝕋_L^N)` and a unit `F`,
`‖γ^{(k)}_{UF} − γ^{(k)}_F‖₁ ≤ 2 ‖UF − F‖`. -/
theorem traceNorm_physMarginal_isometry_sub_le (N k : ℕ) (hk : k ≤ N)
    (U : L2TN L N →L[ℂ] L2TN L N) (hU : ∀ x, ‖U x‖ = ‖x‖) (F : L2TN L N) (hF : ‖F‖ = 1) :
    traceNorm (physMarginal L N k hk (U F) - physMarginal L N k hk F) ≤
      ENNReal.ofReal (2 * ‖U F - F‖) := by
  unfold physMarginal
  have hψ : ‖(physUnitary (L := L) (N := N)).symm F‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, hF]
  -- transport `U` to the tensor power through the isometry `physUnitary`
  let V : HilbertTensorPower ℂ (L2T L) N →L[ℂ] HilbertTensorPower ℂ (L2T L) N :=
    (physUnitary (L := L) (N := N)).symm.toLinearIsometry.toContinuousLinearMap.comp
      (U.comp (physUnitary (L := L) (N := N)).toLinearIsometry.toContinuousLinearMap)
  have hV : ∀ x, ‖V x‖ = ‖x‖ := by
    intro x
    simp only [V, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map, hU]
  have hVψ : V ((physUnitary (L := L) (N := N)).symm F) =
      (physUnitary (L := L) (N := N)).symm (U F) := by
    simp only [V, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
  have key := traceNorm_reducedDensityN_isometry_sub_le N k hk V hV
    ((physUnitary (L := L) (N := N)).symm F) hψ
  rw [hVψ] at key
  refine key.trans (le_of_eq ?_)
  congr 2
  rw [sub_apply, ContinuousLinearMap.id_apply, hVψ, ← map_sub, LinearIsometryEquiv.norm_map]

end QuantumNLS.MarginalPureState

end Physical

#print axioms QuantumNLS.MarginalPureState.traceNorm_reducedDensityN_sub_le
#print axioms QuantumNLS.MarginalPureState.traceNorm_reducedDensityN_isometry_sub_le
#print axioms QuantumNLS.MarginalPureState.toReal_traceNorm_reducedDensityN_isometry_sub_le
#print axioms QuantumNLS.MarginalPureState.traceNorm_physMarginal_isometry_sub_le
