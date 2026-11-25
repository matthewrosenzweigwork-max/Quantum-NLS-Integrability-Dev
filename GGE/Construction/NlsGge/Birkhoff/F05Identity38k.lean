import NlsGge.Birkhoff.F05Identity38j

/-! # F05, file k: packaging of v2 l.655-678 (`B:cor:identity` and the construction before it)

* `F05_construction38` (v2 l.656-669, needs only `B : BirkhoffInput38`): `γ_m` is a probability
  measure carried by `h^{m-1}`, `0 < Z_m ≤ 1`, `μ̂_m`, `μ_m`, `γ_m^F` are probability measures, and
  `Z_m` is the limit of the finite-gap relative partition functions `Z_{m,Λ_N}` of the canonical
  finite-gap ensembles with energy `E_m` (each in `(0,1]`).
* `F05_cor_identity38` (v2 `B:cor:identity`, l.671-678, conditional on `B` and `O`): the identity
  `dμ_m = Z_m⁻¹ e^{-V_m} dγ_m^F`, integrability and `∫ e^{-V_m} dγ_m^F = Z_m ∈ (0,1]`, with the
  normalizer the finite-gap relative partition function (limit statement).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal

section Construction

variable (B : BirkhoffInput38) {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
/-- **v2 l.656-669.** -/
theorem F05_construction38 :
    Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n / finiteHierarchyRate38 m β n) ∧
    IsProbabilityMeasure (gammaM38 m β) ∧
    (∀ᵐ z ∂(gammaM38 m β),
      Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)) ∧
    IsProbabilityMeasure ((gammaM38 m β).map (gaussianRealization38 m)) ∧
    (0 < ZM38 B m β ∧ ZM38 B m β ≤ 1) ∧
    IsProbabilityMeasure (muHatM38 B m β) ∧ IsProbabilityMeasure (muM38 B m β) ∧
    (∀ Λ : Finset ℤ, 0 < ZΛM38 B m β Λ ∧ ZΛM38 B m β Λ ≤ 1) ∧
    Tendsto (fun N : ℕ => ZΛM38 B m β (stdExh38 N)) atTop (𝓝 (ZM38 B m β)) := by
  have hβ0 : ∀ i ≤ m, 0 ≤ β i := fun i hi => (hβ i hi).le
  refine ⟨summable_tailRatio38 m β hm hβ0 (hβ 0 (Nat.zero_le _)) (hβ m le_rfl), inferInstance,
    ae_summable38 hm hβ0 (hβ 0 (Nat.zero_le _)) (hβ m le_rfl), ?_,
    B.ZM38_pos_le_one hm hβ, B.isProbabilityMeasure_muHatM38 hm hβ,
    B.isProbabilityMeasure_muM38 hm hβ, fun Λ => ZΛM38_pos_le_one B m β hm hβ Λ,
    tendsto_ZΛM38 B m β hm hβ⟩
  infer_instance

end Construction

section Identity

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include O hm hβ in
/-- **F05 (v2 `B:cor:identity`).**  Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`.
With `γ_m^F = (𝓕⁻¹)_# γ_m`: `dμ_m = Z_m⁻¹ e^{-V_m} dγ_m^F`, `e^{-V_m}` is `γ_m^F`-integrable with
`∫ e^{-V_m} dγ_m^F = Z_m ∈ (0,1]`, and `Z_m` is the limit of the finite-gap relative partition
functions. -/
theorem F05_cor_identity38 :
    muM38 B m β = (gammaFM38 m β).withDensity
        (fun u => ENNReal.ofReal ((ZM38 B m β)⁻¹ * Real.exp (-(Vm38 m β u)))) ∧
    Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u)) ∂(gammaFM38 m β) = ZM38 B m β ∧
    (0 < ZM38 B m β ∧ ZM38 B m β ≤ 1) ∧
    Tendsto (fun N : ℕ => ZΛM38 B m β (stdExh38 N)) atTop
      (𝓝 (∫ u, Real.exp (-(Vm38 m β u)) ∂(gammaFM38 m β))) := by
  obtain ⟨hZ, hint, hI, hmu⟩ := F05_identity38 B O hm hβ
  refine ⟨hmu, hint, hI, hZ, ?_⟩
  rw [hI]
  exact tendsto_ZΛM38 B m β hm hβ

end Identity

end NlsGge.Birkhoff
