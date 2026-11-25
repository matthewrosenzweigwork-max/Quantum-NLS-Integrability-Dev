import QuantumNLS.PhysicalQuantumMeasure
import QuantumNLS.FullMass
import QuantumNLS.L2SpatialTransfer

/-! Literal normalization compatibility of the canonical quantum measure,
product symbol, and actual L2 spatial transfer. No spatial/quantum symbol
identification or boundary extension is assumed or claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
namespace QuantumNLS.PhysicalL2Normalization
open PhysicalTensor (L2T)
open ProductPreparation PhysicalQuantumMeasure
open SpatialTransfer L1SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L κ : ℝ} [Fact (0 < L)]

/-- The two existing literal unit normalizations coincide. -/
theorem unitProfile_eq_unitDir (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    (preparation hκ u hu).unitProfile = FullMass.unitDir u := by
  rw [PositiveMassPreparation.unitProfile,
    PositiveMassPreparation.sqrt_mass_eq_norm]
  change (‖u‖⁻¹ : ℝ) • u = ((‖u‖⁻¹ : ℝ) : ℂ) • u
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

/-- The canonical quantum measure is the previously constructed full-mass law. -/
theorem measure_eq_Mmeas (hκ : 0 < κ) (u : L2T L) :
    measure hκ u = FullMass.Mmeas κ u := by
  by_cases hu : u = 0
  · subst u; rw [measure_zero, FullMass.Mmeas_zero]
  · rw [measure_eq_scaled hκ hu, FullMass.Mmeas_of_ne κ hu]
    congr 1
    apply congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ))
    symm
    apply unitLaw_unique (preparation hκ u hu)
    simpa only [effectiveCoupling_eq, unitProfile_eq_unitDir] using
      (FreeLimit.muKappa_spec (FullMass.unitDir u) (FullMass.norm_unitDir hu)
        (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hu))))

/-- Exact mass rescaling of the physical product symbol, at every spectral point. -/
theorem productSymbol_normalization (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (z : ℂ) :
    NormalizedTransfer.productSymbol L (preparation hκ u hu).effectiveCoupling
        (preparation hκ u hu).unitProfile z =
      NormalizedTransfer.productSymbol L κ u z := by
  rw [effectiveCoupling_eq, unitProfile_eq_unitDir]
  exact (FullMass.productSymbol_unit κ hu z).symm

/-- The actual quantum phase has the physical, unnormalized product symbol
as its cosine on the proved high half-plane. -/
theorem cosine_physical_productSymbol (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {z : ℂ}
    (hz : RootMeasureComplex.HighHalf L (κ * ‖u‖ ^ 2) z) :
    2 * Complex.cos (SpatialTransfer.boundaryPhase L κ (measure hκ u) z) =
      Complex.exp (-(Complex.I * z * L / 2)) * NormalizedTransfer.productSymbol L κ u z := by
  rw [← productSymbol_normalization hκ hu z]
  exact cosine_productSymbol hκ hu hz

/-- Canonical L2 representatives respect real scalar multiplication almost everywhere. -/
theorem profile_real_smul_ae (c : ℝ) (u : L2T L) :
    L2SpatialTransfer.profile (c • u) =ᵐ[volume.restrict (Icc (0 : ℝ) L)]
      fun x => (c : ℂ) * L2SpatialTransfer.profile u x := by
  have hh : (fun y : AddCircle L => (c : ℂ) * u y) =ᵐ[volume] (c • u : L2T L) := by
    filter_upwards [Lp.coeFn_smul c u] with y hy
    simpa only [Pi.smul_apply, Complex.real_smul] using hy.symm
  exact (L2SpatialTransfer.profile_ae_of_representative (c • u) hh).symm

/-- The balanced coefficient is unchanged by the source mass normalization. -/
theorem normalized_coefficient_ae (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (z : ℂ) :
    balCoef (preparation hκ u hu).effectiveCoupling
        (L2SpatialTransfer.profile (preparation hκ u hu).unitProfile) z
      =ᵐ[volume.restrict (Icc (0 : ℝ) L)] balCoef κ (L2SpatialTransfer.profile u) z := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hs : Real.sqrt (κ * ‖u‖ ^ 2) = Real.sqrt κ * ‖u‖ := by
    rw [Real.sqrt_mul hκ.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hn.le]
  have hh : (preparation hκ u hu).unitProfile = (‖u‖⁻¹ : ℝ) • u := by
    rw [PositiveMassPreparation.unitProfile, PositiveMassPreparation.sqrt_mass_eq_norm]
    rfl
  rw [effectiveCoupling_eq, hh]
  filter_upwards [profile_real_smul_ae (‖u‖⁻¹) u] with x hx
  have hc : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balCoef, coef, hx, hs] <;> field_simp [hc]

/-- The source mass normalization leaves every entry of the actual L2 transfer unchanged. -/
theorem spatialTransfer_normalization (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    L2SpatialTransfer.spatialTransfer (preparation hκ u hu).effectiveCoupling
        (preparation hκ u hu).unitProfile z x = L2SpatialTransfer.spatialTransfer κ u z x :=
  transfer_eq_of_ae (Fact.out : 0 < L).le (normalized_coefficient_ae hκ hu z) hx

/-- In particular the physical L2 discriminant has the same normalization as the quantum symbol. -/
theorem discriminant_normalization (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (z : ℂ) :
    L2SpatialTransfer.discriminant (preparation hκ u hu).effectiveCoupling
        (preparation hκ u hu).unitProfile z = L2SpatialTransfer.discriminant κ u z := by
  unfold L2SpatialTransfer.discriminant
  rw [spatialTransfer_normalization hκ hu z ⟨(Fact.out : 0 < L).le, le_rfl⟩]

end QuantumNLS.PhysicalL2Normalization

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalL2Normalization.unitProfile_eq_unitDir
#print axioms QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas
#print axioms QuantumNLS.PhysicalL2Normalization.productSymbol_normalization
#print axioms QuantumNLS.PhysicalL2Normalization.cosine_physical_productSymbol
#print axioms QuantumNLS.PhysicalL2Normalization.profile_real_smul_ae
#print axioms QuantumNLS.PhysicalL2Normalization.normalized_coefficient_ae
#print axioms QuantumNLS.PhysicalL2Normalization.spatialTransfer_normalization
#print axioms QuantumNLS.PhysicalL2Normalization.discriminant_normalization

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalL2Normalization." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
