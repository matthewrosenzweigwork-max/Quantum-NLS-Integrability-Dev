import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Sequences

/-! GP-10: compactification with an explicit cemetery mass. The vague topology
is induced by integrals against all real compactly supported continuous tests.
Restriction drops the cemetery atom; no probability mass is inferred from vague
convergence. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped CompactlySupported ZeroAtInfty ENNReal NNReal OnePoint
namespace QuantumNLS.Ext025B2Vague

local instance : MeasurableSpace (OnePoint ℝ) := borel _
local instance : BorelSpace (OnePoint ℝ) := ⟨rfl⟩
local instance : MetrizableSpace (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.metrizableSpace

/-- The same finite Borel measures, equipped below with the vague topology. -/
structure VagueMeasure where
  measure : FiniteMeasure ℝ

def tests (μ : VagueMeasure) (f : C_c(ℝ, ℝ)) : ℝ := ∫ x, f x ∂μ.measure

instance : TopologicalSpace VagueMeasure := TopologicalSpace.induced tests inferInstance

theorem tendsto_iff_tests {ι : Type*} {L : Filter ι} {u : ι → VagueMeasure}
    {μ : VagueMeasure} : Tendsto u L (𝓝 μ) ↔
      ∀ f : C_c(ℝ, ℝ), Tendsto (fun i => ∫ x, f x ∂(u i).measure) L
        (𝓝 (∫ x, f x ∂μ.measure)) := by
  rw [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds]
  rfl

/-- The zero extension to the one-point compactification. -/
def extend (f : C_c(ℝ, ℝ)) : C(OnePoint ℝ, ℝ) :=
  (f : C₀(ℝ, ℝ)).toOnePoint

@[simp] theorem extend_coe (f : C_c(ℝ, ℝ)) (x : ℝ) : extend f x = f x := rfl
@[simp] theorem extend_infty (f : C_c(ℝ, ℝ)) : extend f ∞ = 0 := rfl

/-- Restrict a compactified probability to the real line. -/
def dropInfinity (π : ProbabilityMeasure (OnePoint ℝ)) : VagueMeasure :=
  ⟨π.toFiniteMeasure.comap ((↑) : ℝ → OnePoint ℝ)⟩

theorem integral_dropInfinity (π : ProbabilityMeasure (OnePoint ℝ)) (f : C_c(ℝ, ℝ)) :
    (∫ x, f x ∂(dropInfinity π).measure) = ∫ y, extend f y ∂π := by
  let e := (OnePoint.isOpenEmbedding_coe (X := ℝ)).measurableEmbedding
  change (∫ x : ℝ, extend f (x : OnePoint ℝ) ∂((π : Measure (OnePoint ℝ)).comap ((↑) : ℝ → OnePoint ℝ))) = _
  rw [← e.integral_map, e.map_comap]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have : y = (∞ : OnePoint ℝ) := OnePoint.notMem_range_coe_iff.mp hy
  simp [this]

theorem continuous_dropInfinity : Continuous dropInfinity := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro f
  have h := ProbabilityMeasure.continuous_integral_continuousMap (extend f)
  simpa only [Function.comp_apply, tests, integral_dropInfinity] using h

theorem mass_dropInfinity_le (π : ProbabilityMeasure (OnePoint ℝ)) :
    (dropInfinity π).measure.mass ≤ 1 := by
  exact (FiniteMeasure.mass_comap_le _ _).trans_eq π.mass_toFiniteMeasure

/-- Complete a subprobability by placing exactly its missing mass at infinity. -/
def addInfinity (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    ProbabilityMeasure (OnePoint ℝ) :=
  ⟨(μ : Measure ℝ).map ((↑) : ℝ → OnePoint ℝ) +
    (1 - (μ.mass : ℝ≥0∞)) • Measure.dirac (∞ : OnePoint ℝ), by
    constructor
    rw [Measure.add_apply, Measure.map_apply OnePoint.continuous_coe.measurable
      MeasurableSet.univ]
    simp only [preimage_univ, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← FiniteMeasure.ennreal_mass]
    exact add_tsub_cancel_of_le (by exact_mod_cast hμ)⟩

theorem drop_addInfinity (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    (dropInfinity (addInfinity μ hμ)).measure = μ := by
  apply FiniteMeasure.toMeasure_injective
  ext s hs
  let e := (OnePoint.isOpenEmbedding_coe (X := ℝ)).measurableEmbedding
  change ((μ : Measure ℝ).map ((↑) : ℝ → OnePoint ℝ) +
    (1 - (μ.mass : ℝ≥0∞)) • Measure.dirac (∞ : OnePoint ℝ)).comap _ s = _
  rw [e.comap_apply, Measure.add_apply, e.map_apply]
  simp [e.injective.preimage_image]

/-- Compactness of all subprobabilities in the actual vague topology. -/
theorem «FIN-EXT025-GP-10-compact» :
    IsCompact {μ : VagueMeasure | μ.measure.mass ≤ 1} := by
  have heq : {μ : VagueMeasure | μ.measure.mass ≤ 1} = range dropInfinity := by
    ext μ
    constructor
    · intro hμ
      refine ⟨addInfinity μ.measure hμ, ?_⟩
      cases μ
      exact congrArg VagueMeasure.mk (drop_addInfinity _ hμ)
    · rintro ⟨π, rfl⟩
      exact mass_dropInfinity_le π
  rw [heq]
  exact isCompact_range continuous_dropInfinity

/-- Sequential extraction permits mass to escape to the cemetery point. -/
theorem «FIN-EXT025-GP-10-subprobability» (u : ℕ → FiniteMeasure ℝ)
    (hu : ∀ n, (u n).mass ≤ 1) :
    ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ), μ.mass ≤ 1 ∧ StrictMono φ ∧
      ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂u (φ n)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨π, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun n => addInfinity (u n) (hu n))
  refine ⟨(dropInfinity π).measure, φ, mass_dropInfinity_le π, hφ, ?_⟩
  have ht := tendsto_iff_tests.mp (continuous_dropInfinity.continuousAt.tendsto.comp hlim)
  intro f
  simpa only [Function.comp_apply, drop_addInfinity] using ht f

/-- Scaling acts continuously in the vague topology. -/
def scale (C : ℝ≥0) (μ : VagueMeasure) : VagueMeasure := ⟨C • μ.measure⟩

theorem continuous_scale (C : ℝ≥0) : Continuous (scale C) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro f
  have h : Continuous (fun μ : VagueMeasure => tests μ f) :=
    (continuous_apply f).comp (continuous_induced_dom : Continuous tests)
  change Continuous (fun μ : VagueMeasure => ∫ x, f x ∂(C • μ.measure))
  simp only [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  exact continuous_const.smul h

/-- Full bounded-mass sequential vague compactness on the real line. -/
theorem «FIN-EXT025-GP-10» (C : ℝ≥0) (u : ℕ → FiniteMeasure ℝ)
    (hu : ∀ n, (u n).mass ≤ C) :
    ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ), μ.mass ≤ C ∧ StrictMono φ ∧
      ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂u (φ n)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  by_cases hC : C = 0
  · have hz : ∀ n, u n = 0 := fun n =>
      (FiniteMeasure.mass_zero_iff _).mp (le_antisymm (hC ▸ hu n) bot_le)
    refine ⟨0, id, by simp [hC], strictMono_id, ?_⟩
    intro f
    simp only [hz]
    exact tendsto_const_nhds
  have hCpos : 0 < C := pos_iff_ne_zero.mpr hC
  have hv : ∀ n, (C⁻¹ • u n).mass ≤ 1 := by
    intro n
    simp only [FiniteMeasure.mass, FiniteMeasure.smul_apply, smul_eq_mul]
    exact (inv_mul_le_iff₀ hCpos).mpr (by simpa using hu n)
  obtain ⟨μ, φ, hμ, hφ, hlim⟩ := «FIN-EXT025-GP-10-subprobability»
    (fun n => C⁻¹ • u n) hv
  refine ⟨C • μ, φ, ?_, hφ, ?_⟩
  · change (C • μ) univ ≤ C
    rw [FiniteMeasure.smul_apply]
    exact mul_le_of_le_one_right C.2 hμ
  · intro f
    have ht := (hlim f).const_smul C
    simpa only [← integral_smul_nnreal_measure, ← FiniteMeasure.toMeasure_smul,
      smul_smul, mul_inv_cancel₀ hC, one_smul] using ht

/-- Mass-bounded subprobabilities are compact, at every normalization. -/
theorem «FIN-EXT025-GP-10-compact-mass» (C : ℝ≥0) :
    IsCompact {μ : VagueMeasure | μ.measure.mass ≤ C} := by
  by_cases hC : C = 0
  · have heq : {μ : VagueMeasure | μ.measure.mass ≤ C} = {VagueMeasure.mk 0} := by
      ext μ
      simp only [hC, mem_ofPred_eq, le_zero_iff, FiniteMeasure.mass_zero_iff,
        mem_singleton_iff]
      cases μ
      simp
    rw [heq]
    exact isCompact_singleton
  have hc : 0 < C := pos_iff_ne_zero.mpr hC
  have heq : {μ : VagueMeasure | μ.measure.mass ≤ C} =
      scale C '' {μ : VagueMeasure | μ.measure.mass ≤ 1} := by
    ext μ
    constructor
    · intro hμ
      refine ⟨scale C⁻¹ μ, ?_, ?_⟩
      · change (C⁻¹ • μ.measure).mass ≤ 1
        simp only [FiniteMeasure.mass, FiniteMeasure.smul_apply, smul_eq_mul]
        exact (inv_mul_le_iff₀ hc).mpr (by simpa using hμ)
      · cases μ
        simp [scale, smul_smul, mul_inv_cancel₀ hC]
    · rintro ⟨ν, hν, rfl⟩
      change (C • ν.measure).mass ≤ C
      change (C • ν.measure) univ ≤ C
      rw [FiniteMeasure.smul_apply]
      exact mul_le_of_le_one_right C.2 hν
  rw [heq]
  exact «FIN-EXT025-GP-10-compact».image (continuous_scale C)

end QuantumNLS.Ext025B2Vague

#print axioms QuantumNLS.Ext025B2Vague.tests
#print axioms QuantumNLS.Ext025B2Vague.tendsto_iff_tests
#print axioms QuantumNLS.Ext025B2Vague.extend
#print axioms QuantumNLS.Ext025B2Vague.extend_coe
#print axioms QuantumNLS.Ext025B2Vague.extend_infty
#print axioms QuantumNLS.Ext025B2Vague.dropInfinity
#print axioms QuantumNLS.Ext025B2Vague.integral_dropInfinity
#print axioms QuantumNLS.Ext025B2Vague.continuous_dropInfinity
#print axioms QuantumNLS.Ext025B2Vague.mass_dropInfinity_le
#print axioms QuantumNLS.Ext025B2Vague.addInfinity
#print axioms QuantumNLS.Ext025B2Vague.drop_addInfinity
#print axioms QuantumNLS.Ext025B2Vague.«FIN-EXT025-GP-10-compact»
#print axioms QuantumNLS.Ext025B2Vague.«FIN-EXT025-GP-10-subprobability»
#print axioms QuantumNLS.Ext025B2Vague.scale
#print axioms QuantumNLS.Ext025B2Vague.continuous_scale
#print axioms QuantumNLS.Ext025B2Vague.«FIN-EXT025-GP-10»
#print axioms QuantumNLS.Ext025B2Vague.«FIN-EXT025-GP-10-compact-mass»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B2Vague." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025B2Vague audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
