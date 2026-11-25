import QuantumNLS.PeriodSpatialR42b
import QuantumNLS.RootDensityIdentification

/-! The actual quantum law under period change, using its unconditional
continuous density and the actual L2 discriminant transport. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.PeriodMeasureR42b
open PhysicalTensor (L2T)
open PeriodFieldR42b PeriodSpatialR42b
open RootDensityIdentification (dens)
open EmpiricalRapidity (cauchyTransform)
variable {L κ : ℝ} [Fact (0 < L)]

theorem density_scale (hκ : 0 < κ) (u : L2T L) (t : ℝ) :
    dens (κ*L) (period L u) t = L⁻¹ * dens κ u (t/L) := by
  unfold dens
  rw [discriminant_scale hκ u]
  push_cast
  ring

theorem map_density {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) (hg : Measurable g) :
    (volume.withDensity (fun t => ENNReal.ofReal (g t))).map (fun t => c*t) =
      volume.withDensity (fun t => ENNReal.ofReal (c⁻¹*g (t/c))) := by
  have hf : Measurable (fun t : ℝ => c*t) := measurable_const_mul c
  have hgd : Measurable (fun t : ℝ => ENNReal.ofReal (g (t/c))) :=
    ENNReal.measurable_ofReal.comp (hg.comp (measurable_id.div_const c))
  calc
    _ = (volume.map (fun t : ℝ => c*t)).withDensity (fun t => ENNReal.ofReal (g (t/c))) := by
      ext s hs
      rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
        withDensity_apply _ hs, setLIntegral_map hs hgd hf]
      congr 1
      funext t
      rw [mul_div_cancel_left₀ t hc.ne']
    _ = _ := by
      rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc), withDensity_smul_measure,
        ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]

/-- Pushforward of the canonical full-mass quantum law, including vacuum. -/
theorem measure_scale (hκ : 0 < κ) (u : L2T L) :
    PhysicalQuantumMeasure.measure (mul_pos hκ (Fact.out : 0 < L)) (period L u) =
      (PhysicalQuantumMeasure.measure hκ u).map (fun t => L*t) := by
  have hL : 0 < L := Fact.out
  by_cases hu : u = 0
  · have hp : period L u = 0 := by
      apply norm_eq_zero.mp
      rw [norm_period, hu, norm_zero]
    rw [hp, hu, PhysicalQuantumMeasure.measure_zero, PhysicalQuantumMeasure.measure_zero, Measure.map_zero]
  · have hp : period L u ≠ 0 := by
      intro hp
      have hn := norm_period L u
      rw [hp, norm_zero] at hn
      exact hu (norm_eq_zero.mp hn.symm)
    rw [RootDensityIdentification.root_density (mul_pos hκ hL) hp,
      RootDensityIdentification.root_density hκ hu,
      map_density hL _ (RootDensityIdentification.continuous_dens κ u).measurable]
    congr 1
    funext t
    rw [density_scale hκ u t]

/-- Literal Cauchy-transform conversion at every spectral parameter. -/
theorem cauchy_map (μ : Measure ℝ) (z : ℂ) :
    cauchyTransform (μ.map (fun t => L*t)) z =
      (L:ℂ)⁻¹ * cauchyTransform μ (z/(L:ℂ)) := by
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne'
  have hm : MeasurableEmbedding (fun t : ℝ => L*t) := by
    simpa only [Homeomorph.coe_mulLeft₀] using
      (Homeomorph.mulLeft₀ L (Fact.out : 0 < L).ne').isClosedEmbedding.measurableEmbedding
  unfold cauchyTransform
  rw [hm.integral_map, ← integral_const_mul]
  congr 1
  funext t
  have he : z-((L*t:ℝ):ℂ) = (L:ℂ)*(z/(L:ℂ)-(t:ℂ)) := by
    push_cast
    field_simp
  rw [he, mul_inv_rev]
  ring

theorem phase_scale (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    SpatialTransfer.boundaryPhase 1 (κ*L)
      (PhysicalQuantumMeasure.measure (mul_pos hκ (Fact.out : 0 < L)) (period L u)) z =
      SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) (z/(L:ℂ)) := by
  rw [measure_scale hκ u]
  unfold SpatialTransfer.boundaryPhase
  rw [cauchy_map]
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne'
  push_cast
  field_simp

/-- The selected boundary phase has the same labels after spectral dilation. -/
theorem boundary_scale (hκ : 0 < κ) (u : L2T L) (x : ℝ) :
    PhysicalContinuousBoundary.boundary (mul_pos hκ (Fact.out : 0 < L)) (period L u) x =
      PhysicalContinuousBoundary.boundary hκ u (x/L) := by
  have hL : 0 < L := Fact.out
  have ht := (PhysicalSourceFinal.sourceFacts hκ u).boundary (x/L)
  have hb := (PhysicalSourceFinal.sourceFacts (mul_pos hκ hL) (period L u)).boundary x
  have hd : Tendsto (fun ε : ℝ => ε/L) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const L).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε hL
  have he : (fun ε : ℝ => SpatialTransfer.boundaryPhase 1 (κ*L)
      (PhysicalQuantumMeasure.measure (mul_pos hκ hL) (period L u)) ((x:ℂ)+(ε:ℂ)*Complex.I)) =
      (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u)
        (((x/L:ℝ):ℂ)+((ε/L:ℝ):ℂ)*Complex.I)) := by
    funext ε
    rw [phase_scale hκ u]
    congr 1
    push_cast
    ring
  change Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase 1 (κ*L)
    (PhysicalQuantumMeasure.measure (mul_pos hκ hL) (period L u)) ((x:ℂ)+(ε:ℂ)*Complex.I))
    (𝓝[>] 0) (𝓝 _) at hb
  rw [he] at hb
  exact tendsto_nhds_unique hb (ht.comp hd)

theorem separator_scale (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    RootIndexedPhase.separator (mul_pos hκ (Fact.out : 0 < L)) (period L u) n =
      L*RootIndexedPhase.separator hκ u n := by
  apply Eq.symm
  apply (PhysicalSourceFinal.sourceFacts (mul_pos hκ (Fact.out : 0 < L)) (period L u)).phase.separator_unique
  change (PhysicalContinuousBoundary.boundary _ _ _).re = _
  rw [boundary_scale hκ u, mul_div_cancel_left₀ _ (Fact.out : 0 < L).ne']
  exact (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec n

/-- All actual indexed actions agree, with their integer labels unchanged. -/
theorem masses_scale (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    (RootIndexedMasses.masses (mul_pos hκ (Fact.out : 0 < L)) (period L u)).1 n =
      (RootIndexedMasses.masses hκ u).1 n := by
  change (PhysicalQuantumMeasure.measure _ (period L u) (Ioo
    (RootIndexedPhase.separator _ (period L u) (n-1))
    (RootIndexedPhase.separator _ (period L u) n))).toReal = _
  rw [measure_scale hκ u, separator_scale hκ u, separator_scale hκ u,
    Measure.map_apply (measurable_const_mul L) measurableSet_Ioo,
    preimage_const_mul_Ioo₀ _ _ (Fact.out : 0 < L),
    mul_div_cancel_left₀ _ (Fact.out : 0 < L).ne',
    mul_div_cancel_left₀ _ (Fact.out : 0 < L).ne']
  rfl

end QuantumNLS.PeriodMeasureR42b

#print axioms QuantumNLS.PeriodMeasureR42b.density_scale
#print axioms QuantumNLS.PeriodMeasureR42b.map_density
#print axioms QuantumNLS.PeriodMeasureR42b.measure_scale
#print axioms QuantumNLS.PeriodMeasureR42b.cauchy_map
#print axioms QuantumNLS.PeriodMeasureR42b.phase_scale
#print axioms QuantumNLS.PeriodMeasureR42b.boundary_scale
#print axioms QuantumNLS.PeriodMeasureR42b.separator_scale
#print axioms QuantumNLS.PeriodMeasureR42b.masses_scale

-- R42b final aggregate audit
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PeriodMeasureR42b." ||
        n.toString.startsWith "_private.QuantumNLS.PeriodMeasureR42b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R42b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
