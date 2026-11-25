import QuantumNLS.MonotoneIndexedMasses

/-!
New consumers of the faithful DEF-014 phase. The frozen IndexedMasses and
IndexedMassProperness interfaces are left unchanged. This supplies the
nonnegative ell1 map and the LOCAL-022 reset-normalization specialization
without requiring the physical boundary phase to be globally StrictMono.
All measure/phase families and chart hypotheses are explicit parameters.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.MonotoneMassConsumers
open QuantumNLS.MonotoneIndexedMasses QuantumNLS.ActionTorus
open QuantumNLS.ResetNormalizationUniqueness

/-- Selected real boundary phase with the faithful monotone interface. -/
structure SelectedPhase (L κ : ℝ) (M : Measure ℝ) extends BoundaryPhase where
  boundary : QuantumNLS.IndexedMasses.IsBoundaryRealPart L κ M φ

/-- Parametric data on every physical L2 input, with no global strict phase hypothesis. -/
structure MassData (L κ : ℝ) [Fact (0 < L)] where
  M : QuantumNLS.PhysicalTensor.L2T L → Measure ℝ
  finite : ∀ u, IsFiniteMeasure (M u)
  phase : ∀ u, SelectedPhase L κ (M u)

variable {L κ : ℝ} [Fact (0 < L)]

def massMap (D : MassData L κ) (u : QuantumNLS.PhysicalTensor.L2T L) : PosL1 := by
  letI := D.finite u
  exact (D.phase u).toBoundaryPhase.massVector (D.M u)

/-- The map has the source's literal interval-mass coordinates. -/
theorem massMap_apply (D : MassData L κ) (u : QuantumNLS.PhysicalTensor.L2T L) (n : ℤ) :
    (massMap D u).1 n =
      ((D.M u) (Ioo ((D.phase u).separator (n - 1)) ((D.phase u).separator n))).toReal := rfl

/-- Chart-mass correspondence transfers directly to the faithful mass map. -/
theorem chartMasses_iff (D : MassData L κ)
    (Φ : QuantumNLS.PhysicalTensor.L2T L → S2 ℤ) :
    QuantumNLS.IndexedMasses.ChartMasses Φ (fun n u => (massMap D u).1 n) ↔
      ∀ u, Φ u ∈ actionTorus (massMap D u) :=
  QuantumNLS.ActionTorus.chartMasses_iff_mem_actionTorus Φ (massMap D)

/-- DEF-018's definition also transfers to this mass map (properness is not proved). -/
def MassProper (D : MassData L κ) : Prop :=
  ∀ K : Set PosL1, IsCompact K → IsCompact (massMap D ⁻¹' K)

def actionFibre (D : MassData L κ) (a : PosL1) : Set (QuantumNLS.PhysicalTensor.L2T L) :=
  massMap D ⁻¹' {a}

theorem isCompact_fibre {D : MassData L κ} (hD : MassProper D) (a : PosL1) :
    IsCompact (actionFibre D a) := hD {a} isCompact_singleton

/-- LOCAL-022 reset-normalization specialization using monotone DEF-014 phases. -/
theorem reset_normalization_uniqueness (L : ℝ) [Fact (0 < L)] {r : ℝ} (hr : 0 < r)
    (Mfam : Lp ℂ 2 (volume : Measure (AddCircle L)) → Measure ℝ) (hM0 : Mfam 0 = 0)
    (Pfam : Lp ℂ 2 (volume : Measure (AddCircle L)) → BoundaryPhase)
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₁)
    (hΦ₂ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₂)
    (han₁ : AnalyticOnNhd ℝ Φ₁ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (han₂ : AnalyticOnNhd ℝ Φ₂ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (hm₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₁ u n‖ ^ 2 = (Pfam u).indexedMassReal (Mfam u) n)
    (hm₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₂ u n‖ ^ 2 = (Pfam u).indexedMassReal (Mfam u) n)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hc₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ (Cphys L u) = star (Φ₁ u))
    (hc₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₂ (Cphys L u) = star (Φ₂ u)) :
    ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, Φ₁ u = Φ₂ u :=
  reset_normalization_uniqueness_phys L hr (fun n u => (Pfam u).indexedMassReal (Mfam u) n)
    (fun n => by simp [BoundaryPhase.indexedMassReal, BoundaryPhase.indexedMass, hM0])
    Φ₁ Φ₂ hΦ₁ hΦ₂ han₁ han₂ hm₁ hm₂ hD₁ hD₂ hc₁ hc₂

end QuantumNLS.MonotoneMassConsumers

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.MonotoneMassConsumers.SelectedPhase
#print axioms QuantumNLS.MonotoneMassConsumers.MassData
#print axioms QuantumNLS.MonotoneMassConsumers.massMap
#print axioms QuantumNLS.MonotoneMassConsumers.massMap_apply
#print axioms QuantumNLS.MonotoneMassConsumers.chartMasses_iff
#print axioms QuantumNLS.MonotoneMassConsumers.MassProper
#print axioms QuantumNLS.MonotoneMassConsumers.actionFibre
#print axioms QuantumNLS.MonotoneMassConsumers.isCompact_fibre
#print axioms QuantumNLS.MonotoneMassConsumers.reset_normalization_uniqueness

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.MonotoneMassConsumers." then
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
