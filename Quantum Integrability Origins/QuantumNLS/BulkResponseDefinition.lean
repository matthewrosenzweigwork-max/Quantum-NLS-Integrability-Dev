import QuantumNLS.RootCoreDensity
import QuantumNLS.PhysicalL2Normalization

/-! DEF-052 (F03.tex:156): the actual limiting measure, quantile, finite-energy
domain and response equation. Finite second moment is the printed section
assumption, not a conclusion for arbitrary continuous L2 inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped ENNReal
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.BulkResponseDefinition
open PhysicalTensor (L2T)
open BulkResponseActual BulkResponseForm
variable {L κ : ℝ} [Fact (0 < L)]

def mu (u : L2T L) (hu : ‖u‖ = 1) : ProbabilityMeasure ℝ := FreeLimit.muKappa u hu κ

theorem limiting (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    IsLimitingRapidityMeasure L κ hκ u hu (mu (κ := κ) u hu) := FreeLimit.muKappa_spec u hu hκ

theorem fullMass_eq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    PhysicalQuantumMeasure.measure hκ u = (mu (κ := κ) u hu : Measure ℝ) := by
  have hn : u ≠ 0 := by intro h; simp [h] at hu
  rw [PhysicalL2Normalization.measure_eq_Mmeas, FullMass.Mmeas_of_ne κ hn]
  simp [FullMass.unitDir, hu, mu]

theorem density (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) : HasRootDensity L κ uf (mu (κ := κ) u hu) := by
  rw [← fullMass_eq hκ u hu]
  exact RootDensityIdentification.root_density_rep hκ (by intro h; simp [h] at hu) hrep

/-- The F03 standing data now use the canonical measure. Only the printed
finite-second-moment hypothesis remains an input. -/
def data (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf)
    (h2 : RapidityTransport.HasFiniteMoment 2 (mu (κ := κ) u hu : Measure ℝ)) :
    ActualBulkData L κ hκ u hu where
  μ := mu u hu
  limit := limiting hκ u hu
  bulk := {
    isProbability := inferInstance
    noAtoms := by
      rw [← fullMass_eq hκ u hu]
      exact PhysicalUnconditionalTrace.atomless hκ u
    finiteSecondMoment := h2
    coreDensity := by
      rw [← fullMass_eq hκ u hu]
      exact RootCoreDensity.coreDensity_actual hκ (by intro h; simp [h] at hu) hrep }

/-- The increasing quantile of the actual unit-mass law. -/
def Q (u : L2T L) (hu : ‖u‖ = 1) : ℝ → ℝ := bulkQuantile (mu (κ := κ) u hu)
def energy (u : L2T L) (hu : ‖u‖ = 1) (F : L2Unit) : ℝ≥0∞ :=
  formEnergy (Q (κ := κ) u hu) F
def domain (u : L2T L) (hu : ‖u‖ = 1) : Set L2Unit := formDomain (Q (κ := κ) u hu)
def form (u : L2T L) (hu : ‖u‖ = 1) (F H : L2Unit) : ℝ :=
  bulkForm L κ (Q (κ := κ) u hu) F H
def IsResponse (u : L2T L) (hu : ‖u‖ = 1) (W : L2Unit) : Prop :=
  IsBulkResponse L κ (Q (κ := κ) u hu) W

theorem quantile_clause (u : L2T L) (hu : ‖u‖ = 1) :
    Q (κ := κ) u hu = QuantileTransport.quantile (mu (κ := κ) u hu) := rfl

theorem energy_clause (u : L2T L) (hu : ‖u‖ = 1) (F : L2Unit) :
    energy (κ := κ) u hu F = ∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (((F p.1 - F p.2) / (Q (κ := κ) u hu p.1 - Q (κ := κ) u hu p.2)) ^ 2)
        ∂(unitInterval.prod unitInterval) := rfl

theorem domain_clause (u : L2T L) (hu : ‖u‖ = 1) (F : L2Unit) :
    F ∈ domain (κ := κ) u hu ↔ energy (κ := κ) u hu F < ⊤ := Iff.rfl

theorem form_clause (u : L2T L) (hu : ‖u‖ = 1) (F H : L2Unit) :
    form (κ := κ) u hu F H = L * ∫ t, F t * H t ∂unitInterval +
      κ * ∫ p : ℝ × ℝ,
        ((F p.1 - F p.2) / (Q (κ := κ) u hu p.1 - Q (κ := κ) u hu p.2)) *
        ((H p.1 - H p.2) / (Q (κ := κ) u hu p.1 - Q (κ := κ) u hu p.2))
          ∂(unitInterval.prod unitInterval) := rfl

theorem form_ratio_clause (u : L2T L) (hu : ‖u‖ = 1) (F H : L2Unit) :
    form (κ := κ) u hu F H = L * ∫ t, F t * H t ∂unitInterval +
      κ * ∫ p : ℝ × ℝ, ((F p.1 - F p.2) * (H p.1 - H p.2)) /
        (Q (κ := κ) u hu p.1 - Q (κ := κ) u hu p.2) ^ 2
          ∂(unitInterval.prod unitInterval) := by
  simp only [form, bulkForm, quot, div_mul_div_comm, pow_two]

theorem energy_ratio_clause (u : L2T L) (hu : ‖u‖ = 1) (F : L2Unit) :
    energy (κ := κ) u hu F = ∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal ((F p.1 - F p.2) ^ 2 /
        (Q (κ := κ) u hu p.1 - Q (κ := κ) u hu p.2) ^ 2)
          ∂(unitInterval.prod unitInterval) := by
  simp only [energy, formEnergy, quot, div_pow]

theorem response_clause (u : L2T L) (hu : ‖u‖ = 1) (W : L2Unit) :
    IsResponse (κ := κ) u hu W ↔ W ∈ domain (κ := κ) u hu ∧
      ∀ H ∈ domain (κ := κ) u hu, form (κ := κ) u hu W H =
        ∫ t, Q (κ := κ) u hu t * H t ∂unitInterval := Iff.rfl

theorem zero_denominator (F : L2Unit) {t s : ℝ} (q : ℝ → ℝ) (h : q t = q s) :
    quot q F t s = 0 := by simp [quot, h]

/-- Exactly the existing smooth-quantile pullback core predicate. -/
def IsCore (u : L2T L) (hu : ‖u‖ = 1) : Prop :=
  IsFormCore L κ (Q (κ := κ) u hu) {F | IsSmoothQuantilePullback (Q (κ := κ) u hu) F}

theorem core_clause (u : L2T L) (hu : ‖u‖ = 1) :
    IsCore (κ := κ) u hu ↔
      IsFormCore L κ (Q (κ := κ) u hu)
        {F | IsSmoothQuantilePullback (Q (κ := κ) u hu) F} := Iff.rfl

theorem data_quantile (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf)
    (h2 : RapidityTransport.HasFiniteMoment 2 (mu (κ := κ) u hu : Measure ℝ)) :
    (data hκ u hu hrep h2).toBulkResponseData.Q = Q (κ := κ) u hu := rfl

theorem data_response (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf)
    (h2 : RapidityTransport.HasFiniteMoment 2 (mu (κ := κ) u hu : Measure ℝ)) (W : L2Unit) :
    (data hκ u hu hrep h2).toBulkResponseData.IsResponse W ↔ IsResponse (κ := κ) u hu W := Iff.rfl
end QuantumNLS.BulkResponseDefinition

#print axioms QuantumNLS.BulkResponseDefinition.mu
#print axioms QuantumNLS.BulkResponseDefinition.limiting
#print axioms QuantumNLS.BulkResponseDefinition.fullMass_eq
#print axioms QuantumNLS.BulkResponseDefinition.density
#print axioms QuantumNLS.BulkResponseDefinition.data
#print axioms QuantumNLS.BulkResponseDefinition.Q
#print axioms QuantumNLS.BulkResponseDefinition.energy
#print axioms QuantumNLS.BulkResponseDefinition.domain
#print axioms QuantumNLS.BulkResponseDefinition.form
#print axioms QuantumNLS.BulkResponseDefinition.IsResponse
#print axioms QuantumNLS.BulkResponseDefinition.quantile_clause
#print axioms QuantumNLS.BulkResponseDefinition.energy_clause
#print axioms QuantumNLS.BulkResponseDefinition.domain_clause
#print axioms QuantumNLS.BulkResponseDefinition.form_clause
#print axioms QuantumNLS.BulkResponseDefinition.form_ratio_clause
#print axioms QuantumNLS.BulkResponseDefinition.energy_ratio_clause
#print axioms QuantumNLS.BulkResponseDefinition.response_clause
#print axioms QuantumNLS.BulkResponseDefinition.zero_denominator
#print axioms QuantumNLS.BulkResponseDefinition.IsCore
#print axioms QuantumNLS.BulkResponseDefinition.core_clause
#print axioms QuantumNLS.BulkResponseDefinition.data_quantile
#print axioms QuantumNLS.BulkResponseDefinition.data_response

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.BulkResponseDefinition." then
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
