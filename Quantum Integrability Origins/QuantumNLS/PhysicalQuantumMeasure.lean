import QuantumNLS.ProductPreparation
import QuantumNLS.RootMeasureExistence
import QuantumNLS.SpatialTransfer

/-!
Canonical DEF-010 full-mass measure on the arbitrary physical L2 carrier.
The unit law is the proved complete-Bethe Born-law limit at coupling κ‖u‖²/N.
This module does not assert the spectral-density or boundary extension theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.PhysicalQuantumMeasure
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductPreparation
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The unique limiting probability law for a positive-mass preparation. -/
def unitLaw (P : PositiveMassPreparation (L := L)) : ProbabilityMeasure ℝ :=
  Classical.choose (QuantumNLS.RootMeasureExistence.exists_limiting_measure
    P.effectiveCoupling_pos P.unitProfile P.norm_unitProfile)

theorem unitLaw_limit (P : PositiveMassPreparation (L := L)) :
    IsLimitingRapidityMeasure L P.effectiveCoupling P.effectiveCoupling_pos
      P.unitProfile P.norm_unitProfile (unitLaw P) :=
  Classical.choose_spec (QuantumNLS.RootMeasureExistence.exists_limiting_measure
    P.effectiveCoupling_pos P.unitProfile P.norm_unitProfile)

theorem unitLaw_unique (P : PositiveMassPreparation (L := L))
    {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L P.effectiveCoupling P.effectiveCoupling_pos
      P.unitProfile P.norm_unitProfile μ) : μ = unitLaw P :=
  hμ.unique (unitLaw_limit P)

/-- The physical positive-mass preparation; no supplied spectral facts. -/
def preparation (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) :
    PositiveMassPreparation (L := L) :=
  ⟨u, κ, sq_pos_of_pos (norm_pos_iff.mpr hu), hκ⟩

theorem effectiveCoupling_eq (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    (preparation hκ u hu).effectiveCoupling = κ * ‖u‖ ^ 2 := rfl

/-- Canonical full-mass quantum measure, with the prescribed zero-input value. -/
def measure (hκ : 0 < κ) (u : L2T L) : Measure ℝ :=
  by
    classical
    exact if hu : u = 0 then 0 else
      ENNReal.ofReal (physicalMass u) • (unitLaw (preparation hκ u hu) : Measure ℝ)

@[simp] theorem measure_zero (hκ : 0 < κ) : measure hκ (0 : L2T L) = 0 := by
  simp [measure]

theorem measure_eq_scaled (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u = ENNReal.ofReal (physicalMass u) •
      (unitLaw (preparation hκ u hu) : Measure ℝ) := by
  rw [measure, dite_eq_right hu]

theorem measure_eq_fullMassMeasure (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u = fullMassMeasure u (unitLaw (preparation hκ u hu) : Measure ℝ) := by
  rw [measure_eq_scaled hκ hu, fullMassMeasure_eq_scaled (u := u) _
    (preparation hκ u hu).mass_pos]

/-- Full mass as an ENNReal identity; no mass is lost at normalization. -/
theorem measure_univ (hκ : 0 < κ) (u : L2T L) :
    measure hκ u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  classical
  by_cases hu : u = 0
  · subst u; simp
  · rw [measure_eq_scaled hκ hu, Measure.smul_apply,
      MeasureTheory.measure_univ, smul_eq_mul, mul_one]
    rfl

instance finite_measure (hκ : 0 < κ) (u : L2T L) : IsFiniteMeasure (measure hκ u) :=
  ⟨by rw [measure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- The physical full-mass identity on arbitrary L2 inputs, including zero. -/
theorem full_mass (hκ : 0 < κ) (u : L2T L) :
    (measure hκ u Set.univ).toReal = ‖u‖ ^ 2 := by
  rw [measure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem measure_ne_zero (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u ≠ 0 := by
  intro h
  have hf := full_mass hκ u
  rw [h] at hf
  have : ‖u‖ ^ 2 = 0 := by simpa using hf.symm
  exact hu (norm_eq_zero.mp (sq_eq_zero_iff.mp this))

/-- Binding to the literal complete-Bethe law and DEF-003 mass scaling.
The law uses the unit profile and effective coupling κm, hence microscopic κm/N. -/
theorem quantum_law (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    ∃ μ : ProbabilityMeasure ℝ,
      IsLimitingRapidityMeasure L (preparation hκ u hu).effectiveCoupling
        (preparation hκ u hu).effectiveCoupling_pos
        (preparation hκ u hu).unitProfile
        (preparation hκ u hu).norm_unitProfile μ ∧
      measure hκ u = fullMassMeasure u (μ : Measure ℝ) :=
  ⟨unitLaw (preparation hκ u hu), unitLaw_limit (preparation hκ u hu), measure_eq_fullMassMeasure hκ hu⟩

/-- Any probability law with the actual quantum-limit specification yields the
same full-mass measure. This removes dependence on the existence witness. -/
theorem measure_eq_of_limit (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L (preparation hκ u hu).effectiveCoupling
      (preparation hκ u hu).effectiveCoupling_pos
      (preparation hκ u hu).unitProfile
      (preparation hκ u hu).norm_unitProfile μ) :
    measure hκ u = fullMassMeasure u (μ : Measure ℝ) := by
  rw [unitLaw_unique (preparation hκ u hu) hμ]
  exact measure_eq_fullMassMeasure hκ hu

/-- Literal DEF-010/DEF-003 characterization at arbitrary mass. -/
def IsQuantumMeasure (hκ : 0 < κ) (u : L2T L) (M : Measure ℝ) : Prop := by
  classical
  exact if hu : u = 0 then M = 0 else
    ∃ μ : ProbabilityMeasure ℝ,
      IsLimitingRapidityMeasure L (preparation hκ u hu).effectiveCoupling
        (preparation hκ u hu).effectiveCoupling_pos
        (preparation hκ u hu).unitProfile
        (preparation hκ u hu).norm_unitProfile μ ∧
      M = fullMassMeasure u (μ : Measure ℝ)

theorem measure_spec (hκ : 0 < κ) (u : L2T L) :
    IsQuantumMeasure hκ u (measure hκ u) := by
  classical
  by_cases hu : u = 0
  · subst u
    simp [IsQuantumMeasure]
  · simpa only [IsQuantumMeasure, dite_eq_right hu] using quantum_law hκ hu

theorem quantumMeasure_unique (hκ : 0 < κ) (u : L2T L) {M : Measure ℝ}
    (hM : IsQuantumMeasure hκ u M) : M = measure hκ u := by
  classical
  by_cases hu : u = 0
  · subst u
    simpa [IsQuantumMeasure] using hM
  · simp only [IsQuantumMeasure, dite_eq_right hu] at hM
    obtain ⟨μ, hμ, he⟩ := hM
    exact he.trans (measure_eq_of_limit hκ hu hμ).symm

/-- Existence and uniqueness of the physical full-mass quantum measure for
all physical L2 inputs; this theorem has no supplied spectral measure. -/
theorem exists_unique_quantumMeasure (hκ : 0 < κ) (u : L2T L) :
    ∃! M : Measure ℝ, IsQuantumMeasure hκ u M :=
  ⟨measure hκ u, measure_spec hκ u, fun _ hM => quantumMeasure_unique hκ u hM⟩

/-- Literal Cauchy-transform scaling for any spectral parameter. -/
theorem cauchy_scaled (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (z : ℂ) :
    QuantumNLS.EmpiricalRapidity.cauchyTransform (measure hκ u) z =
      (‖u‖ ^ 2 : ℝ) • QuantumNLS.EmpiricalRapidity.cauchyTransform
        (unitLaw (preparation hκ u hu) : Measure ℝ) z := by
  rw [measure_eq_scaled hκ hu]
  simp only [QuantumNLS.EmpiricalRapidity.cauchyTransform, integral_smul_measure,
    physicalMass, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The actual high-half-plane product-law characterization, after full-mass scaling. -/
theorem cauchy_highHalf (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {z : ℂ}
    (hz : QuantumNLS.RootMeasureComplex.HighHalf L (preparation hκ u hu).effectiveCoupling z) :
    QuantumNLS.EmpiricalRapidity.cauchyTransform (measure hκ u) z =
      (‖u‖ ^ 2 : ℝ) • QuantumNLS.RootMeasureConcentration.gStar L
        (preparation hκ u hu).effectiveCoupling (preparation hκ u hu).effectiveCoupling_pos
        (preparation hκ u hu).unitProfile (preparation hκ u hu).norm_unitProfile z := by
  rw [cauchy_scaled hκ hu]
  congr 1
  exact QuantumNLS.RootMeasureExistence.cauchy_limiting_measure
    (preparation hκ u hu).effectiveCoupling_pos
    (preparation hκ u hu).unitProfile (preparation hκ u hu).norm_unitProfile
    (unitLaw_limit (preparation hκ u hu)) hz

/-- Algebraic conversion from the actual quantum product symbol to a cosine.
The remaining spatial step is identifying this symbol with the normalized L2 trace. -/
theorem cosine_fz (L κ : ℝ) (z w : ℂ) :
    2 * Complex.cos ((L : ℂ) * z / 2 - (κ : ℂ) * w) =
      Complex.exp (-(Complex.I * z * L / 2)) *
        QuantumNLS.RootMeasureComplex.fz L κ z w := by
  let a : ℂ := Complex.I * z * L / 2
  let b : ℂ := Complex.I * κ * w
  have he : 2 * a = Complex.I * z * L := by dsimp [a]; ring
  have h₁ : Complex.exp (-a) * Complex.exp b = Complex.exp (-a + b) :=
    (Complex.exp_add _ _).symm
  have h₂ : Complex.exp (-a) * (Complex.exp (2 * a) * Complex.exp (-b)) =
      Complex.exp (a - b) := by
    rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hf : QuantumNLS.RootMeasureComplex.fz L κ z w =
      Complex.exp b + Complex.exp (2 * a) * Complex.exp (-b) := by
    rw [he]
    rfl
  rw [hf]
  change 2 * Complex.cos ((L : ℂ) * z / 2 - (κ : ℂ) * w) =
    Complex.exp (-a) * (Complex.exp b + Complex.exp (2 * a) * Complex.exp (-b))
  rw [mul_add, h₁, h₂, Complex.two_cos]
  have h₃ : ((L : ℂ) * z / 2 - (κ : ℂ) * w) * Complex.I = a - b := by
    dsimp [a, b]; ring
  have h₄ : -((L : ℂ) * z / 2 - (κ : ℂ) * w) * Complex.I = -a + b := by
    dsimp [a, b]; ring
  rw [h₃, h₄, add_comm]

/-- Cosine identity with the actual normalized complete-Bethe product-law symbol
on the high half-plane. No L2 discriminant identification is claimed here. -/
theorem cosine_productSymbol (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {z : ℂ}
    (hz : QuantumNLS.RootMeasureComplex.HighHalf L (preparation hκ u hu).effectiveCoupling z) :
    2 * Complex.cos (QuantumNLS.SpatialTransfer.boundaryPhase L κ (measure hκ u) z) =
      Complex.exp (-(Complex.I * z * L / 2)) *
        QuantumNLS.NormalizedTransfer.productSymbol L (preparation hκ u hu).effectiveCoupling
          (preparation hκ u hu).unitProfile z := by
  unfold QuantumNLS.SpatialTransfer.boundaryPhase
  rw [cauchy_highHalf hκ hu hz, Complex.real_smul]
  have he : (κ : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ) = ((κ * ‖u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [← mul_assoc, he, ← effectiveCoupling_eq hκ hu, cosine_fz]
  rw [(QuantumNLS.RootMeasureConcentration.gStar_spec
    (preparation hκ u hu).effectiveCoupling_pos
    (preparation hκ u hu).unitProfile (preparation hκ u hu).norm_unitProfile hz).2]

/-- Full-mass and normalized phases coincide with the effective coupling.
This is an identity of the actual quantum measures, not an assumed cosine identity. -/
theorem phase_scaling (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (z : ℂ) :
    QuantumNLS.SpatialTransfer.boundaryPhase L κ (measure hκ u) z =
      QuantumNLS.SpatialTransfer.boundaryPhase L (preparation hκ u hu).effectiveCoupling
        (unitLaw (preparation hκ u hu) : Measure ℝ) z := by
  rw [effectiveCoupling_eq hκ hu]
  unfold QuantumNLS.SpatialTransfer.boundaryPhase
  rw [cauchy_scaled hκ hu, Complex.real_smul]
  push_cast
  ring

/-- Positive imaginary phase for every arbitrary physical input, including vacuum. -/
theorem im_phase_pos (hκ : 0 < κ) (u : L2T L) {z : ℂ} (hz : 0 < z.im) :
    0 < (QuantumNLS.SpatialTransfer.boundaryPhase L κ (measure hκ u) z).im := by
  classical
  by_cases hu : u = 0
  · subst u
    simp only [measure_zero, QuantumNLS.SpatialTransfer.boundaryPhase,
      QuantumNLS.EmpiricalRapidity.cauchyTransform, integral_zero_measure,
      mul_zero, sub_zero]
    simp only [Complex.div_ofNat_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    exact div_pos (mul_pos (Fact.out : 0 < L) hz) (by norm_num)
  · exact QuantumNLS.SpatialTransfer.im_boundaryPhase_pos Fact.out hκ
      (measure hκ u) (measure_ne_zero hκ hu) hz

end QuantumNLS.PhysicalQuantumMeasure

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalQuantumMeasure.effectiveCoupling_eq
#print axioms QuantumNLS.PhysicalQuantumMeasure.unitLaw
#print axioms QuantumNLS.PhysicalQuantumMeasure.unitLaw_limit
#print axioms QuantumNLS.PhysicalQuantumMeasure.unitLaw_unique
#print axioms QuantumNLS.PhysicalQuantumMeasure.preparation
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_zero
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_eq_scaled
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_eq_fullMassMeasure
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_univ
#print axioms QuantumNLS.PhysicalQuantumMeasure.full_mass
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_ne_zero
#print axioms QuantumNLS.PhysicalQuantumMeasure.quantum_law
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_eq_of_limit
#print axioms QuantumNLS.PhysicalQuantumMeasure.IsQuantumMeasure
#print axioms QuantumNLS.PhysicalQuantumMeasure.measure_spec
#print axioms QuantumNLS.PhysicalQuantumMeasure.quantumMeasure_unique
#print axioms QuantumNLS.PhysicalQuantumMeasure.exists_unique_quantumMeasure
#print axioms QuantumNLS.PhysicalQuantumMeasure.cauchy_scaled
#print axioms QuantumNLS.PhysicalQuantumMeasure.cauchy_highHalf
#print axioms QuantumNLS.PhysicalQuantumMeasure.cosine_fz
#print axioms QuantumNLS.PhysicalQuantumMeasure.cosine_productSymbol
#print axioms QuantumNLS.PhysicalQuantumMeasure.phase_scaling
#print axioms QuantumNLS.PhysicalQuantumMeasure.im_phase_pos

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalQuantumMeasure." then
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
