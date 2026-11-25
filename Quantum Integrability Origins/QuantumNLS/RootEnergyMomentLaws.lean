import QuantumNLS.RootEnergyMomentKernels
import QuantumNLS.BulkResponseActual

/-! Corrected GP-14 for the ACTUAL product spectral law and its finite
coordinate space. The square has Tonelli with proved measurability (possibly
infinite). Every bounded square truncation has complex Fubini with product
integrability and both section qualifiers proved. No finiteness of the full
square expectation is claimed in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
namespace QuantumNLS.RootEnergyMomentLaws
variable {L κ : ℝ} [Fact (0 < L)]

instance countableLabels (N : ℕ) : Countable (MArr N) := by
  change Countable {m : ℤ →₀ ℕ // (m.sum fun _ k => k) = N}
  infer_instance

def law (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) : Measure (MArr N) :=
  bornMeasure (physBasis L hκ N) u hu

instance (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    IsProbabilityMeasure (law hκ u hu N) := by unfold law; infer_instance

def square (L κ : ℝ) (N : ℕ) (p : MArr N × Fin N) : ℝ :=
  (arrRoots L (κ/N) p.1 p.2)^2

def truncated (L κ : ℝ) (N : ℕ) (R : ℝ) (p : MArr N × Fin N) : ℂ :=
  (min (square L κ N p) R : ℝ)

omit [Fact (0 < L)] in
/-- Each sample has its genuine finite second moment, with the exact root
sum. This is pointwise in the actual spectral label and assumes no averaged
moment or form identity. -/
theorem sample_second_moment {N : ℕ} (hN : 0 < N) (m : MArr N) :
    Integrable (fun t : ℝ => t^2) (empiricalMeasure L (κ/N) m) ∧
      (∫ t : ℝ, t^2 ∂(empiricalMeasure L (κ/N) m)) =
        (N : ℝ)⁻¹ * ∑ j, (arrRoots L (κ/N) m j)^2 := by
  have hi (j : Fin N) : Integrable (fun t : ℝ => t^2)
      (Measure.dirac (arrRoots L (κ/N) m j)) := integrable_dirac (by finiteness)
  have hs : Integrable (fun t : ℝ => t^2)
      (∑ j : Fin N, Measure.dirac (arrRoots L (κ/N) m j)) :=
    integrable_finsetSum_measure.mpr (fun j _ => hi j)
  constructor
  · exact hs.smul_measure (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne'))
  · unfold empiricalMeasure
    rw [integral_smul_measure, integral_finsetSum_measure]
    · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    · intro j _; exact hi j

/-- Both SFinite instances are constructed for the actual measures. -/
lemma actual_sfinite (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    SFinite (law hκ u hu N) ∧ SFinite (Measure.count : Measure (Fin N)) := by
  constructor <;> infer_instance

omit [Fact (0 < L)] in
lemma square_measurable (N : ℕ) : Measurable (square L κ N) :=
  measurable_of_countable _

/-- Corrected nonnegative Tonelli, with both iterated orders, on the actual
Born product measure. The equality remains valid when the value is infinite. -/
theorem actual_square_tonelli (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    let P := law hκ u hu N
    let C : Measure (Fin N) := Measure.count
    (∫⁻ p, ENNReal.ofReal (square L κ N p) ∂P.prod C) =
      ∫⁻ m, ∫⁻ j, ENNReal.ofReal (square L κ N (m,j)) ∂C ∂P ∧
    (∫⁻ p, ENNReal.ofReal (square L κ N p) ∂P.prod C) =
      ∫⁻ j, ∫⁻ m, ENNReal.ofReal (square L κ N (m,j)) ∂P ∂C := by
  dsimp only
  have hm : AEMeasurable (fun p => ENNReal.ofReal (square L κ N p))
      ((law hκ u hu N).prod Measure.count) :=
    (square_measurable (L := L) (κ := κ) N).ennreal_ofReal.aemeasurable
  exact ⟨lintegral_prod _ hm, lintegral_prod_symm _ hm⟩

lemma truncated_integrable (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (N : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Integrable (truncated L κ N R) ((law hκ u hu N).prod Measure.count) := by
  apply (integrable_const R).mono' (measurable_of_countable _).aestronglyMeasurable
  apply ae_of_all
  intro p
  have hsq : 0 ≤ square L κ N p := by unfold square; positivity
  rw [truncated, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_min hsq hR)]
  exact min_le_right _ _

/-- Integrable complex Fubini for actual truncated square kernels, including
both AE section-integrability and outer-integrability conclusions. Every
repair hypothesis is discharged for these specific functions and measures. -/
theorem actual_truncation_fubini (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (N : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    let P := law hκ u hu N
    let C : Measure (Fin N) := Measure.count
    let f := truncated L κ N R
    Integrable f (P.prod C) ∧
    (∀ᵐ m ∂P, Integrable (fun j => f (m,j)) C) ∧
    (∀ᵐ j ∂C, Integrable (fun m => f (m,j)) P) ∧
    Integrable (fun m => ∫ j, f (m,j) ∂C) P ∧
    Integrable (fun j => ∫ m, f (m,j) ∂P) C ∧
    (∫ p, f p ∂P.prod C) = ∫ m, ∫ j, f (m,j) ∂C ∂P ∧
    (∫ p, f p ∂P.prod C) = ∫ j, ∫ m, f (m,j) ∂P ∂C := by
  dsimp only
  have hi := truncated_integrable hκ u hu N hR
  exact ⟨hi, hi.prod_right_ae, hi.prod_left_ae, hi.integral_prod_left,
    hi.integral_prod_right, integral_prod _ hi, integral_prod_symm _ hi⟩

#print axioms sample_second_moment
#print axioms actual_square_tonelli
#print axioms actual_truncation_fubini
end QuantumNLS.RootEnergyMomentLaws

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentLaws." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentLaws." then
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
