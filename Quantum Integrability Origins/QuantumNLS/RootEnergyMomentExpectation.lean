import QuantumNLS.RootEnergyMomentFinite

/-! Exact unbounded expectation of the ACTUAL Born product spectral law.
Every integrability obligation is derived from the contact-form expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy QuantumNLS.BetheLabels
open QuantumNLS.BetheCoefficientTransform QuantumNLS.BulkResponseActual
open QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
open QuantumNLS.RootEnergyMomentLaws QuantumNLS.RootEnergyMomentFinite
namespace QuantumNLS.RootEnergyMomentExpectation
variable {L κ : ℝ} [Fact (0 < L)] {N : ℕ}

def sampleEnergy (L κ : ℝ) (N : ℕ) (m : MArr N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, (arrRoots L (κ/N) m j)^2

omit [Fact (0 < L)] in
lemma sampleEnergy_nonneg (m : MArr N) : 0 ≤ sampleEnergy L κ N m := by
  unfold sampleEnergy
  positivity

lemma coordinate_basis_physical (hN : 0 < N) (hκ : 0 < κ) (m : MArr N) :
    coordBasis hN hκ m = QuantumNLS.BethePhysicalTransfer.symmetricPosition L N
      (physBasis L hκ N m) := by
  unfold physBasis
  rw [dite_eq_left (show 1 ≤ N by omega)]
  change coordBasis hN hκ m = QuantumNLS.BethePhysicalTransfer.symmetricPosition L N
    (QuantumNLS.UnconditionalBetheBasis.physicalBasis L N hN (κ/N)
      (div_pos hκ (Nat.cast_pos.mpr hN)) m)
  rw [QuantumNLS.UnconditionalBetheBasis.physicalBasis_position,coordBasis_apply]

lemma product_position (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    QuantumNLS.BethePhysicalTransfer.symmetricPosition L N (productVec L N u) =
      ContactOperator.valSym (⟨productH1 hu hH N,productH1_sym hu hH N⟩ : ContactOperator.VSym L N) := by
  apply Subtype.ext
  exact (physUnitary_ptprod (fun _ : Fin N => u)).trans (productH1_val hu hH N).symm

/-- Exact finite-N series, with no finiteness assumption. -/
theorem born_energy_hasSum (hN : 0 < N) (hκ : 0 < κ)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    HasSum (fun m => bornLaw (physBasis L hκ N) u m * sampleEnergy L κ N m)
      (energyH1 κ (u : AddCircle L → ℂ) - κ * quartic (u : AddCircle L → ℂ) / N) := by
  let x : ContactOperator.VSym L N := ⟨productH1 hu hH N,productH1_sym hu hH N⟩
  have hb (m : MArr N) : bornLaw (physBasis L hκ N) u m =
      ‖⟪coordBasis hN hκ m,ContactOperator.valSym x⟫_ℂ‖^2 := by
    unfold bornLaw
    rw [← (QuantumNLS.BethePhysicalTransfer.symmetricPosition L N).inner_map_map,
      ← coordinate_basis_physical hN hκ,product_position u hu hH]
  have h := (contact_energy_hasSum hN hκ x).div_const (N : ℝ)
  have he := hN_div_product hu hH κ hN
  change (ContactForm.q (κ/N) x.1 x.1).re / N = _ at he
  rw [he] at h
  convert h using 1
  funext m
  rw [hb]
  unfold sampleEnergy
  ring

/-- Finiteness and exact expectation under the actual, unconditioned law. -/
theorem actual_energy_expectation (hN : 0 < N) (hκ : 0 < κ)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    Integrable (sampleEnergy L κ N) (law hκ u hu N) ∧
    (∫ m, sampleEnergy L κ N m ∂law hκ u hu N) =
      energyH1 κ (u : AddCircle L → ℂ) - κ * quartic (u : AddCircle L → ℂ) / N := by
  have hs := born_energy_hasSum hN hκ u hu hH
  let P := law hκ u hu N
  have hsingle (m : MArr N) : (P {m}).toReal = bornLaw (physBasis L hκ N) u m := by
    rw [show P = EmpiricalRapidity.bornMeasure (physBasis L hκ N) u hu from rfl,
      EmpiricalRapidity.bornMeasure_singleton,ENNReal.toReal_ofReal (bornLaw_nonneg _ _ _)]
  have hi : Integrable (sampleEnergy L κ N) P := by
    rw [← Measure.sum_smul_dirac P]
    apply integrable_sum_dirac (fun m => measure_ne_top _ _)
    simpa only [hsingle,Real.norm_eq_abs,abs_of_nonneg (sampleEnergy_nonneg _)] using hs.summable
  refine ⟨hi,?_⟩
  rw [integral_countable hi]
  simp only [measureReal_def,hsingle,smul_eq_mul]
  exact hs.tsum_eq

/-- The integrable-complex branch of repaired GP-14 for the FULL actual
square kernel. Product integrability is a conclusion of the proved finite
contact energy, not an added hypothesis. -/
theorem actual_square_fubini (hN : 0 < N) (hκ : 0 < κ)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    let P := law hκ u hu N
    let C : Measure (Fin N) := Measure.count
    let f := fun p : MArr N × Fin N => (square L κ N p : ℂ)
    Integrable f (P.prod C) ∧
    (∀ᵐ m ∂P, Integrable (fun j => f (m,j)) C) ∧
    (∀ᵐ j ∂C, Integrable (fun m => f (m,j)) P) ∧
    Integrable (fun m => ∫ j, f (m,j) ∂C) P ∧
    Integrable (fun j => ∫ m, f (m,j) ∂P) C ∧
    (∫ p, f p ∂P.prod C) = ∫ m, ∫ j, f (m,j) ∂C ∂P ∧
    (∫ p, f p ∂P.prod C) = ∫ j, ∫ m, f (m,j) ∂P ∂C := by
  dsimp only
  have hsum := (actual_energy_expectation hN hκ u hu hH).1.const_mul (N : ℝ)
  have hj (j : Fin N) : Integrable (fun m : MArr N => (square L κ N (m,j) : ℂ))
      (law hκ u hu N) := by
    apply hsum.mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro m
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by unfold square; positivity)]
    have hle := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
      sq_nonneg (arrRoots L (κ/N) m k)) (Finset.mem_univ j)
    change square L κ N (m,j) ≤ (N : ℝ) * sampleEnergy L κ N m
    unfold sampleEnergy square
    rw [← mul_assoc,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'),one_mul]
    exact hle
  have hi : Integrable (fun p : MArr N × Fin N => (square L κ N p : ℂ))
      ((law hκ u hu N).prod Measure.count) := by
    rw [integrable_prod_iff (measurable_of_countable _).aestronglyMeasurable]
    constructor
    · exact ae_of_all _ (fun m => Integrable.of_finite)
    · have h : Integrable (fun m => ∑ j : Fin N, ‖(square L κ N (m,j) : ℂ)‖)
          (law hκ u hu N) := integrable_finsetSum _ (fun j _ => (hj j).norm)
      simpa only [integral_count] using h
  exact ⟨hi,hi.prod_right_ae,hi.prod_left_ae,hi.integral_prod_left,
    hi.integral_prod_right,integral_prod _ hi,integral_prod_symm _ hi⟩

#print axioms actual_energy_expectation
#print axioms actual_square_fubini
end QuantumNLS.RootEnergyMomentExpectation

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentExpectation." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentExpectation." then
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
