import QuantumNLS.ContactProductMass
import QuantumNLS.ContactFormFamily

/-! Corrected GP-14 applied to the actual physical tensor, weak partials,
and coordinate collision traces. All measures below are finite (hence SFinite);
all square kernels are integrable because their vectors belong to L².
No regularity or section-integrability premise is carried by the consumer. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.ProductEnergyPreparation QuantumNLS.CollisionTrace
  QuantumNLS.CollisionIdentification QuantumNLS.ChargeEnergy
namespace QuantumNLS.ContactProductIntegrals
variable {L : ℝ} [Fact (0 < L)]

section Fubini
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]

/-- Both corrected branches, including the a.e. section qualifiers. -/
def SquareFubini (F : Lp ℂ 2 (μ.prod ν)) : Prop :=
  let g := fun p : A × B => ‖F p‖ ^ 2
  Integrable g (μ.prod ν) ∧
  (∀ᵐ a ∂μ, Integrable (fun b => g (a,b)) ν) ∧
  (∀ᵐ b ∂ν, Integrable (fun a => g (a,b)) μ) ∧
  Integrable (fun a => ∫ b, g (a,b) ∂ν) μ ∧
  Integrable (fun b => ∫ a, g (a,b) ∂μ) ν ∧
  (∫ p, g p ∂(μ.prod ν)) = ∫ a, ∫ b, g (a,b) ∂ν ∂μ ∧
  (∫ p, g p ∂(μ.prod ν)) = ∫ b, ∫ a, g (a,b) ∂μ ∂ν ∧
  AEMeasurable (fun p => ENNReal.ofReal (g p)) (μ.prod ν) ∧
  AEMeasurable (fun a => ∫⁻ b, ENNReal.ofReal (g (a,b)) ∂ν) μ ∧
  AEMeasurable (fun b => ∫⁻ a, ENNReal.ofReal (g (a,b)) ∂μ) ν ∧
  (∫⁻ p, ENNReal.ofReal (g p) ∂(μ.prod ν)) =
    ∫⁻ a, ∫⁻ b, ENNReal.ofReal (g (a,b)) ∂ν ∂μ ∧
  (∫⁻ p, ENNReal.ofReal (g p) ∂(μ.prod ν)) =
    ∫⁻ b, ∫⁻ a, ENNReal.ofReal (g (a,b)) ∂μ ∂ν

theorem square_fubini (F : Lp ℂ 2 (μ.prod ν)) : SquareFubini μ ν F := by
  have hi : Integrable (fun p : A × B => ‖F p‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hm := hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  exact ⟨hi, hi.prod_right_ae, hi.prod_left_ae, hi.integral_prod_left,
    hi.integral_prod_right, integral_prod _ hi, integral_prod_symm _ hi,
    hm, hm.lintegral_prod_right', hm.lintegral_prod_left',
    lintegral_prod _ hm, lintegral_prod_symm _ hm⟩
end Fubini

/-- A measure-preserving split of one actual tensor coordinate. -/
def splitL2 {n : ℕ} (F : L2TN L (n+1)) (j : Fin (n+1)) :
    Lp ℂ 2 ((volume : Measure (AddCircle L)).prod (torusPiMeasure L n)) :=
  Lp.compMeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => AddCircle L) j).symm
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure (AddCircle L))) j).symm F

theorem splitL2_norm {n : ℕ} (F : L2TN L (n+1)) (j : Fin (n+1)) :
    ‖splitL2 F j‖ = ‖F‖ := by
  exact Lp.norm_compMeasurePreserving _ _

/-- Finite Haar/Lebesgue products provide the repaired SFinite hypotheses. -/
theorem actual_measures_sfinite (n : ℕ) :
    SFinite (volume : Measure (AddCircle L)) ∧ SFinite (torusPiMeasure L n) :=
  ⟨inferInstance, inferInstance⟩

/-- GP-14 for an actual split tensor or weak-partial square kernel. -/
theorem split_fubini {n : ℕ} (F : L2TN L (n+1)) (j : Fin (n+1)) :
    SquareFubini (volume : Measure (AddCircle L)) (torusPiMeasure L n) (splitL2 F j) :=
  square_fubini _ _ _

/-- The same physical splitting for any particle number (the empty case is vacuous). -/
def PiSquareFubini : {N : ℕ} → L2TN L N → Prop
  | 0, _ => True
  | n+1, F => ∀ j : Fin (n+1),
      SquareFubini (volume : Measure (AddCircle L)) (torusPiMeasure L n) (splitL2 F j)

theorem pi_square_fubini {N : ℕ} (F : L2TN L N) : PiSquareFubini F := by
  cases N with
  | zero => trivial
  | succ n => exact fun j => split_fubini F j

/-- GP-14 for the actual collision trace, on precisely dy_ij. -/
theorem collision_fubini {N : ℕ} (x : PhysH1 L N) (i j : Fin N) (hij : i ≠ j) :
    SquareFubini (volume : Measure (AddCircle L))
      (Measure.pi fun _ : Rest N i j => (volume : Measure (AddCircle L)))
      (productTrace i j hij x) := square_fubini _ _ _

/-- Integrability is established before finite-product Fubini is used. -/
theorem literal_tensor_integral (u : L2T L) (N : ℕ) :
    Integrable (fun x : Fin N → AddCircle L => ‖prodFun (fun _ => u) x‖ ^ 2)
      (torusPiMeasure L N) ∧
    (∫ x : Fin N → AddCircle L, ‖prodFun (fun _ => u) x‖ ^ 2
      ∂(torusPiMeasure L N)) = (‖u‖ ^ 2) ^ N := by
  have hs : Integrable (fun t : AddCircle L => ‖u t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hp := Integrable.fintype_prod (fun _ : Fin N => hs)
  constructor
  · simpa only [prodFun, norm_prod, Finset.prod_pow] using hp
  · simp only [prodFun, norm_prod]
    simp_rw [← Finset.prod_pow]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin N => (volume : Measure (AddCircle L)))
      (fun (_ : Fin N) (t : AddCircle L) => ‖u t‖ ^ 2)]
    simp only [QuantumNLS.ContactFormFamily.integral_norm_sq_eq,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The one-particle quartic integrand is integrable by the proved H¹ sup bound. -/
theorem literal_collision_kernel {u : L2T L} (hH : OneH1 u) {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    let f := fun p : AddCircle L × (Rest N i j → AddCircle L) =>
      ‖u p.1‖ ^ 4 * ∏ r, ‖u (p.2 r)‖ ^ 2
    Integrable f (dyij (L := L) i j) ∧
    (∫ p, f p ∂(dyij (L := L) i j)) =
      (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) := by
  dsimp only
  have hq := quartic_integrable (oneH1_h04 hH)
  have hs : Integrable (fun t : AddCircle L => ‖u t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hp := Integrable.fintype_prod (fun _ : Rest N i j => hs)
  have hi := hq.mul_prod hp
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  simp_rw [integral_fintype_prod_eq_prod (fun (_ : Rest N i j) (t : AddCircle L) => ‖u t‖ ^ 2)]
  simp only [QuantumNLS.ContactFormFamily.integral_norm_sq_eq, Finset.prod_const,
    Finset.card_univ]
  rw [integral_mul_const]
  have hc : Fintype.card (Rest N i j) = N - 2 := by
    have h := card_DCoord i j hij
    simp only [DCoord, Fintype.card_sum, Fintype.card_unit] at h
    omega
  rw [hc]
  exact mul_comm _ _

#print axioms square_fubini
#print axioms actual_measures_sfinite
#print axioms split_fubini
#print axioms collision_fubini
#print axioms literal_tensor_integral
#print axioms literal_collision_kernel
end QuantumNLS.ContactProductIntegrals

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ContactProductIntegrals." ||
        n.toString.startsWith "_private.QuantumNLS.ContactProductIntegrals." then
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
