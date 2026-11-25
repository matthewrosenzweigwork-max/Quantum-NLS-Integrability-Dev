import QuantumNLS.Ext025B6SpectralLimits
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! GP-08, R-2E4C2F4E: literal finite-family joint spectral projections,
their scalar measure, and its square-integrability domains. All projections
act on the actual physical Bethe space. No intersection replaces a maximal
summed-symbol domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B7JointResolution
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels BoundedBetheTransfer
open BetheChargeResolution
variable {L : ℝ} [Fact (0 < L)] {N d : ℕ}
local instance : Countable (MArr N) :=
  inferInstanceAs (Countable {m : ℤ →₀ ℕ // (m.sum fun _ k => k) = N})
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def tuple (a : Fin d → MArr N → ℝ) (m : MArr N) : Fin d → ℝ := fun j => a j m

def jointProjection (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (B : Set (Fin d → ℝ)) : HN L N →L[ℂ] HN L N := projection b (tuple a ⁻¹' B)

theorem jointProjection_coord (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (B : Set (Fin d → ℝ)) (x : HN L N) (m : MArr N) :
    b.repr (jointProjection b a B x) m = if tuple a m ∈ B then b.repr x m else 0 := by
  simpa only [jointProjection,Set.mem_preimage] using projection_coord b (tuple a ⁻¹' B) x m

theorem jointProjection_univ (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    jointProjection b a Set.univ = 1 := by simp [jointProjection,projection_univ]

theorem jointProjection_empty (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    jointProjection b a ∅ = 0 := by simp [jointProjection,projection_empty]

theorem jointProjection_inter (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (B C : Set (Fin d → ℝ)) :
    jointProjection b a B * jointProjection b a C = jointProjection b a (B ∩ C) :=
  projection_inter b _ _

theorem jointProjection_adjoint (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (B : Set (Fin d → ℝ)) :
    (jointProjection b a B).adjoint = jointProjection b a B := projection_selfAdjoint b _

/-- Strong countable additivity on every disjoint family, hence on Borel families. -/
theorem jointProjection_additive (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (B : ℕ → Set (Fin d → ℝ)) (hB : Pairwise (Disjoint on B)) (x : HN L N) :
    HasSum (fun n => jointProjection b a (B n) x) (jointProjection b a (⋃ n, B n) x) := by
  simpa only [jointProjection,Set.preimage_iUnion] using projection_iUnion_hasSum b
    (fun n => tuple a ⁻¹' B n) (fun i j hij => (hB hij).preimage _) x

/-- This is the displayed weighted coefficient scalar spectral measure. -/
def jointMeasure (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (x : HN L N) :
    Measure (Fin d → ℝ) :=
  Measure.sum fun m => ENNReal.ofReal (‖b.repr x m‖^2) • Measure.dirac (tuple a m)

theorem jointMeasure_apply (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (x : HN L N) (B : Set (Fin d → ℝ)) :
    jointMeasure b a x B = ENNReal.ofReal (‖jointProjection b a B x‖^2) := by
  rw [jointMeasure,Measure.sum_apply_of_countable]
  have hn : ‖jointProjection b a B x‖^2 =
      ∑' m, if tuple a m ∈ B then ‖b.repr x m‖^2 else 0 := by
    rw [← b.repr.norm_map,Energy.norm_sq_eq_tsum]
    apply tsum_congr
    intro m
    rw [jointProjection_coord]
    split_ifs <;> simp
  rw [hn,ENNReal.ofReal_tsum_of_nonneg
    (fun m => by split_ifs <;> positivity)
    (Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
      (fun m => by split_ifs <;> simp) (Energy.summable_sq (b.repr x)))]
  apply tsum_congr
  intro m
  simp only [Measure.smul_apply,Measure.dirac_apply,smul_eq_mul]
  split_ifs <;> simp_all

theorem jointMeasure_univ (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (x : HN L N) :
    jointMeasure b a x Set.univ = ENNReal.ofReal (‖x‖^2) := by
  rw [jointMeasure_apply,jointProjection_univ]
  rfl

instance jointMeasure_finite (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (x : HN L N) :
    IsFiniteMeasure (jointMeasure b a x) := ⟨by rw [jointMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- Integration is a literal coefficient sum, including infinite values. -/
theorem joint_lintegral (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (x : HN L N)
    (f : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ t, f t ∂jointMeasure b a x = ∑' m, ENNReal.ofReal (‖b.repr x m‖^2) * f (tuple a m) := by
  simp only [jointMeasure,lintegral_sum_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]

/-- Exact square-integral domain for any real joint symbol, including sums
whose maximal domain can strictly exceed the common individual domain. -/
theorem joint_domain_iff (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : HN L N) :
    x ∈ (multiplier b (fun m => f (tuple a m))).domain ↔
      (∫⁻ t, ENNReal.ofReal (|f t|^2) ∂jointMeasure b a x) ≠ ⊤ := by
  change x ∈ domain b (fun m => f (tuple a m)) ↔ _
  rw [mem_domain,joint_lintegral]
  have he : (fun m => ENNReal.ofReal (‖b.repr x m‖^2)*ENNReal.ofReal (|f (tuple a m)|^2)) =
      (fun m => ENNReal.ofReal (|f (tuple a m)|^2*‖b.repr x m‖^2)) := by
    funext m
    rw [← ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  rw [he]
  constructor
  · intro h
    apply Summable.tsum_ofReal_ne_top
    simpa only [HilbertBasis.repr_apply_apply] using h
  · intro h
    have hr := ENNReal.summable_toReal h
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      HilbertBasis.repr_apply_apply] using hr

/-- The j-th coordinate spectral projection is exactly the individual one. -/
theorem coordinate_projection (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (j : Fin d) (C : Set ℝ) :
    jointProjection b a {t | t j ∈ C} = (resolution b (a j)).toFun C := rfl

theorem strong_commutation (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (j k : Fin d) (B C : Set ℝ) :
    Commute ((resolution b (a j)).toFun B) ((resolution b (a k)).toFun C) := by
  change Commute (projection b _) (projection b _)
  show projection b _ * projection b _ = projection b _ * projection b _
  rw [projection_inter,projection_inter,Set.inter_comm]

/-- The literal bounded j-th coordinate integrals converge on precisely
that coordinate's maximal square-integral domain. -/
theorem coordinate_cutoff_limit (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (j : Fin d) (x : HN L N)
    (hx : (∫⁻ t, ENNReal.ofReal (|t j|^2) ∂jointMeasure b a x) ≠ ⊤) :
    ∃ hdomain : x ∈ (multiplier b (a j)).domain,
      Tendsto (fun n => Ext025B6SpectralLimits.boundedCutoff b (a j) n x)
        atTop (𝓝 (multiplier b (a j) ⟨x,hdomain⟩)) := by
  have hd : x ∈ (multiplier b (a j)).domain :=
    (joint_domain_iff b a (fun t => t j) x).mpr hx
  exact ⟨hd,Ext025B6SpectralLimits.cutoff_strong b (a j) x hd⟩

/-- A real Borel joint symbol has its exact selfadjoint maximal multiplier.
On this countable represented space the result holds for every finite-valued symbol. -/
theorem joint_symbol_selfAdjoint (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (f : (Fin d → ℝ) → ℝ) :
    IsSelfAdjoint (multiplier b (fun m => f (tuple a m))) :=
  multiplier_selfAdjoint b _

/-- The bounded joint integral is constructed directly in the physical basis. -/
def boundedJoint (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (f : (Fin d → ℝ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ t, ‖f t‖ ≤ C) :
    HN L N →L[ℂ] HN L N :=
  Ext025SCalculus.bounded b (fun m => f (tuple a m)) C hC (fun m => hf (tuple a m))

/-- The joint spectral integral's exact scalar square-integral identity. -/
theorem boundedJoint_square (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (f : (Fin d → ℝ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ t, ‖f t‖ ≤ C)
    (x : HN L N) :
    (∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂jointMeasure b a x) =
      ENNReal.ofReal (‖boundedJoint b a f C hC hf x‖^2) := by
  rw [joint_lintegral,← b.repr.norm_map,Energy.norm_sq_eq_tsum,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
      (Energy.summable_sq (b.repr (boundedJoint b a f C hC hf x)))]
  apply tsum_congr
  intro m
  rw [boundedJoint,Ext025SCalculus.bounded_coord,norm_mul,mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _),mul_comm]

/-- Complex adjoints of the actual bounded joint integral. -/
theorem boundedJoint_star (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (f : (Fin d → ℝ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ t, ‖f t‖ ≤ C) :
    (boundedJoint b a f C hC hf).adjoint =
      boundedJoint b a (fun t => star (f t)) C hC (fun t => by simpa using hf t) :=
  Ext025SCalculus.bounded_star b _ C hC _

end QuantumNLS.Ext025B7JointResolution

#print axioms QuantumNLS.Ext025B7JointResolution.tuple
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection_coord
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection_univ
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection_empty
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection_inter
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection_adjoint
#print axioms QuantumNLS.Ext025B7JointResolution.jointProjection_additive
#print axioms QuantumNLS.Ext025B7JointResolution.jointMeasure
#print axioms QuantumNLS.Ext025B7JointResolution.jointMeasure_apply
#print axioms QuantumNLS.Ext025B7JointResolution.jointMeasure_univ
#print axioms QuantumNLS.Ext025B7JointResolution.joint_lintegral
#print axioms QuantumNLS.Ext025B7JointResolution.joint_domain_iff
#print axioms QuantumNLS.Ext025B7JointResolution.coordinate_projection
#print axioms QuantumNLS.Ext025B7JointResolution.strong_commutation
#print axioms QuantumNLS.Ext025B7JointResolution.coordinate_cutoff_limit

#print axioms QuantumNLS.Ext025B7JointResolution.joint_symbol_selfAdjoint
#print axioms QuantumNLS.Ext025B7JointResolution.boundedJoint
#print axioms QuantumNLS.Ext025B7JointResolution.boundedJoint_square
#print axioms QuantumNLS.Ext025B7JointResolution.boundedJoint_star

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B7JointResolution." then
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Ext025B7JointResolution audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
