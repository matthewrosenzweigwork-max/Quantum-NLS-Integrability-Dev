import QuantumNLS.PhysicalIndexedMasses
import QuantumNLS.PhysicalQuantumMeasure
import QuantumNLS.L2DiscriminantRegularity

/-! Physical SourceFacts at the vacuum, with the actual L2ST1 transfer and the
canonical quantum measure. The nonzero arbitrary-input construction is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix
namespace QuantumNLS.PhysicalVacuumSourceFacts
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental
open QuantumNLS.L2SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

def P₀ : Mat2 := !![1, 0; 0, 0]
def P₁ : Mat2 := !![0, 0; 0, 1]

def freeMatrix (z : ℂ) (x : ℝ) : Mat2 :=
  Complex.exp (-(Complex.I * z / 2) * x) • P₀ +
    Complex.exp (Complex.I * z / 2 * x) • P₁

theorem free_fundamental (κ : ℝ) (z : ℂ) :
    IsFundamental (balCoef κ (fun _ => 0) z) (freeMatrix z) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [freeMatrix, P₀, P₁]
  · intro x
    have h₀ := ((hasDerivAt_id x).ofReal_comp.const_mul (-(Complex.I * z / 2))).cexp
    have h₁ := ((hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * z / 2)).cexp
    apply ((h₀.smul_const P₀).add (h₁.smul_const P₁)).congr_deriv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P₀, P₁, freeMatrix, balCoef, coef, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Vacuum monodromy, proved by representative independence and uniqueness. -/
theorem transfer_zero (κ : ℝ) (z : ℂ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    L2SpatialTransfer.spatialTransfer κ (0 : PhysicalTensor.L2T L) z x = freeMatrix z x := by
  have hp : (fun _ : AddCircle L => (0 : ℂ)) =ᵐ[volume]
      (0 : PhysicalTensor.L2T L) := (Lp.coeFn_zero _ _ _).symm
  have he := spatialTransfer_eq_of_representative κ (0 : PhysicalTensor.L2T L) hp z hx
  rw [← he]
  exact L2SpatialTransfer.transfer_eq_classical continuous_const (free_fundamental κ z) hx

/-- Exact free trace for the frozen L2ST1 definition. -/
theorem discriminant_zero (κ : ℝ) (z : ℂ) :
    L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) z =
      2 * Complex.cos ((L : ℂ) * z / 2) := by
  unfold L2SpatialTransfer.discriminant
  rw [transfer_zero κ z ⟨(Fact.out : 0 < L).le, le_rfl⟩, Matrix.trace_fin_two,
    Complex.two_cos]
  have h00 : freeMatrix z L 0 0 = Complex.exp (-(Complex.I * z / 2) * (L : ℂ)) := by
    simp [freeMatrix, P₀, P₁]
  have h11 : freeMatrix z L 1 1 = Complex.exp (Complex.I * z / 2 * (L : ℂ)) := by
    simp [freeMatrix, P₀, P₁]
  rw [h00, h11]
  have h₀ : -(Complex.I * z / 2) * (L : ℂ) = -((L : ℂ) * z / 2) * Complex.I := by ring
  have h₁ : Complex.I * z / 2 * (L : ℂ) = ((L : ℂ) * z / 2) * Complex.I := by ring
  rw [h₀, h₁, add_comm]

theorem discriminant_zero_real (κ : ℝ) (t : ℝ) :
    (L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) (t : ℂ)).re =
      2 * Real.cos (L * t / 2) := by
  rw [discriminant_zero]
  have he : (L : ℂ) * (t : ℂ) / 2 = ((L * t / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [he, Complex.mul_re, Complex.cos_ofReal_re]
  norm_num

/-- An actual inhabitant of SourceFacts at u=0; no analytic fields are supplied. -/
def sourceFacts (κ : ℝ) : PhysicalIndexedMasses.SourceFacts L κ (0 : PhysicalTensor.L2T L) where
  M := 0
  finite := inferInstance
  full_mass := by simp
  atomless := ⟨fun _ => rfl⟩
  γ := fun x => (L : ℂ) * (x : ℂ) / 2
  boundary := by
    intro x
    have hc : Continuous (fun ε : ℝ =>
        (L : ℂ) * ((x : ℂ) + (ε : ℂ) * Complex.I) / 2) := by fun_prop
    simpa [SpatialTransfer.boundaryPhase, EmpiricalRapidity.cauchyTransform] using
      (hc.tendsto (0 : ℝ)).mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  continuous := by fun_prop
  monotone := by
    intro x y hxy
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxy (Fact.out : 0 < L).le) (by norm_num)
  onto := by
    intro y
    refine ⟨2 * y / L, ?_⟩
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp [(Fact.out : 0 < L).ne']
  continuous_discriminant := L2DiscriminantRegularity.continuous_discriminant κ 0
  real_discriminant := L2DiscriminantRegularity.discriminant_real κ 0
  quantum_identity := by
    intro z hz
    simp only [SpatialTransfer.boundaryPhase, EmpiricalRapidity.cauchyTransform,
      integral_zero_measure, mul_zero, sub_zero]
    exact (discriminant_zero κ z).symm
  positive_band_derivative := by
    intro x hx
    have he : (fun y : ℝ => ((L : ℂ) * (y : ℂ) / 2).re) =
        (fun y : ℝ => L * y / 2) := by
      funext y
      simp
    rw [he]
    have hd : HasDerivAt (fun y : ℝ => L * y / 2) (L / 2) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul L).div_const 2
    rw [hd.deriv]
    exact div_pos Fact.out (by norm_num)
  gap_constancy := by
    intro a b hab hg
    have hx := hg ((a + b) / 2) ⟨by linarith, by linarith⟩
    rw [discriminant_zero_real, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hx
    have := Real.abs_cos_le_one (L * ((a + b) / 2) / 2)
    linarith

/-- The constructed vacuum SourceFacts use precisely the canonical quantum measure. -/
theorem sourceFacts_measure {κ : ℝ} (hκ : 0 < κ) :
    (sourceFacts (L := L) κ).M = PhysicalQuantumMeasure.measure (L := L) hκ 0 := by
  simp [sourceFacts]

/-- The named DEF-014 conclusion at vacuum has no SourceFacts parameter. -/
theorem vacuum_DEF014 (κ : ℝ) :
    (∀ n : ℤ, ∃! b : ℝ,
      ((sourceFacts (L := L) κ).γ b).re = MonotoneIndexedMasses.level n) ∧
    StrictMono (sourceFacts (L := L) κ).phase.separator ∧
    (∀ n, ((sourceFacts (L := L) κ).masses).1 n =
      ((sourceFacts (L := L) κ).M
        (Ioo ((sourceFacts (L := L) κ).phase.separator (n - 1))
          ((sourceFacts (L := L) κ).phase.separator n))).toReal) ∧
    (∀ n, 0 ≤ ((sourceFacts (L := L) κ).masses).1 n) ∧
    Summable (fun n => ((sourceFacts (L := L) κ).masses).1 n) ∧
    (∑' n, ((sourceFacts (L := L) κ).masses).1 n) = 0 := by
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
    PhysicalIndexedMasses.«DEF-014» (κ := κ) (0 : PhysicalTensor.L2T L) (sourceFacts κ)

end QuantumNLS.PhysicalVacuumSourceFacts

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.P₀
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.P₁
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.freeMatrix
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.free_fundamental
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.transfer_zero
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.discriminant_zero
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.discriminant_zero_real
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.sourceFacts
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.sourceFacts_measure
#print axioms QuantumNLS.PhysicalVacuumSourceFacts.vacuum_DEF014

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalVacuumSourceFacts." then
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
