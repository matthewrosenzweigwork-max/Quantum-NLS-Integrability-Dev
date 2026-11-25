import QuantumNLS.Def021UnitPeriodR41b
import QuantumNLS.GlobalCompatFinalR47a

/-! Literal physical period conversion. The map is identified with the Fourier
isometry, rather than postulated to preserve its differential. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace QuantumNLS.PeriodFieldR42b
open PhysicalTensor (L2T)
open HierarchyScaling (dilation)
open QuantumNLS.Fourier (fourierL2 coeff fourierL2_apply)
open AddCircle (haarAddCircle)
variable (L : ℝ) [Fact (0 < L)]

def circleEquiv : AddCircle (1 : ℝ) ≃ₜ AddCircle L :=
  AddCircle.homeomorphAddCircle 1 L one_ne_zero (Fact.out : 0 < L).ne'

theorem circleEquiv_eq : (circleEquiv L : AddCircle (1 : ℝ) → AddCircle L) = dilation L := rfl

theorem dilation_coe (x : ℝ) : dilation L (x : AddCircle (1 : ℝ)) =
    (L*x : ℝ) := by simp [dilation, mul_comm]

theorem haar_preserving : MeasurePreserving (dilation L)
    (haarAddCircle : Measure (AddCircle (1 : ℝ)))
    (haarAddCircle : Measure (AddCircle L)) := by
  exact (AddCircle.equivAddCircle 1 L one_ne_zero (Fact.out : 0 < L).ne').toAddMonoidHom.measurePreserving
    (AddCircle.continuous_equivAddCircle 1 L _ _)
    (AddCircle.equivAddCircle 1 L _ _).surjective (by simp)

theorem haar_eq_inv_volume : (haarAddCircle : Measure (AddCircle L)) =
    (ENNReal.ofReal L)⁻¹ • (volume : Measure (AddCircle L)) := by
  rw [Fourier.volume_eq_smul_haar]
  rw [smul_smul, ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (Fact.out : 0 < L)))
    ENNReal.ofReal_ne_top, one_smul]

theorem unit_volume : (volume : Measure (AddCircle (1 : ℝ))) = haarAddCircle := by
  rw [Fourier.volume_eq_smul_haar]
  simp

theorem mem_period (u : L2T L) :
    MemLp (fun x : AddCircle (1 : ℝ) => (Real.sqrt L : ℂ)*u (dilation L x)) 2 volume := by
  have hu : MemLp (u : AddCircle L → ℂ) 2 haarAddCircle := by
    rw [haar_eq_inv_volume]
    exact (Lp.memLp u).smul_measure (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Fact.out : 0 < L))))
  rw [unit_volume]
  exact (hu.comp_measurePreserving (haar_preserving L)).const_mul _

def period (u : L2T L) : L2T 1 := (mem_period L u).toLp _

theorem period_ae (u : L2T L) : (period L u : AddCircle (1 : ℝ) → ℂ) =ᵐ[volume]
    fun x => (Real.sqrt L : ℂ)*u (dilation L x) := (mem_period L u).coeFn_toLp

theorem fourier_dilation (n : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier n (dilation L x) = fourier n x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    rw [dilation_coe, fourier_coe_apply, fourier_coe_apply]
    congr 1
    push_cast
    field_simp [(Fact.out : 0 < L).ne']

theorem fourier_period (u : L2T L) : fourierL2 1 (period L u) = fourierL2 L u := by
  apply lp.ext
  funext n
  rw [fourierL2_apply, fourierL2_apply,
    Fourier.coeff_congr_ae 1 (period_ae L u),
    Fourier.coeff_eq_sqrt_mul_fourierCoeff, Fourier.coeff_eq_sqrt_mul_fourierCoeff]
  simp only [Real.sqrt_one, Complex.ofReal_one, one_mul]
  unfold fourierCoeff
  simp only [smul_eq_mul]
  rw [show (fun x : AddCircle (1 : ℝ) => fourier (-n) x * ((Real.sqrt L : ℂ)*u (dilation L x))) =
    (fun x => (Real.sqrt L : ℂ)*(fourier (-n) (dilation L x)*u (dilation L x))) by
      funext x; rw [fourier_dilation]; ring,
    integral_const_mul]
  exact congrArg (fun z : ℂ => (Real.sqrt L : ℂ)*z)
    ((haar_preserving L).integral_comp (circleEquiv L).toMeasurableEquiv.measurableEmbedding
      (fun x : AddCircle L => fourier (-n) x * u x))

/-- The actual ae period map is exactly the complex Hilbert isometry. -/
def periodEquiv : L2T L ≃ₗᵢ[ℂ] L2T 1 := (fourierL2 L).trans (fourierL2 1).symm

theorem period_eq (u : L2T L) : period L u = periodEquiv L u := by
  apply (fourierL2 1).injective
  rw [fourier_period]
  simp [periodEquiv]

theorem norm_period (u : L2T L) : ‖period L u‖ = ‖u‖ := by
  rw [period_eq]
  exact (periodEquiv L).norm_map u

theorem inner_period (u v : L2T L) :
    inner ℂ (period L u) (period L v) = inner ℂ u v := by
  rw [period_eq, period_eq]
  exact (periodEquiv L).inner_map_map u v

end QuantumNLS.PeriodFieldR42b

#print axioms QuantumNLS.PeriodFieldR42b.circleEquiv_eq
#print axioms QuantumNLS.PeriodFieldR42b.dilation_coe
#print axioms QuantumNLS.PeriodFieldR42b.haar_preserving
#print axioms QuantumNLS.PeriodFieldR42b.haar_eq_inv_volume
#print axioms QuantumNLS.PeriodFieldR42b.unit_volume
#print axioms QuantumNLS.PeriodFieldR42b.mem_period
#print axioms QuantumNLS.PeriodFieldR42b.period_ae
#print axioms QuantumNLS.PeriodFieldR42b.fourier_dilation
#print axioms QuantumNLS.PeriodFieldR42b.fourier_period
#print axioms QuantumNLS.PeriodFieldR42b.period_eq
#print axioms QuantumNLS.PeriodFieldR42b.norm_period
#print axioms QuantumNLS.PeriodFieldR42b.inner_period

-- R42b final aggregate audit
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PeriodFieldR42b." ||
        n.toString.startsWith "_private.QuantumNLS.PeriodFieldR42b." then
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
