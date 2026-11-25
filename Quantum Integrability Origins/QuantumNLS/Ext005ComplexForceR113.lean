import QuantumNLS.Ext005FormRieszR112

/-! Complex symmetric bounded forms give the real skew force required by D3.
This module constructs the real force and proves its norm, continuity,
measurability and diagonal properties. No source A,B scale is postulated. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005ComplexForceR113
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q

/-- Multiplication by -i, followed by restriction to the underlying real space. -/
def forceMap : (Q →L[ℂ] Q) →L[ℝ] Q →L[ℝ] Q :=
  (ContinuousLinearMap.restrictScalarsIsometry ℝ (𝕜 := ℂ) (E := Q) (Fₗ := Q)
    (𝕜'' := ℝ)).toContinuousLinearMap ∘L
    ((-Complex.I) • ContinuousLinearMap.id ℂ (Q →L[ℂ] Q)).restrictScalars ℝ

@[simp] lemma force_apply (L : Q →L[ℂ] Q) (u : Q) :
    forceMap L u = (-Complex.I) • L u := rfl

lemma force_norm (L : Q →L[ℂ] Q) : ‖forceMap L‖ = ‖L‖ := by
  change ‖((-Complex.I) • L).restrictScalars ℝ‖ = ‖L‖
  rw [ContinuousLinearMap.norm_restrictScalars, norm_smul]
  simp

lemma force_pair (L : Q →L[ℂ] Q) (u v : Q) :
    ⟪v, forceMap L u⟫_ℝ = (⟪v, L u⟫_ℂ).im := by
  change (⟪v, (-Complex.I) • L u⟫_ℂ).re = _
  simp [inner_smul_right, Complex.mul_re]

/-- Symmetry of the complex form implies a vanishing real diagonal. -/
lemma force_diagonal (L : Q →L[ℂ] Q) (hsym : L.IsSymmetric) (u : Q) :
    ⟪u, forceMap L u⟫_ℝ = 0 := by
  rw [force_pair]
  have h : starRingEnd ℂ (⟪u, L u⟫_ℂ) = ⟪u, L u⟫_ℂ := by
    rw [inner_conj_symm]
    exact hsym u u
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

lemma force_measurable (L : ℝ → Q →L[ℂ] Q) (μ : Measure ℝ)
    (hL : AEStronglyMeasurable L μ) :
    AEStronglyMeasurable (fun t => forceMap (L t)) μ :=
  forceMap.continuous.comp_aestronglyMeasurable hL

lemma force_local_bound (L : ℝ → Q →L[ℂ] Q) (S : Set ℝ) (M : ℝ)
    (h : ∀ᵐ t, t ∈ S → ‖L t‖ ≤ M) :
    ∀ᵐ t, t ∈ S → ‖forceMap (L t)‖ ≤ M := by
  simpa only [force_norm] using h

/-- The real form obtained from the imaginary part of the complex form. -/
def realForm (L : Q →L[ℂ] Q) : Q →L[ℝ] Q →L[ℝ] ℝ :=
  (innerSL ℝ).comp (forceMap L)

lemma realForm_apply (L : Q →L[ℂ] Q) (u v : Q) :
    realForm L u v = (⟪v, L u⟫_ℂ).im := by
  change ⟪forceMap L u, v⟫_ℝ = _
  rw [real_inner_comm, force_pair]

lemma realForm_riesz [CompleteSpace Q] (L : Q →L[ℂ] Q) :
    Ext005FormRieszR112.rieszMap (realForm L) = forceMap L := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Ext005FormRieszR112.riesz_pair]
  rfl

end QuantumNLS.Ext005ComplexForceR113
#print axioms QuantumNLS.Ext005ComplexForceR113.force_diagonal
#print axioms QuantumNLS.Ext005ComplexForceR113.realForm_riesz

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ComplexForceR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ComplexForceR113." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R113 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
