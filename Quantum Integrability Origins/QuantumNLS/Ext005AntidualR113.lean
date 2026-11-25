import QuantumNLS.Ext005ComplexForceR113

/-! The complex antidual and its isometric realification. The construction
uses the actual continuous conjugate-linear functionals, not an assumed
Riesz coordinate identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005AntidualR113
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q

abbrev Antidual (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] :=
  Q →L⋆[ℂ] ℂ

/-- Restriction of a complex antilinear functional to its real part. -/
def realPart (f : Antidual Q) : StrongDual ℝ Q where
  toFun v := (f v).re
  map_add' u v := by simp
  map_smul' r v := by
    change (f ((r : ℂ) • v)).re = r * (f v).re
    rw [map_smulₛₗ]
    simp
  cont := Complex.continuous_re.comp f.continuous

@[simp] lemma realPart_apply (f : Antidual Q) (u : Q) : realPart f u = (f u).re := rfl

lemma realPart_norm_le (f : Antidual Q) : ‖realPart f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  exact (Complex.abs_re_le_norm (f u)).trans (f.le_opNorm u)

lemma realPart_injective : Function.Injective (realPart (Q := Q)) := by
  intro f g h
  apply ContinuousLinearMap.ext
  intro u
  apply Complex.ext
  · exact congrArg (fun k : StrongDual ℝ Q => k u) h
  · have hi := congrArg (fun k : StrongDual ℝ Q => k (Complex.I • u)) h
    simpa [realPart, Complex.mul_re] using hi

/-- A real functional has a unique complex antilinear extension. -/
lemma realPart_riesz [CompleteSpace Q] (g : StrongDual ℝ Q) :
    realPart (innerSLFlip ℂ ((toDual ℝ Q).symm g)) = g := by
  ext u
  change (⟪u, (toDual ℝ Q).symm g⟫_ℂ).re = g u
  change ⟪u, (toDual ℝ Q).symm g⟫_ℝ = g u
  rw [real_inner_comm]
  exact toDual_symm_apply

lemma antidual_riesz [CompleteSpace Q] (f : Antidual Q) :
    innerSLFlip ℂ ((toDual ℝ Q).symm (realPart f)) = f :=
  realPart_injective (realPart_riesz (realPart f))

lemma realPart_norm [CompleteSpace Q] (f : Antidual Q) : ‖realPart f‖ = ‖f‖ := by
  apply le_antisymm (realPart_norm_le f)
  conv_lhs => rw [← antidual_riesz f]
  calc
    _ ≤ ‖(toDual ℝ Q).symm (realPart f)‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      exact (norm_inner_le_norm u _).trans_eq (mul_comm _ _)
    _ = ‖realPart f‖ := (toDual ℝ Q).symm.norm_map _

/-- Realification is a continuous real-linear isometry onto the real dual. -/
def realPartMap : Antidual Q →L[ℝ] StrongDual ℝ Q :=
  LinearMap.mkContinuous
    { toFun := realPart
      map_add' := by intro f g; ext u; simp
      map_smul' := by intro r f; ext u; simp }
    1 (by
      intro f
      change ‖realPart f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using realPart_norm_le f)

/-- Actual antidual to Hilbert Riesz coordinates. -/
def coordinates [CompleteSpace Q] : Antidual Q →L[ℝ] Q :=
  (toDual ℝ Q).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L realPartMap

lemma coordinates_pair [CompleteSpace Q] (f : Antidual Q) (u : Q) :
    ⟪u, coordinates f⟫_ℝ = (f u).re := by
  rw [real_inner_comm]
  exact toDual_symm_apply

lemma coordinates_norm [CompleteSpace Q] (f : Antidual Q) : ‖coordinates f‖ = ‖f‖ := by
  change ‖(toDual ℝ Q).symm (realPart f)‖ = _
  rw [(toDual ℝ Q).symm.norm_map, realPart_norm]

lemma coordinates_riesz [CompleteSpace Q] (u : Q) :
    coordinates (innerSLFlip ℂ u) = u := by
  apply ext_inner_left ℝ
  intro v
  rw [coordinates_pair]
  rfl

end QuantumNLS.Ext005AntidualR113
#print axioms QuantumNLS.Ext005AntidualR113.antidual_riesz
#print axioms QuantumNLS.Ext005AntidualR113.coordinates_norm

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005AntidualR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005AntidualR113." then
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
