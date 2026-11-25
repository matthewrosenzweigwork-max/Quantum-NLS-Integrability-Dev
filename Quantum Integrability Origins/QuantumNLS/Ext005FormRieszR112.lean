import QuantumNLS.Ext005HilbertD3R112

/-! R112: construct the antidual force of an actual bounded real bilinear
form by Riesz representation. Operator measurability, norm bounds and the
zero diagonal are derived from the form, rather than assumed of a chosen K.
A complex Schrodinger form still needs its checked realification bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005FormRieszR112
open Ext005IntervalChainR111 Ext005HilbertEnergyR112 Ext005HilbertD3R112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Riesz representation as a bounded linear map on the space of forms. -/
def rieszMap : (Q →L[ℝ] Q →L[ℝ] ℝ) →L[ℝ] Q →L[ℝ] Q :=
  ContinuousLinearMap.compL ℝ Q (StrongDual ℝ Q) Q
    (toDual ℝ Q).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma riesz_pair (b : Q →L[ℝ] Q →L[ℝ] ℝ) (u v : Q) :
    ⟪rieszMap b u, v⟫_ℝ = b u v :=
  continuousLinearMapOfBilin_apply b u v

lemma riesz_norm_le (b : Q →L[ℝ] Q →L[ℝ] ℝ) : ‖rieszMap b‖ ≤ ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (rieszMap (Q := Q) b) (norm_nonneg b) ?_
  intro u
  change ‖(toDual ℝ Q).symm (b u)‖ ≤ ‖b‖ * ‖u‖
  rw [(toDual ℝ Q).symm.norm_map]
  exact ContinuousLinearMap.le_opNorm b u

/-- Form hypotheses imply operator hypotheses for the intrinsic D3 theorem. -/
theorem form_energy_unique_source_interval (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (x y : ℝ → H) (b : ℝ → Q →L[ℝ] Q →L[ℝ] ℝ)
    (hx : ContinuousOn x (Ico 0 1)) (hy : ContinuousOn y (Ico 0 1))
    (hex : ∀ T ∈ Ioo (0 : ℝ) 1, EnergyBounded i (Icc 0 T) x)
    (hey : ∀ T ∈ Ioo (0 : ℝ) 1, EnergyBounded i (Icc 0 T) y)
    (hb : AEStronglyMeasurable b (volume.restrict (Ico 0 1)))
    (hbb : ∀ T ∈ Ioo (0 : ℝ) 1, ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ t, t ∈ Icc 0 T → ‖b t‖ ≤ M)
    (hdiag : ∀ᵐ t, t ∈ Ico (0 : ℝ) 1 → ∀ w : Q, b t w w = 0)
    (hwx : WeakDerivativeOn (Ioo 0 1) (fun t => i.adjoint (x t))
      (fun t => rieszMap (b t) (lift i (x t))))
    (hwy : WeakDerivativeOn (Ioo 0 1) (fun t => i.adjoint (y t))
      (fun t => rieszMap (b t) (lift i (y t))))
    (hinit : x 0 = y 0) : ∀ t ∈ Ico (0 : ℝ) 1, x t = y t := by
  apply energy_unique_source_interval i hinj hdense x y (fun t => rieszMap (b t))
    hx hy hex hey ((rieszMap (Q := Q)).continuous.comp_aestronglyMeasurable hb)
  · intro T hT
    obtain ⟨M, hM, hbm⟩ := hbb T hT
    exact ⟨M, hM, hbm.mono fun t ht htI => (riesz_norm_le (b t)).trans (ht htI)⟩
  · filter_upwards [hdiag] with t ht htI w
    calc
      _ = ⟪rieszMap (b t) w, w⟫_ℝ := real_inner_comm _ _
      _ = b t w w := riesz_pair (b t) w w
      _ = 0 := ht htI w
  · exact hwx
  · exact hwy
  · exact hinit

end QuantumNLS.Ext005FormRieszR112
#print axioms QuantumNLS.Ext005FormRieszR112.riesz_pair
#print axioms QuantumNLS.Ext005FormRieszR112.form_energy_unique_source_interval

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005FormRieszR112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005FormRieszR112." then
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
  Lean.logInfo m!"R112 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
