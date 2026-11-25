import QuantumNLS.Ext005MomentDomainR33b
import QuantumNLS.Ext005SourceIntervalR32b

/-! Same-operator comparison for the physical EXT-005 instance. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap Set Filter MeasureTheory UniformSpace
namespace QuantumNLS.Ext005SameComparisonR121
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005SourceHypothesesR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def sameB (A : PositiveOperator H) : NonnegativeOperator H where
  op := A.op
  selfAdjoint := A.selfAdjoint
  nonneg u := (sq_nonneg _).trans (A.lower u)

def toShiftedCore (A : PositiveOperator H) (v : Core A) : Core (plusOne (sameB A)) :=
  ⟨v.val, v.property⟩

lemma shifted_core_norm (A : PositiveOperator H) (v : Core A) :
    ‖(toShiftedCore A v)‖ ^ 2 = ‖v‖ ^ 2 + ‖coreVal A v‖ ^ 2 := by
  rw [core_norm_sq, core_norm_sq]
  change (⟪coreVal A v, A.op v + (1 : ℂ) • coreVal A v⟫_ℂ).re = _
  simp only [one_smul, inner_add_right, Complex.add_re]
  exact congrArg (fun r : ℝ => (⟪coreVal A v, A.op (show A.op.domain from v)⟫_ℂ).re + r)
    (norm_sq_eq_re_inner (𝕜 := ℂ) (coreVal A v)).symm

def shiftedCore (A : PositiveOperator H) : Core A →L[ℂ] Core (plusOne (sameB A)) :=
  LinearMap.mkContinuous
    { toFun := toShiftedCore A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    2 (fun v => by
      change ‖(toShiftedCore A v)‖ ≤ 2 * ‖v‖
      have he := shifted_core_norm A v
      have hb := core_norm_domination A v
      nlinarith [norm_nonneg v, norm_nonneg (coreVal A v),
        norm_nonneg (toShiftedCore A v)])

def shiftedCompletion (A : PositiveOperator H) :
    FormDomain A →L[ℂ] FormDomain (plusOne (sameB A)) :=
  (Completion.toComplL.comp (shiftedCore A)).extend Completion.toComplL

lemma shiftedCompletion_coe (A : PositiveOperator H) (v : Core A) :
    shiftedCompletion A (v : FormDomain A) =
      ((toShiftedCore A v) : FormDomain (plusOne (sameB A))) :=
  (Completion.toComplL.comp (shiftedCore A)).extend_eq
    Completion.denseRange_coe (Completion.isUniformInducing_coe _) v

lemma shiftedCompletion_pair (A : PositiveOperator H) (u : FormDomain A) :
    inclusion (plusOne (sameB A)) (shiftedCompletion A u) = inclusion A u := by
  refine Completion.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro v
  rw [shiftedCompletion_coe, inclusion_coe, inclusion_coe]
  rfl

theorem sameDomain (A : PositiveOperator H) : FormContained A (plusOne (sameB A)) :=
  fun u => ⟨shiftedCompletion A u, shiftedCompletion_pair A u⟩

lemma comparison_eq (A : PositiveOperator H) (u : FormDomain A) :
    comparison A (plusOne (sameB A)) (sameDomain A) u = shiftedCompletion A u := by
  apply Ext005OperatorFormR113.inclusion_injective
  rw [comparison_pair, shiftedCompletion_pair]

lemma same_comparison_energy (A : PositiveOperator H) (u : FormDomain A) :
    comparisonEnergy A (sameB A) (sameDomain A) u = ‖u‖ ^ 2 := by
  have hn : ‖shiftedCompletion A u‖ ^ 2 = ‖u‖ ^ 2 + ‖inclusion A u‖ ^ 2 := by
    refine Completion.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro v
    rw [shiftedCompletion_coe, Completion.norm_coe, Completion.norm_coe, inclusion_coe]
    exact shifted_core_norm A v
  unfold comparisonEnergy
  rw [comparison_eq, hn]
  ring

omit [CompleteSpace H] in
/-- Resolvents of one operator commute, including coincident parameters. -/
lemma stronglyCommute_self (T : H →ₗ.[ℂ] H) : StronglyCommute T T := by
  intro z w _ _ R S hR hS
  have rid (x : H) : R x - S x = (z-w) • R (S x) := by
    obtain ⟨hx, he⟩ := hS.1 x
    have hr := hR.2 ⟨S x, hx⟩
    have ht : T ⟨S x, hx⟩ = x + w • S x := by
      exact sub_eq_iff_eq_add.mp he
    rw [ht, map_sub, map_add, map_smul, map_smul] at hr
    change R x + w • R (S x) - z • R (S x) = S x at hr
    rw [sub_smul]
    calc
      R x - S x = R x - (R x + w • R (S x) - z • R (S x)) :=
        congrArg (fun y => R x - y) hr.symm
      _ = z • R (S x) - w • R (S x) := by abel
  have sid (x : H) : R x - S x = (z-w) • S (R x) := by
    obtain ⟨hx, he⟩ := hR.1 x
    have hs := hS.2 ⟨R x, hx⟩
    have ht : T ⟨R x, hx⟩ = x + z • R x := sub_eq_iff_eq_add.mp he
    rw [ht, map_sub, map_add, map_smul, map_smul] at hs
    change S x + z • S (R x) - w • S (R x) = R x at hs
    rw [sub_smul]
    calc
      R x - S x = (S x + z • S (R x) - w • S (R x)) - S x :=
        congrArg (fun y => y - S x) hs.symm
      _ = z • S (R x) - w • S (R x) := by abel
  ext x
  by_cases hzw : z = w
  · have hrs : R = S := by
      ext y
      have hh := rid y
      rw [hzw, sub_self, zero_smul] at hh
      exact sub_eq_zero.mp hh
    rw [hrs]
  · exact (smul_right_injective H (sub_ne_zero.mpr hzw)) ((rid x).symm.trans (sid x))

end QuantumNLS.Ext005SameComparisonR121
#print axioms QuantumNLS.Ext005SameComparisonR121.same_comparison_energy
#print axioms QuantumNLS.Ext005SameComparisonR121.stronglyCommute_self

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SameComparisonR121." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SameComparisonR121." then
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
  Lean.logInfo m!"R121 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
