import QuantumNLS.Q07GradientRemovalR24
import QuantumNLS.WindowDualGradientR44b

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: the actual accepted scalar contour error, pulled back in
ALL real directions through a C¹ inverse restriction. The compact set and
the inverse derivative bounds are fixed before the cutoff. No scalar tail
estimate or gradient estimate is an input to the theorems below. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Q07GradientRemovalR24 QuantumNLS.Q07SobolevModelR24
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.Q07TailBindingR24 QuantumNLS.PROP017UniformN
namespace QuantumNLS.WindowScalarPullbackR44b
variable {L κ : ℝ} [Fact (0 < L)]

/-- Pointwise form of the accepted bound, on its actual H^(2r+4) carrier. -/
theorem scalar_bound (hκ : 0 < κ) (r : ℕ) (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      ∀ u : H02 L (regularity r), ‖u‖ ≤ B →
        DifferentiableAt ℝ (T (L := L) hκ r h l) u ∧
        ‖fderiv ℝ (T (L := L) hκ r h l) u‖ ≤ C*(cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨C,hC,l0,hb⟩ := model_bound (L := L) hκ r B hh
  refine ⟨C,hC,l0,?_⟩
  intro l hl u hu
  have ha : 0 ≤ cutSeq L l := by unfold cutSeq; positivity [(Fact.out : 0 < L)]
  let A := ((coordinates (L := L) (regularity_pos r).le).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hn : ∀ v, ‖A v‖ = ‖v‖ := fun v => (coordinates (regularity_pos r).le).norm_map v
  obtain ⟨hd,hbound⟩ := hb l hl (A u) (by rwa [hn])
  have hcomp := hd.hasFDerivAt.comp u A.hasFDerivAt
  refine ⟨hcomp.differentiableAt,?_⟩
  change ‖fderiv ℝ (tail (L := L) hκ r h l ∘ A) u‖ ≤ _
  rw [hcomp.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hC])
  intro v
  calc ‖(fderiv ℝ (tail (L := L) hκ r h l) (A u)).comp A v‖ ≤
      ‖fderiv ℝ (tail (L := L) hκ r h l) (A u)‖*‖A v‖ :=
        by
          change ‖fderiv ℝ (tail (L := L) hκ r h l) (A u) (A v)‖ ≤ _
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C*(cutSeq L l)^(-(1/2 : ℝ)))*‖v‖ := by
      rw [hn]
      exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- The full real chain rule preserves the half-power rate uniformly on
any fixed compact class. There is no mass-tangent restriction. -/
theorem compact_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hκ : 0 < κ) (r : ℕ) {h : ℝ} (hh : 0 < h)
    (g : E → H02 L (regularity r)) (hg : ContDiff ℝ 1 g)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
      DifferentiableAt ℝ (fun x => T (L := L) hκ r h l (g x)) z ∧
      ‖fderiv ℝ (fun x => T (L := L) hκ r h l (g x)) z‖ ≤
        C*(cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
    (hg.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨C,hC,l0,hb⟩ := scalar_bound (L := L) hκ r B hh
  refine ⟨C*max M 0,mul_nonneg hC (le_max_right _ _),l0,?_⟩
  intro l hl z hz
  have ha : 0 ≤ cutSeq L l := by unfold cutSeq; positivity [(Fact.out : 0 < L)]
  obtain ⟨hd,hbound⟩ := hb l hl (g z) (hB z hz)
  have hcomp := hd.hasFDerivAt.comp z ((hg.differentiable (by norm_num)) z).hasFDerivAt
  refine ⟨hcomp.differentiableAt,?_⟩
  change ‖fderiv ℝ (T (L := L) hκ r h l ∘ g) z‖ ≤ _
  rw [hcomp.fderiv]
  calc ‖(fderiv ℝ (T (L := L) hκ r h l) (g z)).comp (fderiv ℝ g z)‖ ≤
      ‖fderiv ℝ (T (L := L) hκ r h l) (g z)‖*‖fderiv ℝ g z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C*(cutSeq L l)^(-(1/2 : ℝ)))*max M 0 :=
      mul_le_mul hbound ((hM z hz).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The actual pulled-back scalar contour differential is represented by
an h^(-s) vector of norm O(a^-1/2), uniformly before a is chosen. -/
theorem compact_dual_error (hκ : 0 < κ) (r : ℕ) {h : ℝ} (hh : 0 < h)
    (W : PosWeight) (g : WSeq W → H02 L (regularity r)) (hg : ContDiff ℝ 1 g)
    {K : Set (WSeq W)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
      ∃ e : WSeq (WindowInterpolationR44b.reciprocal W),
        ‖e‖ ≤ C*(cutSeq L l)^(-(1/2 : ℝ)) ∧ ∀ v : WSeq W,
          HasSum (fun j => (starRingEnd ℂ (e.val j)*v.val j).re)
            (fderiv ℝ (fun x => T (L := L) hκ r h l (g x)) z v) := by
  obtain ⟨C,hC,l0,hb⟩ := compact_pullback hκ r hh g hg hK
  refine ⟨C,hC,l0,?_⟩
  intro l hl z hz
  obtain ⟨e,he,hrep⟩ := WindowDualGradientR44b.dual_vector W
    (fderiv ℝ (fun x => T (L := L) hκ r h l (g x)) z)
  exact ⟨e,he.le.trans (hb l hl z hz).2,hrep⟩

end QuantumNLS.WindowScalarPullbackR44b

#print axioms QuantumNLS.WindowScalarPullbackR44b.scalar_bound
#print axioms QuantumNLS.WindowScalarPullbackR44b.compact_pullback
#print axioms QuantumNLS.WindowScalarPullbackR44b.compact_dual_error

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowScalarPullbackR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowScalarPullbackR44b." then
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
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
