import QuantumNLS.WindowInverseRestrictionR44b
import QuantumNLS.WindowScalarPullbackR44b
import QuantumNLS.WindowRateEstimateR44b
import QuantumNLS.WindowActionInvariantR44b

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9, estimates on the accepted actual chart. No hierarchy theorem
is assumed or restated here. The exact printed HierarchyInput is preserved
in the review record; the source proposition itself is not claimed before the
accepted predecessor and the remaining trajectory identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] InnerProductSpace.complexToReal
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.PhysicalTensor QuantumNLS.Reg015Setting
open QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowInverseRestrictionR44b
open QuantumNLS.Q07GradientRemovalR24 QuantumNLS.Q07SobolevModelR24
open QuantumNLS.Q07TailBindingR24
open QuantumNLS.PROP017UniformN QuantumNLS.WindowPhaseR44b QuantumNLS.WindowRateEstimateR44b
namespace QuantumNLS.WindowActualEstimatesR44b
variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed sequence order, fixed once for the largest charge. -/
def sequenceOrder (d : ℕ) : ℝ≥0 := ⟨4*(d : ℝ)+9,by positivity⟩

def chargeOrder (r : ℕ) : ℝ≥0 := ⟨regularity r,(regularity_pos r).le⟩

def highInverse (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (d : ℕ) :
    h02 L (sequenceOrder d : ℝ) → H02 L (sequenceOrder d : ℝ) :=
  Classical.choose (inverse_restriction hκ C (sequenceOrder d) (sequenceOrder d).2)

theorem highInverse_continuous (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (d : ℕ) :
    Continuous (highInverse hκ C d) :=
  (Classical.choose_spec (inverse_restriction hκ C (sequenceOrder d) (sequenceOrder d).2)).1

theorem highInverse_val (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (d : ℕ)
    (z : h02 L (sequenceOrder d : ℝ)) :
    (highInverse hκ C d z).val = C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z) :=
  (Classical.choose_spec (inverse_restriction hκ C (sequenceOrder d) (sequenceOrder d).2)).2 z

theorem orders {d r : ℕ} (hr : r ≤ d) :
    0 < chargeOrder r ∧ 2*(chargeOrder r : ℝ) < sequenceOrder d ∧ chargeOrder r ≤ sequenceOrder d := by
  have hpos : 0 < chargeOrder r := by exact_mod_cast regularity_pos r
  have hr' : (r : ℝ) ≤ d := by exact_mod_cast hr
  have hstrict : 2*(chargeOrder r : ℝ) < sequenceOrder d := by
    change 2*((2*r+4 : ℕ) : ℝ) < 4*(d : ℝ)+9
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  refine ⟨hpos,hstrict,?_⟩
  change regularity r ≤ 4*(d : ℝ)+9
  change 2*(regularity r) < 4*(d : ℝ)+9 at hstrict
  linarith [regularity_pos r]

def inverseForCharge (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) : h02 L (sequenceOrder d : ℝ) → H02 L (regularity r) :=
  fun x => (LossSobolev.fieldScale L).emb (sequenceOrder d) (chargeOrder r) (orders hr).2.2
    (highInverse hκ C d x)

theorem inverseForCharge_contDiff (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) : ContDiff ℝ 1 (inverseForCharge hκ C d r hr) := by
  unfold inverseForCharge
  exact inverse_loss hκ C (chargeOrder r) (sequenceOrder d) (orders hr).1 (orders hr).2.1
    (orders hr).2.2 (highInverse hκ C d) (highInverse_continuous hκ C d) (highInverse_val hκ C d)

/-- The physical scale inclusions preserve the literal L² class. -/
theorem field_emb_val (q S : ℝ≥0) (hqS : q ≤ S) (u : H02 L (S : ℝ)) :
    ((LossSobolev.fieldScale L).emb S q hqS u).val = u.val := by
  exact fieldIncl_val (def002 L (q : ℝ)) (def002 L (S : ℝ)) zero_le_one
    (def002_le_of_le L (by exact_mod_cast hqS)) u

theorem inverseForCharge_val (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) (z : h02 L (sequenceOrder d : ℝ)) :
    (inverseForCharge hκ C d r hr z).val = C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z) := by
  unfold inverseForCharge
  exact (field_emb_val (chargeOrder r) (sequenceOrder d) (orders hr).2.2
    (highInverse hκ C d z)).trans (highInverse_val hκ C d z)

/-- The actual scalar error in all real h^(4d+9) directions, uniformly on
any fixed compact subset, with no supplied gradient bound. -/
theorem actual_dual_error (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) {h : ℝ} (hh : 0 < h)
    {K : Set (h02 L (sequenceOrder d : ℝ))} (hK : IsCompact K) :
    ∃ g : h02 L (sequenceOrder d : ℝ) → H02 L (regularity r),
      ContDiff ℝ 1 g ∧
      (∀ z, (g z).val = C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z)) ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
        ∃ e : WSeq (reciprocal (def002 L (sequenceOrder d))),
          ‖e‖ ≤ A*(cutSeq L l)^(-(1/2 : ℝ)) ∧ ∀ v : h02 L (sequenceOrder d),
            HasSum (fun j => (starRingEnd ℂ (e.val j)*v.val j).re)
              (fderiv ℝ (fun x => T (L := L) hκ r h l (g x)) z v) := by
  refine ⟨inverseForCharge hκ C d r hr,inverseForCharge_contDiff hκ C d r hr,
    inverseForCharge_val hκ C d r hr,?_⟩
  exact WindowScalarPullbackR44b.compact_dual_error hκ r hh _
    (inverseForCharge hκ C d r hr) (inverseForCharge_contDiff hκ C d r hr) hK

/-- The actual physical inverse is C¹ on the ambient unweighted space. -/
theorem actual_inverse_contDiff (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    ContDiff ℝ 1 (fun z : WSeq unitWeight => C.Ψ (toL2 unitWeight z)) := by
  have hC : ContDiff ℝ 1 C.Ψ :=
    contDiffOn_univ.mp ((show AnalyticOnNhd ℝ C.Ψ univ from fun z _ => C.inverse_analytic z).contDiffOn uniqueDiffOn_univ)
  exact hC.comp ((toL2ᵢ unitWeight).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff

/-- The physical comparison estimate for the actual accepted inverse.
The modulus/phase and differential identifications are explicit comparison
hypotheses; this support result is not the named source proposition. -/
theorem actual_physical_comparison (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j)
    {K : Set (WSeq unitWeight)} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : WSeq W) (α β : ℤ → ℝ)
      (δ : WSeq (reciprocal W)),
      (∀ j, δ.val j = (((α j-β j : ℝ) : ℂ)*z.val j)) →
      ∀ {a A : ℝ}, 0 < a → 0 ≤ A → ‖δ‖ ≤ A*a^(-(1/2 : ℝ)) →
      lower W hW (rotate α z) ∈ K → lower W hW (rotate β z) ∈ K →
      ‖C.Ψ (toL2 unitWeight (lower W hW (rotate α z)))-
        C.Ψ (toL2 unitWeight (lower W hW (rotate β z)))‖ ≤
        (M*Real.sqrt (A*(2*‖z‖)))*a^(-(1/4 : ℝ)) :=
  physical_rate W hW hK _ (actual_inverse_contDiff hκ C)

/-- There is no hidden rescaling in the unweighted physical inverse:
unitWeight has sqrt(weight)=1 at every index. -/
theorem unit_base (s : ℝ) (hs : 0 ≤ s) (z : h02 L s)
    (hW : ∀ j, 1 ≤ (def002 L s).w j) :
    toL2 unitWeight (lower (def002 L s) hW z) = toBase s hs z := by
  apply lp.ext
  funext j
  rw [toL2_apply,toBase_apply]
  change (Real.sqrt (1 : ℝ) : ℂ)*z.val j = z.val j
  simp

end QuantumNLS.WindowActualEstimatesR44b

#print axioms QuantumNLS.WindowActualEstimatesR44b.actual_dual_error
#print axioms QuantumNLS.WindowActualEstimatesR44b.actual_physical_comparison

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowActualEstimatesR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowActualEstimatesR44b." then
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
