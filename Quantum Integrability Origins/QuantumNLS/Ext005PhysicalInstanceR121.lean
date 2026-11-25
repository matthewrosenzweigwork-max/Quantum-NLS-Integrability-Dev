import QuantumNLS.Ext005PhysicalSourceR121

/-! A fixed-j physical EXT-005 instance on every finite nondegenerate
interval, with arbitrary data time and genuine moment-domain data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap Set Filter MeasureTheory
namespace QuantumNLS.Ext005PhysicalInstanceR121
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005MomentDomainR33b Ext005OperatorFormR113 Ext005PhysicalSourceR121
open Ext005SourceIntervalR32b Ext005ContractR39b Ext005ReversalR39b
open Ext005FiniteContractR39b Ext005PatchingR32b Ext005SourceBoundsR36b
open Prop022FactorialCoefficientsR115
variable {L : ℝ} [Fact (0 < L)]

lemma norm_at {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : PositiveOperator H) (l r : ℝ) (S : SourceOn A l r)
    (x : ℝ → H) (hx : D3On A l r S x) (t : ℝ) (ht : t ∈ Icc l r) :
    ‖x t‖ = ‖x l‖ := by
  rcases eq_or_lt_of_le ht.1 with he | hlt
  · rw [← he]
  · have h := EXT005_D3_norm_conserved A l t
      (restrictSource A l r S l t le_rfl ht.2) hlt x
      (D3On_restrict A l r S l t le_rfl ht.2 x hx)
    nlinarith [norm_nonneg (x t), norm_nonneg (x l)]

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))

/-- The physical left-data application, with all source premises discharged. -/
theorem physical_forward (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l < r)
    (v₀ : FormDomain (momentPositive (L := L) j)) :
    ∃ v : ℝ → FormDomain (momentPositive (L := L) j),
      v l = v₀ ∧ (∀ t ∈ Icc l r, ‖v t‖ ≤ forwardRadius (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) v₀) ∧
      D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (fun t => Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ∧
      ‖Ext005OperatorFormR113.inclusion (momentPositive j) (v r)‖ = ‖Ext005OperatorFormR113.inclusion (momentPositive j) v₀‖ ∧
      ∀ y : ℝ → Fock L, D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) y →
        y l = Ext005OperatorFormR113.inclusion (momentPositive j) v₀ →
        ∀ t ∈ Icc l r, y t = Ext005OperatorFormR113.inclusion (momentPositive j) (v t) :=
  EXT005_contract _ l r (physicalSource B M A hM hA hB hs u₀ j hj l r) hlr v₀

/-- Right-data existence is obtained from the proved reversed physical bounds. -/
theorem physical_reverse (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l < r)
    (v₀ : FormDomain (momentPositive (L := L) j)) :
    ∃ v : ℝ → FormDomain (momentPositive (L := L) j), v r = v₀ ∧
      D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (fun t => Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) := by
  obtain ⟨v, hi, _, hv, _, _⟩ := EXT005_REVERSAL _ l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (physicalReversal B M A hM hA hB hs u₀ j hj l r) hlr v₀
  exact ⟨v, hi, hv⟩

/-- ONE physical instance: every fixed integer j>=1, every finite interval,
any initial time, and actual square-root-domain data. The energy bound,
root action, norm conservation and D3 uniqueness are all conclusions.
The SourceOn and reversal records are constructed from the physical coefficients. -/
theorem physical_nondegenerate_R121 (j : ℕ) (hj : 1 ≤ j)
    (l r : ℝ) (hlr : l < r) (s : ℝ) (hs₀ : s ∈ Icc l r)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    ∃ v : ℝ → FormDomain (momentPositive (L := L) j),
      Ext005OperatorFormR113.inclusion (momentPositive j) (v s) = x ∧
      (∀ t ∈ Icc l r, Ext005OperatorFormR113.inclusion (momentPositive j) (v t) ∈ momentDomain (L := L) j) ∧
      (∀ t, momentRoot j ⟨Ext005OperatorFormR113.inclusion (momentPositive j) (v t), inclusion_mem_root j (v t)⟩ = completedRoot j (v t)) ∧
      (∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Icc l r,
        energy j (Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ≤ E) ∧
      D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (fun t => Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ∧
      (∀ t ∈ Icc l r, ‖Ext005OperatorFormR113.inclusion (momentPositive j) (v t)‖ = ‖x‖) ∧
      ∀ y : ℝ → Fock L, D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) y → y s = x →
        ∀ t ∈ Icc l r, y t = Ext005OperatorFormR113.inclusion (momentPositive j) (v t) := by
  obtain ⟨v₀, hv₀⟩ := (moment_form_domain_iff j x).mpr hx
  obtain ⟨v, hi, ⟨E, hE, hb⟩, hv, hu⟩ :=
    EXT005_finite_interval _ l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (physicalReversal B M A hM hA hB hs u₀ j hj l r) hlr s hs₀ v₀
  have hinitial : Ext005OperatorFormR113.inclusion (momentPositive j) (v s) = x := by rw [hi, hv₀]
  refine ⟨v, hinitial, ?_, ?_, ⟨E^2, sq_nonneg E, ?_⟩, hv, ?_, ?_⟩
  · intro t _
    exact (moment_form_domain_iff j _).mp ⟨v t, rfl⟩
  · intro t
    exact completedRoot_eq j (v t)
  · intro t ht
    have hn := moment_form_norm_sq j (v t)
    change ‖v t‖ ^ 2 = energy j (Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) at hn
    rw [← hn]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb t ht) 2
  · intro t ht
    have ht' := norm_at _ l r (physicalSource B M A hM hA hB hs u₀ j hj l r) _ hv t ht
    have hs' := norm_at _ l r (physicalSource B M A hM hA hB hs u₀ j hj l r) _ hv s hs₀
    rw [hinitial] at hs'
    exact ht'.trans hs'.symm
  · intro y hy hys
    exact hu y hy (hys.trans hv₀.symm)

/-- The physical instance also covers a singleton closed interval. -/
theorem EXT005_physical_instance_R121 (j : ℕ) (hj : 1 ≤ j)
    (l r : ℝ) (hlr : l ≤ r) (s : ℝ) (hs₀ : s ∈ Icc l r)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    ∃ v : ℝ → FormDomain (momentPositive (L := L) j),
      Ext005OperatorFormR113.inclusion (momentPositive j) (v s) = x ∧
      (∀ t ∈ Icc l r, Ext005OperatorFormR113.inclusion (momentPositive j) (v t) ∈ momentDomain (L := L) j) ∧
      (∀ t, momentRoot j ⟨Ext005OperatorFormR113.inclusion (momentPositive j) (v t), inclusion_mem_root j (v t)⟩ = completedRoot j (v t)) ∧
      (∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Icc l r,
        energy j (Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ≤ E) ∧
      D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (fun t => Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ∧
      (∀ t ∈ Icc l r, ‖Ext005OperatorFormR113.inclusion (momentPositive j) (v t)‖ = ‖x‖) ∧
      ∀ y : ℝ → Fock L, D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) y → y s = x →
        ∀ t ∈ Icc l r, y t = Ext005OperatorFormR113.inclusion (momentPositive j) (v t) := by
  rcases eq_or_lt_of_le hlr with he | hlt
  · subst r
    have hsl : s = l := le_antisymm hs₀.2 hs₀.1
    subst s
    obtain ⟨v₀, hv₀⟩ := (moment_form_domain_iff j x).mpr hx
    refine ⟨fun _ => v₀, hv₀, ?_, ?_, ⟨energy j x, energy_nonneg j x, ?_⟩, ?_, ?_, ?_⟩
    · intro _ _
      rw [hv₀]
      exact hx
    · intro _
      exact completedRoot_eq j v₀
    · intro _ _
      rw [hv₀]
    · refine ⟨continuous_const.continuousOn, ?_, ?_⟩
      · refine ⟨‖v₀‖, norm_nonneg _, ?_⟩
        exact ae_restrict_of_forall_mem measurableSet_Icc (fun _ _ => ⟨v₀, rfl, le_rfl⟩)
      · intro w p hp hc hsup
        have hp0 : p = fun _ => 0 := by
          funext t
          apply image_eq_zero_of_notMem_tsupport
          intro ht
          have h := hsup ht
          exact (lt_irrefl l) (h.1.trans h.2)
        simp only [hp0, deriv_const, zero_mul, integral_zero, neg_zero]
    · intro _ _
      rw [hv₀]
    · intro y hy hi t ht
      have htl : t = l := le_antisymm ht.2 ht.1
      simpa only [htl, hv₀] using hi
  · exact physical_nondegenerate_R121 B M A hM hA hB hs u₀ j hj l r hlt s hs₀ x hx

end QuantumNLS.Ext005PhysicalInstanceR121
#print axioms QuantumNLS.Ext005PhysicalInstanceR121.EXT005_physical_instance_R121
#print axioms QuantumNLS.Ext005PhysicalInstanceR121.physical_forward
#print axioms QuantumNLS.Ext005PhysicalInstanceR121.physical_reverse

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalInstanceR121." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalInstanceR121." then
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
