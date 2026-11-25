import QuantumNLS.Ext005ReversalR39b
import QuantumNLS.Ext005PatchingR32b

/-! Conditional finite-interval patching. A backward path reaches the left
endpoint, then the forward theorem constructs a path over the entire
interval. D3 uniqueness proves agreement on the overlap. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005FiniteContractR39b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005ReversalR39b
open Ext005ContractR39b Ext005PatchingR32b Ext005SourceBoundsR36b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction carries only the explicitly assumed reversal inequalities. -/
def restrictReversal (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
    (R : ReversalBounds A a b S) (c d : ℝ) (hac : a ≤ c) (hdb : d ≤ b) :
    ReversalBounds A c d (restrictSource A a b S c d hac hdb) where
  K := R.K
  positive := R.positive
  diagonal_constant := R.diagonal_constant
  derivative_constant := R.derivative_constant
  reflected_lower t ht := R.reflected_lower t ⟨hac.trans ht.1, ht.2.trans hdb⟩
  absolute_commutator t ht := R.absolute_commutator t ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- On EVERY finite nondegenerate interval, under the explicit reversible
source bounds, data may be prescribed at ANY s in the interval. Patching
uses actual forward/reversed solutions and uniqueness on their overlap.
Each competitor must satisfy D3 on this whole relevant interval. -/
theorem EXT005_finite_interval (A : PositiveOperator H) (a b : ℝ)
    (S : SourceOn A a b) (R : ReversalBounds A a b S)
    (hab : a < b) (s : ℝ) (hs : s ∈ Icc a b) (u₀ : FormDomain A) :
    ∃ v : ℝ → FormDomain A,
      v s = u₀ ∧ (∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Icc a b, ‖v t‖ ≤ E) ∧
      D3On A a b S (fun t => inclusion A (v t)) ∧
      ∀ y : ℝ → H, D3On A a b S y → y s = inclusion A u₀ →
        ∀ t ∈ Icc a b, y t = inclusion A (v t) := by
  rcases eq_or_lt_of_le hs.1 with he | has
  · subst s
    obtain ⟨v, hi, hb, hv, _, hu⟩ := EXT005_contract A a b S hab u₀
    exact ⟨v, hi, ⟨_, forwardRadius_nonneg A a b S u₀, hb⟩, hv, hu⟩
  · let S' := restrictSource A a b S a s le_rfl hs.2
    let R' := restrictReversal A a b S R a s le_rfl hs.2
    obtain ⟨w, hws, _, hw, _, _⟩ := EXT005_REVERSAL A a s S' R' has u₀
    obtain ⟨v, hva, hb, hv, _, _⟩ := EXT005_contract A a b S hab (w a)
    have hvs : v s = u₀ := by
      have h := EXT005_D3_finite_interval_unique A a s S' a has ⟨le_rfl, has.le⟩
        (fun t => inclusion A (v t)) (fun t => inclusion A (w t))
        (D3On_restrict A a b S a s le_rfl hs.2 _ hv) hw
        (congrArg (inclusion A) hva) s ⟨has.le, le_rfl⟩
      exact (inclusion_injective A h).trans hws
    refine ⟨v, hvs, ⟨_, forwardRadius_nonneg A a b S (w a), hb⟩, hv, ?_⟩
    intro y hy hyi
    apply EXT005_D3_finite_interval_unique A a b S s hab hs
      y (fun t => inclusion A (v t)) hy hv
    rw [hvs]
    exact hyi

/-- Local solutions on overlapping finite intervals with the same literal
Hamiltonian agree wherever both D3 hypotheses hold and they share a datum.
This is the compatibility step used for consecutive compact intervals. -/
theorem EXT005_overlap (A : PositiveOperator H) (a b c d e f : ℝ)
    (S : SourceOn A a b) (T : SourceOn A c d)
    (heq : S.hamiltonian = T.hamiltonian)
    (hae : a ≤ e) (hfb : f ≤ b) (hce : c ≤ e) (hfd : f ≤ d)
    (hef : e < f) (s : ℝ) (hs : s ∈ Icc e f) (x y : ℝ → H)
    (hx : D3On A a b S x) (hy : D3On A c d T y) (hi : x s = y s) :
    ∀ t ∈ Icc e f, x t = y t := by
  have hx' := D3On_restrict A a b S e f hae hfb x hx
  have hy' := D3On_restrict A c d T e f hce hfd y hy
  have hy'' : D3On A e f (restrictSource A a b S e f hae hfb) y := by
    refine ⟨hy'.1, hy'.2.1, ?_⟩
    intro z p hp hc hsupp
    simpa only [restrictSource, heq] using hy'.2.2 z p hp hc hsupp
  exact EXT005_D3_finite_interval_unique A e f _ s hef hs x y hx' hy'' hi

end QuantumNLS.Ext005FiniteContractR39b
#print axioms QuantumNLS.Ext005FiniteContractR39b.EXT005_finite_interval
#print axioms QuantumNLS.Ext005FiniteContractR39b.EXT005_overlap

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005FiniteContractR39b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005FiniteContractR39b." then
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
  Lean.logInfo m!"R39b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
