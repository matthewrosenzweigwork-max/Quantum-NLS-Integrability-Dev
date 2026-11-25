import QuantumNLS.Ext005ContractR39b
import QuantumNLS.Ext005TimeReversalR38b

/-! Conditional reversal of the forward source theorem. The reflected
coercivity and absolute commutator estimates are explicit input inequalities;
they are never inferred from the one-sided source bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005ReversalR39b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005TimeReversalR38b
open Ext005SourceBoundsR36b Ext005ForwardContractR37b Ext005ContractR39b
open Ext005HilbertEnergyR112
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)

/-- Precisely the additional source estimates used under time reversal.
The constant dominates the derived two-sided diagonal bound and original
scalar derivative bound. The last field is an ABSOLUTE commutator bound
with all B-domain premises. Reverse lower coercivity is separately explicit;
it is not a consequence of a one-sided commutator estimate. -/
structure ReversalBounds where
  K : ℝ
  positive : 0 < K
  diagonal_constant : finiteBound A a b S ≤ K
  derivative_constant : S.C ≤ K
  reflected_lower : ∀ t ∈ Icc a b, ∀ u : FormDomain A,
    K⁻¹ * ‖u‖ ^ 2 - K * Ext005FormEmbeddingR114.comparisonEnergy A S.B S.domain u ≤
      -(S.hamiltonian t u u).re
  absolute_commutator : ∀ t ∈ Icc a b, ∀ u : FormDomain A,
    ∀ hu : inclusion A u ∈ S.B.op.domain, ∀ v : FormDomain A,
    inclusion A v = S.B.op ⟨inclusion A u, hu⟩ →
      |(Complex.I * (S.hamiltonian t v u - S.hamiltonian t u v)).re| ≤ K * ‖u‖ ^ 2

/-- The reversed SourceOn is CONSTRUCTED from scalar/operator inequalities,
not supplied as an assumed existence or uniqueness conclusion. -/
def reflectedSource (R : ReversalBounds A a b S) : SourceOn A (-b) (-a) where
  B := S.B
  domain := S.domain
  commute := S.commute
  hamiltonian := reversedHamiltonian A a b S
  C := R.K
  constant_pos := R.positive
  symmetric := reversed_symmetric A a b S
  upper t ht u := by
    have h := reversed_diagonal_bound A a b S t ht u
    exact (le_abs_self _).trans (h.trans
      (mul_le_mul_of_nonneg_right R.diagonal_constant (sq_nonneg _)))
  lower t ht u := by
    exact R.reflected_lower (-t) (reflected_mem a b t ht) u
  commutator t ht u hu v hv := by
    rw [reversed_commutator]
    exact (abs_le.mp (R.absolute_commutator (-t) (reflected_mem a b t ht) u hu v hv)).1
      |> neg_le_of_neg_le
  diagonalDerivative t u := S.diagonalDerivative (-t) u
  derivative := reversed_derivative A a b S
  derivative_bound u t ht := (reversed_derivative_bound A a b S u t ht).trans
    (mul_le_mul_of_nonneg_right R.derivative_constant (sq_nonneg _))

/-- Pull the actual weak equation back through t ↦ -t. This lemma only
transforms the equation; it supplies no reversed source assumptions. -/
lemma weak_reflect (R : ReversalBounds A a b S) (x : ℝ → H)
    (hx : D3On A (-b) (-a) (reflectedSource A a b S R) x)
    (z : FormDomain A) (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hc : HasCompactSupport p) (hs : tsupport p ⊆ Ioo a b) :
    letI : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
    let i := (inclusion A).restrictScalars ℝ
    ∫ t, deriv p t * (⟪inclusion A z, x (-t)⟫_ℂ).re =
      -(∫ t, p t * (S.hamiltonian t (lift i (x (-t))) z).im) := by
  let q : ℝ → ℝ := fun t => p (-t)
  have hq : ContDiff ℝ ∞ q := hp.comp contDiff_neg
  have hcq : HasCompactSupport q := hc.comp_homeomorph (Homeomorph.neg ℝ)
  have hsq : tsupport q ⊆ Ioo (-b) (-a) := by
    intro t ht
    have ht' : -t ∈ tsupport p := tsupport_comp_subset_preimage p continuous_neg ht
    have h := hs ht'
    constructor <;> linarith [h.1, h.2]
  have hd (t : ℝ) : deriv q t = -deriv p (-t) := by
    simpa only [q, mul_neg_one, Function.comp_def, Pi.neg_apply, id_eq] using
      ((hp.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
        (hasDerivAt_id t).neg).deriv
  have he := hx.2.2 z q hq hcq hsq
  simp only [hd, reflectedSource, reversedHamiltonian_apply, Complex.neg_im,
    mul_neg, neg_mul, integral_neg] at he
  have hl := integral_neg_eq_self (fun t => deriv p t * (⟪inclusion A z, x (-t)⟫_ℂ).re) volume
  have hr := integral_neg_eq_self
    (fun t => p t * (S.hamiltonian t (lift ((inclusion A).restrictScalars ℝ) (x (-t))) z).im) volume
  simp only [neg_neg] at hl hr
  change -(∫ t, deriv p (-t) * (⟪inclusion A z, x t⟫_ℂ).re) =
    -(-(∫ t, p (-t) * (S.hamiltonian (-t)
      (lift ((inclusion A).restrictScalars ℝ) (x t)) z).im)) at he
  rw [hl, hr] at he
  linarith

/-- The constructed reflected path satisfies all three original D3
requirements. Its uniform form bound is a proved forward estimate. -/
lemma reflected_path_D3 (R : ReversalBounds A a b S)
    (v : ℝ → FormDomain A) (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ t ∈ Icc (-b) (-a), ‖v t‖ ≤ E)
    (hv : D3On A (-b) (-a) (reflectedSource A a b S R)
      (fun t => inclusion A (v t))) :
    D3On A a b S (fun t => inclusion A (v (-t))) := by
  have hm (t : ℝ) (ht : t ∈ Icc a b) : -t ∈ Icc (-b) (-a) := by
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨hv.1.comp continuous_neg.continuousOn hm, ?_, ?_⟩
  · refine ⟨E, hE, ?_⟩
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Filter.Eventually.of_forall fun t ht => ⟨v (-t), rfl, hb (-t) (hm t ht)⟩
  · exact weak_reflect A a b S R (fun t => inclusion A (v t)) hv

/-- REVERSAL corollary: if the explicitly displayed reflected source
inequalities hold, forward Theorem 8 applied to -H(-t) gives existence
with data at the RIGHT endpoint, plus uniqueness in D3 for the original
Hamiltonian. In particular [a,0] supplies negative times. -/
theorem EXT005_REVERSAL (R : ReversalBounds A a b S) (hab : a < b)
    (u₀ : FormDomain A) :
    ∃ v : ℝ → FormDomain A,
      v b = u₀ ∧
      (∀ t ∈ Icc a b, ‖v t‖ ≤
        forwardRadius A (-b) (-a) (reflectedSource A a b S R) u₀) ∧
      D3On A a b S (fun t => inclusion A (v t)) ∧
      ‖inclusion A (v a)‖ = ‖inclusion A u₀‖ ∧
      ∀ y : ℝ → H, D3On A a b S y → y b = inclusion A u₀ →
        ∀ t ∈ Icc a b, y t = inclusion A (v t) := by
  have hr : -b < -a := by linarith
  obtain ⟨w, hi, hb, hw, hn, _⟩ :=
    EXT005_contract A (-b) (-a) (reflectedSource A a b S R) hr u₀
  have hd := reflected_path_D3 A a b S R w _
    (forwardRadius_nonneg A (-b) (-a) (reflectedSource A a b S R) u₀) hb hw
  refine ⟨fun t => w (-t), hi, ?_, hd, hn, ?_⟩
  · intro t ht
    exact hb (-t) (by constructor <;> linarith [ht.1, ht.2])
  · intro y hy hyi
    apply EXT005_D3_finite_interval_unique A a b S b hab ⟨hab.le, le_rfl⟩
      y (fun t => inclusion A (w (-t))) hy hd
    rw [hi]
    exact hyi

end QuantumNLS.Ext005ReversalR39b
#print axioms QuantumNLS.Ext005ReversalR39b.EXT005_REVERSAL

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ReversalR39b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ReversalR39b." then
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
