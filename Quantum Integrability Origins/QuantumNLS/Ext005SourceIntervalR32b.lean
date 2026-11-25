import QuantumNLS.Ext005SourceD3R114
import QuantumNLS.Ext005TimeFormR32b
import QuantumNLS.Ext005IntervalUniqueR32b

/-! Finite-interval uniqueness from source-form hypotheses on any [a,b].
Both signs of time and arbitrary initial time s are handled in one theorem.
The finite-form, positive self-adjoint B and strong-commutation conventions
are explicit; this module makes no existence claim. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005SourceIntervalR32b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005AlgebraicFormR114 Ext005ComplexRieszR113 Ext005SourceHypothesesR114
open Ext005ComplexForceR113 Ext005AntidualWeakR113 Ext005HilbertEnergyR112
open Ext005IntervalUniqueR32b Ext005HilbertUniqueR112
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Source assumptions localized to an arbitrary finite closed interval. -/
structure SourceOn (A : PositiveOperator H) (a b : ℝ) where
  B : NonnegativeOperator H
  domain : FormContained A (plusOne B)
  commute : StronglyCommute A.op B.op
  hamiltonian : ℝ → RawForm (FormDomain A)
  C : ℝ
  constant_pos : 0 < C
  symmetric : ∀ t ∈ Icc a b, Hermitian (hamiltonian t)
  upper : ∀ t ∈ Icc a b, ∀ u : FormDomain A,
    (hamiltonian t u u).re ≤ C * ‖u‖ ^ 2
  lower : ∀ t ∈ Icc a b, ∀ u : FormDomain A,
    C⁻¹ * ‖u‖ ^ 2 - C * comparisonEnergy A B domain u ≤ (hamiltonian t u u).re
  commutator : ∀ t ∈ Icc a b, ∀ u : FormDomain A,
    ∀ hu : inclusion A u ∈ B.op.domain, ∀ v : FormDomain A,
    inclusion A v = B.op ⟨inclusion A u, hu⟩ →
      (Complex.I * (hamiltonian t v u - hamiltonian t u v)).re ≤ C * ‖u‖ ^ 2
  diagonalDerivative : ℝ → FormDomain A → ℝ
  derivative : ∀ u t, t ∈ Icc a b →
    HasDerivWithinAt (fun s => (hamiltonian s u u).re)
      (diagonalDerivative t u) (Icc a b) t
  derivative_bound : ∀ u t, t ∈ Icc a b →
    |diagonalDerivative t u| ≤ C * ‖u‖ ^ 2

variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)

/-- A derived finite bound. The B contribution comes from the closed graph
theorem, not from the incorrect implication B <= A. -/
def finiteBound : ℝ := S.C * (1 + ‖comparison A (plusOne S.B) S.domain‖ ^ 2)

lemma finiteBound_nonneg : 0 ≤ finiteBound A a b S := by
  have hC := S.constant_pos.le
  dsimp [finiteBound]
  positivity

lemma source_diagonal_bound (t : ℝ) (ht : t ∈ Icc a b) (u : FormDomain A) :
    |(S.hamiltonian t u u).re| ≤ finiteBound A a b S * ‖u‖ ^ 2 := by
  have hC := S.constant_pos.le
  have hE : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have hN : 0 ≤ ‖comparison A (plusOne S.B) S.domain‖ ^ 2 := sq_nonneg _
  have hB := comparisonEnergy_bound A S.B S.domain u
  have hCB := mul_le_mul_of_nonneg_left hB hC
  have hi : 0 ≤ S.C⁻¹ * ‖u‖ ^ 2 := mul_nonneg (inv_nonneg.mpr hC) hE
  have hCN : 0 ≤ S.C * ‖comparison A (plusOne S.B) S.domain‖ ^ 2 * ‖u‖ ^ 2 := by positivity
  have hCE : 0 ≤ S.C * ‖u‖ ^ 2 := mul_nonneg hC hE
  dsimp [finiteBound]
  apply abs_le.mpr
  constructor <;> nlinarith [S.upper t ht u, S.lower t ht u]

/-- Continuous forms constructed from the source inequalities, with zero
extension outside the source interval. No b(t) is supplied as input. -/
def sourceForm (t : ℝ) : Form (FormDomain A) := by
  classical
  exact if ht : t ∈ Icc a b then
    continuousForm (S.hamiltonian t) (finiteBound A a b S) (finiteBound_nonneg A a b S)
      (S.symmetric t ht) (source_diagonal_bound A a b S t ht)
    else 0

lemma sourceForm_apply (t : ℝ) (ht : t ∈ Icc a b) (u v : FormDomain A) :
    sourceForm A a b S t u v = S.hamiltonian t u v := by
  simp only [sourceForm, dite_eq_left ht, continuousForm_apply]

lemma sourceForm_symmetric (t : ℝ) (ht : t ∈ Icc a b) (u v : FormDomain A) :
    starRingEnd ℂ (sourceForm A a b S t u v) = sourceForm A a b S t v u := by
  rw [sourceForm_apply A a b S t ht, sourceForm_apply A a b S t ht]
  exact S.symmetric t ht u v

lemma sourceForm_derivative (u : FormDomain A) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => (sourceForm A a b S s u u).re)
      (S.diagonalDerivative t u) (Icc a b) t := by
  apply (S.derivative u t ht).congr_of_mem _ ht
  intro s hs
  rw [sourceForm_apply A a b S s hs]

/-- The actual represented Hamiltonian is norm continuous, as a consequence
of the scalar time-derivative bound in the source assumptions. -/
lemma coefficient_continuous :
    ContinuousOn (fun t => formOperator (sourceForm A a b S t)) (Icc a b) := by
  apply (Ext005TimeFormR32b.time_lipschitz
    (fun t => formOperator (sourceForm A a b S t)) S.diagonalDerivative a b S.C
    S.constant_pos.le _ _ S.derivative_bound).continuousOn
  · intro t ht
    exact form_symmetric _ (sourceForm_symmetric A a b S t ht)
  · intro u t ht
    simpa only [form_pair] using sourceForm_derivative A a b S u t ht

lemma coefficient_bound (t : ℝ) (ht : t ∈ Icc a b) :
    ‖formOperator (sourceForm A a b S t)‖ ≤ finiteBound A a b S := by
  apply Ext005TimeFormR113.symmetric_norm_le _
    (form_symmetric _ (sourceForm_symmetric A a b S t ht))
    _ (finiteBound_nonneg A a b S)
  intro u
  have hsym := form_symmetric _ (sourceForm_symmetric A a b S t ht) u u
  simp only [ContinuousLinearMap.coe_coe] at hsym
  rw [hsym, form_pair, sourceForm_apply A a b S t ht]
  exact source_diagonal_bound A a b S t ht u

/-- Exactly the D3 class on a relevant finite interval: norm continuity,
essentially uniform Q(A) bound on that interval, and the source weak equation. -/
def D3On (x : ℝ → H) : Prop :=
  letI : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  ContinuousOn x (Icc a b) ∧ EnergyBounded i (Icc a b) x ∧
    ∀ (v : FormDomain A) (p : ℝ → ℝ), ContDiff ℝ ∞ p → HasCompactSupport p →
      tsupport p ⊆ Ioo a b →
      ∫ t, deriv p t * (⟪inclusion A v, x t⟫_ℂ).re =
        -(∫ t, p t * (S.hamiltonian t (lift i (x t)) v).im)

lemma D3On.weak (x : ℝ → H) (hx : D3On A a b S x) :
    letI : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
    let i := (inclusion A).restrictScalars ℝ
    Ext005IntervalChainR111.WeakDerivativeOn (Ioo a b)
      (fun t => i.adjoint (x t))
      (fun t => forceMap (formOperator (sourceForm A a b S t)) (lift i (x t))) := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  apply (schrodinger_weak_iff (Ioo a b) (inclusion A) (sourceForm A a b S) x
    (fun t => lift i (x t))).mp
  intro v p hp hc hs
  have he : (fun t => p t * (((-Complex.I) • sourceForm A a b S t (lift i (x t))) v).re) =
      (fun t => p t * (S.hamiltonian t (lift i (x t)) v).im) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · change p t * ((-Complex.I) * sourceForm A a b S t (lift i (x t)) v).re = _
      rw [sourceForm_apply A a b S t ht]
      simp [Complex.mul_re]
    · have hpt : p t = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        ht (Ioo_subset_Icc_self (hs h)))
      simp only [hpt, zero_mul]
  rw [he]
  simpa only [ambient_apply] using hx.2.2 v p hp hc hs

/-- EXT-005/D3 uniqueness on EVERY finite positive/negative interval,
including both endpoints, with data prescribed at any s in the interval.
No existence, norm identity or solution estimate is a premise. -/
theorem EXT005_D3_finite_interval_unique (s : ℝ) (hab : a < b) (hs : s ∈ Icc a b)
    (x y : ℝ → H) (hx : D3On A a b S x) (hy : D3On A a b S y)
    (hinit : x s = y s) : ∀ t ∈ Icc a b, x t = y t := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  let L := fun t => formOperator (sourceForm A a b S t)
  apply energy_unique_at_on i (inclusion_injective A) (inclusion_dense A) a b s hab hs
    x y (fun t => forceMap (L t)) hx.1 hy.1 hx.2.1 hy.2.1
    (force_measurable L _ ((coefficient_continuous A a b S).aestronglyMeasurable measurableSet_Icc))
  · exact ⟨finiteBound A a b S, finiteBound_nonneg A a b S,
      force_local_bound L (Icc a b) _ (Filter.Eventually.of_forall (coefficient_bound A a b S))⟩
  · exact Filter.Eventually.of_forall fun t ht u =>
      force_diagonal _ (form_symmetric _ (sourceForm_symmetric A a b S t ht)) u
  · exact D3On.weak A a b S x hx
  · exact D3On.weak A a b S y hy
  · exact hinit

/-- Norm conservation for any existing D3 solution, derived rather than
supplied as an additional requirement on competitors. -/
theorem EXT005_D3_norm_conserved (hab : a < b) (x : ℝ → H) (hx : D3On A a b S x) :
    ‖x b‖ ^ 2 = ‖x a‖ ^ 2 := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  let L := fun t => formOperator (sourceForm A a b S t)
  apply energy_norm_conserved_on i (inclusion_injective A) (inclusion_dense A) a b hab
    x (fun t => forceMap (L t)) hx.1 hx.2.1
    (force_measurable L _ ((coefficient_continuous A a b S).aestronglyMeasurable measurableSet_Icc))
  · exact ⟨finiteBound A a b S, finiteBound_nonneg A a b S,
      force_local_bound L (Icc a b) _ (Filter.Eventually.of_forall (coefficient_bound A a b S))⟩
  · exact Filter.Eventually.of_forall fun t ht u =>
      force_diagonal _ (form_symmetric _ (sourceForm_symmetric A a b S t ht)) u
  · exact D3On.weak A a b S x hx

end QuantumNLS.Ext005SourceIntervalR32b
#print axioms QuantumNLS.Ext005SourceIntervalR32b.EXT005_D3_finite_interval_unique
#print axioms QuantumNLS.Ext005SourceIntervalR32b.EXT005_D3_norm_conserved

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceIntervalR32b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceIntervalR32b." then
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
  Lean.logInfo m!"R32b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
