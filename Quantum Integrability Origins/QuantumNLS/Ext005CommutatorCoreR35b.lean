import QuantumNLS.Ext005ComparisonFormR35b

/-! Extension of the literal one-sided source commutator estimate through
an explicitly identified invariant operator core. The density/regularizer
bridge below is an additional algebraic hypothesis, not yet a consequence
of SourceOn's nonreal-resolvent convention. No energy bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005CommutatorCoreR35b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005GramResolventR112 Ext005ComplexGramR34b Ext005PositiveCutoffR35b
open Ext005ComparisonFormR35b Ext005RegularizedR33b Ext005ComplexForceR113
open Ext005ComplexRieszR113 Ext005SourceIntervalR32b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (B : NonnegativeOperator H)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- Vectors on which B acts within Q(A) and commutes with this actual cutoff.
Both operator-domain assertions are explicit. -/
def cutoffOperatorCore (e : ℝ) (he : 0 < e) : Set (FormDomain A) :=
  {u | ∃ (v : FormDomain A) (hu : inclusion A u ∈ B.op.domain)
      (hp : inclusion A (cutoff ((inclusion A).restrictScalars ℝ) e he u) ∈ B.op.domain),
    inclusion A v = B.op ⟨inclusion A u, hu⟩ ∧
      inclusion A (cutoff ((inclusion A).restrictScalars ℝ) e he v) =
        B.op ⟨inclusion A (cutoff ((inclusion A).restrictScalars ℝ) e he u), hp⟩}

variable (a b : ℝ) (S : SourceOn A a b)

/-- The true comparison derivative is bounded on the invariant operator
core directly by the source commutator, with all cutoff factors retained. -/
lemma source_commutator_on_core (e : ℝ) (he : 0 < e)
    (t : ℝ) (ht : t ∈ Icc a b) (u : FormDomain A)
    (hu : u ∈ cutoffOperatorCore A S.B e he) :
    let K := comparison A (plusOne S.B) S.domain
    let P := cutoff ((inclusion A).restrictScalars ℝ) e he
    let g := generator ((inclusion A).restrictScalars ℝ) e he
      (forceMap (formOperator (sourceForm A a b S t))) u
    2 * (⟪K u, K g⟫_ℂ).re ≤ S.C * ‖P u‖ ^ 2 := by
  rcases hu with ⟨v, hu, hp, hv, hpv⟩
  let i := inclusion A
  let P := cutoff (i.restrictScalars ℝ) e he
  let L := formOperator (sourceForm A a b S t)
  let g := generator (i.restrictScalars ℝ) e he (forceMap L) u
  let K := comparison A (plusOne S.B) S.domain
  change 2 * (⟪K u, K g⟫_ℂ).re ≤ S.C * ‖P u‖ ^ 2
  have hz : (⟪i u, i g⟫_ℂ).re = 0 := by
    change ⟪i.restrictScalars ℝ u, i.restrictScalars ℝ g⟫_ℝ = 0
    rw [generator_pair]
    exact force_diagonal L (form_symmetric _ (sourceForm_symmetric A a b S t ht)) (P u)
  have hpair := comparisonOperator_pair A S.B S.domain u g
  have hpairre := congrArg Complex.re hpair
  change (⟪comparisonOperator A S.B S.domain u, g⟫_ℂ).re =
    (⟪K u, K g⟫_ℂ).re - (⟪i u, i g⟫_ℂ).re at hpairre
  rw [hz, sub_zero] at hpairre
  have hgen : ⟪comparisonOperator A S.B S.domain u, g⟫_ℂ =
      (-Complex.I) * S.hamiltonian t (P u) (P v) := by
    change ⟪comparisonOperator A S.B S.domain u,
      inverseC i e he ((-Complex.I) • L (P u))⟫_ℂ = _
    rw [← inverseC_symm, comparisonOperator_action A S.B S.domain u v hu hv]
    rw [gramC_apply]
    change ⟪P v, (-Complex.I) • L (P u)⟫_ℂ = _
    rw [inner_smul_right, form_pair, sourceForm_apply A a b S t ht]
  have hbound := S.commutator t ht (P u) hp (P v) hpv
  have hsym := S.symmetric t ht (P u) (P v)
  have hnum : (Complex.I *
      (S.hamiltonian t (P v) (P u) - S.hamiltonian t (P u) (P v))).re =
      2 * ((-Complex.I) * S.hamiltonian t (P u) (P v)).re := by
    rw [← hsym]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im,
      Complex.conj_im, Complex.neg_re, Complex.neg_im, zero_mul, one_mul,
      neg_zero, neg_neg, neg_one_mul, zero_sub]
    ring
  rw [hnum] at hbound
  rw [← hpairre, hgen]
  exact hbound

/-- Density of that explicitly described core extends the literal source
bound to every Q(A) vector. The density assertion remains an open source
bridge; no commutator estimate is postulated at the endpoint. -/
theorem source_comparison_derivative_bound (e : ℝ) (he : 0 < e)
    (hd : Dense (cutoffOperatorCore A S.B e he))
    (t : ℝ) (ht : t ∈ Icc a b) (u : FormDomain A) :
    let K := comparison A (plusOne S.B) S.domain
    let P := cutoff ((inclusion A).restrictScalars ℝ) e he
    let g := generator ((inclusion A).restrictScalars ℝ) e he
      (forceMap (formOperator (sourceForm A a b S t))) u
    2 * (⟪K u, K g⟫_ℂ).re ≤ S.C * ‖P u‖ ^ 2 := by
  exact hd.induction
    (fun w hw => source_commutator_on_core A a b S e he t ht w hw)
    (isClosed_le (by fun_prop) (by fun_prop)) u

end QuantumNLS.Ext005CommutatorCoreR35b
#print axioms QuantumNLS.Ext005CommutatorCoreR35b.source_comparison_derivative_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005CommutatorCoreR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005CommutatorCoreR35b." then
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
  Lean.logInfo m!"R35b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
