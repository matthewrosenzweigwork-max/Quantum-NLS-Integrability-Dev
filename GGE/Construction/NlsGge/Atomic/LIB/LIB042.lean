import NlsGge.Atomic.LIB.LIB041
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# LIB-042: the genuine norm-valued Riesz contour integral

The actual LIB041 resolvent family is continuous in operator norm, and LIB040
proves each inverse compact. Its lift into the closed complex subspace of compact
operators is therefore Bochner-integrable along every C1 arc. Integrating there
and including into the ambient operator space gives exactly the literal contour
integral, with factor 1/(2πi); compactness follows from closed-subspace membership.

Finite arbitrary arc families and their oriented concatenations are retained.
`PiecewiseC1` records finite concatenations of C1 arcs with the normalized `Path.trans`
parameterization. The family theorem accepts every finite family directly, so
there is no circle or contour-shape restriction. The stronger compactness results
need no simplicity or orientation premise; actual closed-path specialization is
provided. No Cauchy identity, contour deformation, or idempotence is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology unitInterval

namespace NlsGge.Atomic.LIB042
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB040
open NlsGge.Atomic.LIB041

abbrev ResolventOp := SourcePairL2 →L[ℂ] SourcePairL2
abbrev CompactResolventOp := compactOperator (RingHom.id ℂ) SourcePairL2 SourcePairL2

local instance : NormedAddCommGroup CompactResolventOp := Submodule.normedAddCommGroup _
local instance : AddCommGroup CompactResolventOp := (Submodule.normedAddCommGroup _).toAddCommGroup
local instance : NormedSpace ℂ CompactResolventOp := Submodule.normedSpace _

lemma compactOperators_isClosed : IsClosed (CompactResolventOp : Set ResolventOp) :=
  isClosed_setOfPred_isCompactOperator

local instance : CompleteSpace CompactResolventOp := compactOperators_isClosed.completeSpace_coe

lemma zsResolventFamily_isCompact (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    IsCompactOperator (zsResolventFamily φ bc z) := by
  by_cases hz : HasBoundedResolvent (zsRealization φ bc) z
  · rw [zsResolventFamily_eq φ bc z hz]
    exact zs_resolvent_isCompact φ bc z hz
  · have he : zsResolventFamily φ bc z = 0 := by
      simp only [zsResolventFamily, resolventFamily, dite_eq_right hz]
    rw [he]
    exact isCompactOperator_zero

/-- The actual selected inverse, in the proved closed subspace of compact operators. -/
def compactResolventFamily (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    CompactResolventOp := ⟨zsResolventFamily φ bc z, zsResolventFamily_isCompact φ bc z⟩

@[simp] lemma compactResolventFamily_coe (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    (compactResolventFamily φ bc z : ResolventOp) = zsResolventFamily φ bc z := rfl

lemma compactResolventFamily_continuousOn (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ContinuousOn (compactResolventFamily φ bc)
      {z | HasBoundedResolvent (zsRealization φ bc) z} := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  exact zsResolventFamily_continuousOn φ bc

/-- The literal resolvent 1-form: applying it to v multiplies R(z) by v. -/
def resolventForm (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    ℂ →L[ℂ] ResolventOp := (1 : ℂ →L[ℂ] ℂ).smulRight (zsResolventFamily φ bc z)

def compactResolventForm (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    ℂ →L[ℂ] CompactResolventOp :=
  (1 : ℂ →L[ℂ] ℂ).smulRight (compactResolventFamily φ bc z)

@[simp] lemma resolventForm_apply (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z v : ℂ) :
    resolventForm φ bc z v = v • zsResolventFamily φ bc z := rfl

@[simp] lemma compactResolventForm_coe_apply
    (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z v : ℂ) :
    (compactResolventForm φ bc z v : ResolventOp) = resolventForm φ bc z v := rfl

lemma resolventForm_continuousOn (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ContinuousOn (resolventForm φ bc) {z | HasBoundedResolvent (zsRealization φ bc) z} :=
  ((ContinuousLinearMap.smulRightL ℂ ℂ ResolventOp) (1 : ℂ →L[ℂ] ℂ)).continuous.comp_continuousOn
    (zsResolventFamily_continuousOn φ bc)

lemma smulRight_id_continuousOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {s : Set ℂ} (hf : ContinuousOn f s) :
    ContinuousOn (fun z => (1 : ℂ →L[ℂ] ℂ).smulRight (f z)) s :=
  ((ContinuousLinearMap.smulRightL ℂ ℂ F) (1 : ℂ →L[ℂ] ℂ)).continuous.comp_continuousOn hf

lemma compactResolventForm_continuousOn (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ContinuousOn (compactResolventForm φ bc)
      {z | HasBoundedResolvent (zsRealization φ bc) z} :=
  smulRight_id_continuousOn (compactResolventFamily_continuousOn φ bc)

/-- Finite concatenations of genuine C1 arcs; no Cauchy or projection property is a field. -/
inductive PiecewiseC1 : {a b : ℂ} → Path a b → Prop
  | ofC1 {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : PiecewiseC1 γ
  | trans {a b c : ℂ} {γ : Path a b} {δ : Path b c} :
      PiecewiseC1 γ → PiecewiseC1 δ → PiecewiseC1 (γ.trans δ)

lemma PiecewiseC1.curveIntegrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {ω : ℂ → ℂ →L[ℂ] F} {s : Set ℂ} (hω : ContinuousOn ω s)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ) (himage : ∀ t, γ t ∈ s) :
    CurveIntegrable ω γ := by
  induction hγ with
  | ofC1 γ hc => exact hω.curveIntegrable_of_contDiffOn hc himage
  | @trans a b c γ δ hγ hδ ihγ ihδ =>
    have him : Set.range γ ∪ Set.range δ ⊆ s := by
      rw [← Path.trans_range]
      rintro _ ⟨t, rfl⟩
      exact himage t
    exact (ihγ (fun t => him (Or.inl (mem_range_self t)))).trans
      (ihδ (fun t => him (Or.inr (mem_range_self t))))

lemma resolvent_curveIntegrable (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    CurveIntegrable (resolventForm φ bc) γ :=
  hγ.curveIntegrable (resolventForm_continuousOn φ bc) hres

lemma compactResolvent_curveIntegrable (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    CurveIntegrable (compactResolventForm φ bc) γ :=
  hγ.curveIntegrable (compactResolventForm_continuousOn φ bc) hres

/-- Including the genuine compact-valued integral gives exactly the ambient contour integral. -/
lemma compact_curveIntegral_coe (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    ((curveIntegral (compactResolventForm φ bc) γ : CompactResolventOp) : ResolventOp) =
      curveIntegral (resolventForm φ bc) γ := by
  have hi := compactResolvent_curveIntegrable φ bc hγ hres
  rw [curveIntegral_def, curveIntegral_def]
  have h := CompactResolventOp.subtypeL.intervalIntegral_comp_comm hi
  change CompactResolventOp.subtypeL (∫ t in (0 : ℝ)..1, curveIntegralFun (compactResolventForm φ bc) γ t) = _
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t ht
  change CompactResolventOp.subtypeL (curveIntegralFun (compactResolventForm φ bc) γ t) =
    curveIntegralFun (resolventForm φ bc) γ t
  rw [curveIntegralFun_def, curveIntegralFun_def]
  rfl

/-- Exact positively oriented normalization; the path parameter fixes the orientation. -/
def rieszFactor : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

/-- Literal norm-valued resolvent contour integral on an arbitrary path. -/
def zsRieszProjection (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} (γ : Path a b) : ResolventOp :=
  rieszFactor • curveIntegral (resolventForm φ bc) γ

def compactRieszIntegral (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} (γ : Path a b) : CompactResolventOp :=
  rieszFactor • curveIntegral (compactResolventForm φ bc) γ

lemma compactRieszIntegral_coe (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    (compactRieszIntegral φ bc γ : ResolventOp) = zsRieszProjection φ bc γ := by
  change rieszFactor • ((curveIntegral (compactResolventForm φ bc) γ : CompactResolventOp) : ResolventOp) = _
  rw [compact_curveIntegral_coe φ bc hγ hres]
  rfl

/-- Stronger than the closed simple contour case: every finite piecewise C1 path works. -/
theorem zsRieszProjection_isCompact (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    IsCompactOperator (zsRieszProjection φ bc γ) := by
  rw [← compactRieszIntegral_coe φ bc hγ hres]
  exact (compactRieszIntegral φ bc γ).property


/-- Both convergence/integrability and the literal parameter-integral formula are explicit. -/
theorem zsRieszProjection_parameterIntegral (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b : ℂ} {γ : Path a b} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    IntervalIntegrable
      (fun t => derivWithin γ.extend (Icc 0 1) t • zsResolventFamily φ bc (γ.extend t))
      volume 0 1 ∧
    zsRieszProjection φ bc γ =
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        ∫ t in (0 : ℝ)..1, derivWithin γ.extend (Icc 0 1) t •
          zsResolventFamily φ bc (γ.extend t) := by
  have he : curveIntegralFun (resolventForm φ bc) γ =
      fun t => derivWithin γ.extend (Icc 0 1) t • zsResolventFamily φ bc (γ.extend t) := by
    funext t
    rw [curveIntegralFun_def, resolventForm_apply]
  have hi := resolvent_curveIntegrable φ bc hγ hres
  change IntervalIntegrable (curveIntegralFun (resolventForm φ bc) γ) volume 0 1 at hi
  rw [he] at hi
  refine ⟨hi, ?_⟩
  rw [zsRieszProjection, rieszFactor, curveIntegral_def, he]

/-- Literal compatibility with joining oriented arcs, hence with every finite concatenation. -/
theorem zsRieszProjection_trans (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a b c : ℂ} {γ : Path a b} {δ : Path b c}
    (hγ : PiecewiseC1 γ) (hδ : PiecewiseC1 δ)
    (hrγ : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t))
    (hrδ : ∀ t, HasBoundedResolvent (zsRealization φ bc) (δ t)) :
    zsRieszProjection φ bc (γ.trans δ) = zsRieszProjection φ bc γ + zsRieszProjection φ bc δ := by
  simp only [zsRieszProjection, curveIntegral_trans
    (resolvent_curveIntegrable φ bc hγ hrγ) (resolvent_curveIntegrable φ bc hδ hrδ), smul_add]

/-- Finite arc-family form: no restriction to circles or to a single smooth arc. -/
def zsRieszArcSum (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {ι : Type*} [Fintype ι] {a b : ι → ℂ} (γ : ∀ i, Path (a i) (b i)) : ResolventOp :=
  ∑ i, zsRieszProjection φ bc (γ i)

theorem zsRieszArcSum_eq (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {ι : Type*} [Fintype ι] {a b : ι → ℂ} (γ : ∀ i, Path (a i) (b i)) :
    zsRieszArcSum φ bc γ = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
      ∑ i, curveIntegral (resolventForm φ bc) (γ i) := by
  simp only [zsRieszArcSum, zsRieszProjection, rieszFactor, Finset.smul_sum]

/-- Compactness is stronger than contour simplicity or positive orientation: every such family works. -/
theorem zsRieszArcSum_isCompact (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {ι : Type*} [Fintype ι] {a b : ι → ℂ} (γ : ∀ i, Path (a i) (b i))
    (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend (Icc 0 1))
    (hres : ∀ i t, HasBoundedResolvent (zsRealization φ bc) (γ i t)) :
    IsCompactOperator (zsRieszArcSum φ bc γ) := by
  change (∑ i, zsRieszProjection φ bc (γ i)) ∈ CompactResolventOp
  exact CompactResolventOp.sum_mem fun i _ =>
    zsRieszProjection_isCompact φ bc (PiecewiseC1.ofC1 (γ i) (hγ i)) (hres i)

/-- Actual closed-path specialization; arbitrary simple positive piecewise contours are included. -/
theorem closed_piecewiseContour_isCompact (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {a : ℂ} {γ : Path a a} (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t)) :
    CurveIntegrable (resolventForm φ bc) γ ∧ IsCompactOperator (zsRieszProjection φ bc γ) :=
  ⟨resolvent_curveIntegrable φ bc hγ hres, zsRieszProjection_isCompact φ bc hγ hres⟩

/-- Full finite-contour contract: convergence is proved before compactness of the literal sum. -/
theorem finite_arc_contour_integrable_and_compact (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    {ι : Type*} [Fintype ι] {a b : ι → ℂ} (γ : ∀ i, Path (a i) (b i))
    (hγ : ∀ i, ContDiffOn ℝ 1 (γ i).extend (Icc 0 1))
    (hres : ∀ i t, HasBoundedResolvent (zsRealization φ bc) (γ i t)) :
    (∀ i, CurveIntegrable (resolventForm φ bc) (γ i)) ∧
      IsCompactOperator (zsRieszArcSum φ bc γ) :=
  ⟨fun i => resolvent_curveIntegrable φ bc (PiecewiseC1.ofC1 (γ i) (hγ i)) (hres i),
    zsRieszArcSum_isCompact φ bc γ hγ hres⟩

end NlsGge.Atomic.LIB042
