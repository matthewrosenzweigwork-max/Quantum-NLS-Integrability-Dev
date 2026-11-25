import NlsGge.Atomic.LIB.LIB040
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.Bounded

/-! Common-domain resolvents, bounded H1 perturbations, and actual operator-norm
analytic dependence. All inverse statements use the convention z-A. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology Classical

namespace NlsGge.Atomic.LIB041
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB032 NlsGge.Atomic.LIB033
open NlsGge.Atomic.LIB035 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB040

/-- Actual selected full inverse, with explicit zero extension off the resolvent. -/
def resolventFamily (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  if hz : HasBoundedResolvent A z then hz.choose else 0

lemma resolventFamily_eq (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (hz : HasBoundedResolvent A z) : resolventFamily A z = hz.choose := by
  simp only [resolventFamily, dite_eq_left hz]

lemma resolventFamily_eq_of_inverse (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (T : SourcePairL2 →L[ℂ] SourcePairL2)
    (hr : ∀ f : SourcePairL2, ∃ hf : T f ∈ A.domain, z • T f - A ⟨T f, hf⟩ = f)
    (hl : ∀ u : A.domain, T (z • (u : SourcePairL2) - A u) = u) :
    resolventFamily A z = T := by
  let h : HasBoundedResolvent A z := ⟨T, hr, hl⟩
  rw [resolventFamily_eq A z h]
  exact boundedInverse_eq A z _ T h.choose_spec.2 hr

/-- The resolvent identity is proved on the same literal domain, including z=w. -/
lemma commonDomain_resolvent_identity (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z w : ℂ)
    (hz : HasBoundedResolvent A z) (hw : HasBoundedResolvent A w) :
    resolventFamily A z - resolventFamily A w =
      (w-z) • (resolventFamily A z).comp (resolventFamily A w) := by
  rw [resolventFamily_eq A z hz, resolventFamily_eq A w hw]
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨hf, hright⟩ := hw.choose_spec.1 f
  have hleft := hz.choose_spec.2 ⟨hw.choose f, hf⟩
  have hinput : z • hw.choose f - A ⟨hw.choose f, hf⟩ =
      f + (z-w) • hw.choose f := by
    calc
      _ = (w • hw.choose f - A ⟨hw.choose f, hf⟩) + (z-w) • hw.choose f := by module
      _ = _ := by rw [hright]
  rw [hinput, map_add, map_smul] at hleft
  change hz.choose f - hw.choose f = (w-z) • hz.choose (hw.choose f)
  calc
    _ = hz.choose f - (hz.choose f + (z-w) • hz.choose (hw.choose f)) :=
      congrArg (fun u => hz.choose f - u) hleft.symm
    _ = _ := by module

/-- The same actual source resolvent as LIB040, extended by zero outside its set. -/
def zsResolventFamily (φ : SourcePairL2) (bc : ZSBoundaryCondition) :=
  resolventFamily (zsRealization φ bc)

lemma zsResolventFamily_eq (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) :
    zsResolventFamily φ bc z = zsResolvent φ bc z hz :=
  resolventFamily_eq _ z hz

lemma zs_resolvent_identity (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z w : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z)
    (hw : HasBoundedResolvent (zsRealization φ bc) w) :
    zsResolvent φ bc z hz - zsResolvent φ bc w hw =
      (w-z) • (zsResolvent φ bc z hz).comp (zsResolvent φ bc w hw) := by
  have h := commonDomain_resolvent_identity (zsRealization φ bc) z w hz hw
  rw [resolventFamily_eq _ z hz, resolventFamily_eq _ w hw] at h
  exact h

/-- The domain's graph embedding is algebraic; its inherited L2 norm is not an H1 norm. -/
def domainH1Value {bc : ZSBoundaryCondition} (u : zsDomain bc) : IntervalPairH1 :=
  intervalPairOfLiteral (domainLift u)

@[simp] lemma domainH1Value_value {bc : ZSBoundaryCondition} (u : zsDomain bc) :
    intervalH1ToL2 (domainH1Value u) = u := by
  rw [domainH1Value, intervalPairOfLiteral_value, domainLift_value]

def domainToH1 (bc : ZSBoundaryCondition) : zsDomain bc →ₗ[ℂ] IntervalPairH1 where
  toFun := domainH1Value
  map_add' u v := by
    apply intervalH1ToL2_injective
    rw [intervalH1ToL2.map_add, domainH1Value_value, domainH1Value_value, domainH1Value_value]
    rfl
  map_smul' c u := by
    apply intervalH1ToL2_injective
    rw [intervalH1ToL2.map_smul, domainH1Value_value, domainH1Value_value]
    rfl

@[simp] lemma domainToH1_value {bc : ZSBoundaryCondition} (u : zsDomain bc) :
    intervalH1ToL2 (domainToH1 bc u) = u := domainH1Value_value u

/-- Arbitrary bounded H1 perturbation of the actual ZS action on EXACTLY the old domain. -/
def commonDomainOperator (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (Q : IntervalPairH1 →L[ℂ] SourcePairL2) : SourcePairL2 →ₗ.[ℂ] SourcePairL2 where
  domain := zsDomain bc
  toFun := (show zsDomain bc →ₗ[ℂ] SourcePairL2 from (zsRealization φ bc).toFun) +
    Q.toLinearMap.comp (domainToH1 bc)

@[simp] lemma commonDomainOperator_apply (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (Q : IntervalPairH1 →L[ℂ] SourcePairL2) (u : zsDomain bc) :
    commonDomainOperator φ bc Q u = zsRealization φ bc u + Q (domainToH1 bc u) := rfl

@[simp] lemma commonDomainOperator_zero (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    commonDomainOperator φ bc 0 = zsRealization φ bc := by
  apply LinearPMap.ext (f := commonDomainOperator φ bc 0) (g := zsRealization φ bc) rfl
  intro x hx hy
  change zsRealization φ bc ⟨x, hx⟩ + 0 = zsRealization φ bc ⟨x, hy⟩
  exact add_zero _

section Local
variable (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z0 : ℂ)
  (hz0 : HasBoundedResolvent (zsRealization φ bc) z0)

lemma zsResolventH1Lift_left (u : zsDomain bc) :
    zsResolventH1Lift φ bc z0 hz0 (z0 • (u : SourcePairL2) - zsRealization φ bc u) =
      domainToH1 bc u := by
  apply intervalH1ToL2_injective
  rw [zsResolventH1Lift_value, domainToH1_value, zsResolvent_left_inverse]

def localKernel (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  p.1.comp (zsResolventH1Lift φ bc z0 hz0) + (z0-p.2) • zsResolvent φ bc z0 hz0

def localInverse (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  Ring.inverse (1 - localKernel φ bc z0 hz0 p)

def localResolvent (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  (zsResolvent φ bc z0 hz0).comp (localInverse φ bc z0 hz0 p)

def localH1Resolvent (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) : SourcePairL2 →L[ℂ] IntervalPairH1 :=
  (zsResolventH1Lift φ bc z0 hz0).comp (localInverse φ bc z0 hz0 p)

lemma local_factorization (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) (u : zsDomain bc) :
    p.2 • (u : SourcePairL2) - commonDomainOperator φ bc p.1 u =
      (1 - localKernel φ bc z0 hz0 p) (z0 • (u : SourcePairL2) - zsRealization φ bc u) := by
  change _ = (z0 • (u : SourcePairL2) - zsRealization φ bc u) -
    (p.1 (zsResolventH1Lift φ bc z0 hz0 (z0 • (u : SourcePairL2) - zsRealization φ bc u)) +
      (z0-p.2) • zsResolvent φ bc z0 hz0 (z0 • (u : SourcePairL2) - zsRealization φ bc u))
  rw [zsResolventH1Lift_left, zsResolvent_left_inverse, commonDomainOperator_apply]
  module

lemma localInverse_hasSum (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    HasSum (fun n : ℕ => localKernel φ bc z0 hz0 p ^ n) (localInverse φ bc z0 hz0 p) :=
  hasSum_geom_series_inverse _ hsmall

lemma localInverse_right (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) (f : SourcePairL2) :
    (1-localKernel φ bc z0 hz0 p) (localInverse φ bc z0 hz0 p f) = f :=
  congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T f)
    (Ring.mul_inverse_cancel _ (IsUnit.one_sub_of_norm_lt_one hsmall))

lemma localInverse_left (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) (f : SourcePairL2) :
    localInverse φ bc z0 hz0 p ((1-localKernel φ bc z0 hz0 p) f) = f :=
  congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T f)
    (Ring.inverse_mul_cancel _ (IsUnit.one_sub_of_norm_lt_one hsmall))

lemma localResolvent_mem_domain (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) (f : SourcePairL2) :
    localResolvent φ bc z0 hz0 p f ∈ (commonDomainOperator φ bc p.1).domain :=
  zsResolvent_mem_domain φ bc z0 hz0 (localInverse φ bc z0 hz0 p f)

lemma localResolvent_right (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) (f : SourcePairL2) :
    p.2 • localResolvent φ bc z0 hz0 p f - commonDomainOperator φ bc p.1
      ⟨localResolvent φ bc z0 hz0 p f, localResolvent_mem_domain φ bc z0 hz0 p f⟩ = f := by
  calc
    _ = (1-localKernel φ bc z0 hz0 p)
        (z0 • localResolvent φ bc z0 hz0 p f - zsRealization φ bc
          ⟨localResolvent φ bc z0 hz0 p f, localResolvent_mem_domain φ bc z0 hz0 p f⟩) :=
      local_factorization φ bc z0 hz0 p _
    _ = (1-localKernel φ bc z0 hz0 p) (localInverse φ bc z0 hz0 p f) :=
      congrArg (fun u => (1-localKernel φ bc z0 hz0 p) u)
        (zsResolvent_right_apply φ bc z0 hz0 (localInverse φ bc z0 hz0 p f))
    _ = f := localInverse_right φ bc z0 hz0 p hsmall f

lemma localResolvent_left (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) (u : zsDomain bc) :
    localResolvent φ bc z0 hz0 p
      (p.2 • (u : SourcePairL2) - commonDomainOperator φ bc p.1 u) = u := by
  rw [local_factorization]
  change zsResolvent φ bc z0 hz0
    (localInverse φ bc z0 hz0 p ((1-localKernel φ bc z0 hz0 p)
      (z0 • (u : SourcePairL2) - zsRealization φ bc u))) = u
  rw [localInverse_left φ bc z0 hz0 p hsmall, zsResolvent_left_inverse]

lemma local_hasBoundedResolvent (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    HasBoundedResolvent (commonDomainOperator φ bc p.1) p.2 :=
  ⟨localResolvent φ bc z0 hz0 p,
    (fun f => ⟨localResolvent_mem_domain φ bc z0 hz0 p f,
      localResolvent_right φ bc z0 hz0 p hsmall f⟩),
    localResolvent_left φ bc z0 hz0 p hsmall⟩

end Local

def commonDomainResolvent (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (Q : IntervalPairH1 →L[ℂ] SourcePairL2) (z : ℂ) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  resolventFamily (commonDomainOperator φ bc Q) z

lemma commonDomainResolvent_eq_local (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z0 : ℂ)
    (hz0 : HasBoundedResolvent (zsRealization φ bc) z0)
    (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    commonDomainResolvent φ bc p.1 p.2 = localResolvent φ bc z0 hz0 p :=
  resolventFamily_eq_of_inverse _ _ _
    (fun f => ⟨localResolvent_mem_domain φ bc z0 hz0 p f,
      localResolvent_right φ bc z0 hz0 p hsmall f⟩)
    (localResolvent_left φ bc z0 hz0 p hsmall)

lemma localKernel_center (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z)
    (Q : IntervalPairH1 →L[ℂ] SourcePairL2) :
    localKernel φ bc z hz (Q,z) = Q.comp (zsResolventH1Lift φ bc z hz) := by
  change _ + (z-z) • zsResolvent φ bc z hz = _
  rw [sub_self]
  have hzero : (0 : ℂ) • zsResolvent φ bc z hz = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change (0 : ℂ) • (zsResolvent φ bc z hz f) = 0
    exact zero_smul ℂ _
  rw [hzero, add_zero]

lemma commonDomain_neumann (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z)
    (Q : IntervalPairH1 →L[ℂ] SourcePairL2)
    (hsmall : ‖Q.comp (zsResolventH1Lift φ bc z hz)‖ < 1) :
    HasBoundedResolvent (commonDomainOperator φ bc Q) z ∧
    commonDomainResolvent φ bc Q z =
      (zsResolvent φ bc z hz).comp (Ring.inverse (1-Q.comp (zsResolventH1Lift φ bc z hz))) := by
  have hs : ‖localKernel φ bc z hz (Q,z)‖ < 1 := by simpa only [localKernel_center] using hsmall
  exact ⟨local_hasBoundedResolvent φ bc z hz (Q,z) hs,
    by simpa only [localResolvent, localInverse, localKernel_center] using
      commonDomainResolvent_eq_local φ bc z hz (Q,z) hs⟩

section Analytic
variable (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z0 : ℂ)
  (hz0 : HasBoundedResolvent (zsRealization φ bc) z0)

lemma localKernel_analyticAt (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) :
    AnalyticAt ℂ (localKernel φ bc z0 hz0) p := by
  have hQ : AnalyticAt ℂ
      (fun q : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ =>
        q.1.comp (zsResolventH1Lift φ bc z0 hz0)) p :=
    (((ContinuousLinearMap.compL ℂ SourcePairL2 IntervalPairH1 SourcePairL2).flip
      (zsResolventH1Lift φ bc z0 hz0)).analyticAt _).comp analyticAt_fst
  exact hQ.add ((analyticAt_const.sub analyticAt_snd).smul analyticAt_const)

lemma localKernel_continuous : Continuous (localKernel φ bc z0 hz0) :=
  continuous_iff_continuousAt.mpr (fun p => (localKernel_analyticAt φ bc z0 hz0 p).continuousAt)

lemma localInverse_analyticAt (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    AnalyticAt ℂ (localInverse φ bc z0 hz0) p := by
  have hi : AnalyticAt ℂ Ring.inverse (1-localKernel φ bc z0 hz0 p) :=
    analyticAt_inverse (𝕜 := ℂ) (Units.oneSub _ hsmall)
  exact AnalyticAt.comp
    (f := fun q => (1 : SourcePairL2 →L[ℂ] SourcePairL2)-localKernel φ bc z0 hz0 q)
    (g := Ring.inverse) (x := p) hi
    (analyticAt_const.sub (localKernel_analyticAt φ bc z0 hz0 p))

lemma localResolvent_analyticAt (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    AnalyticAt ℂ (localResolvent φ bc z0 hz0) p :=
  (((ContinuousLinearMap.compL ℂ SourcePairL2 SourcePairL2 SourcePairL2)
    (zsResolvent φ bc z0 hz0)).analyticAt _).comp
    (localInverse_analyticAt φ bc z0 hz0 p hsmall)

lemma localH1Resolvent_analyticAt (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    AnalyticAt ℂ (localH1Resolvent φ bc z0 hz0) p :=
  (((ContinuousLinearMap.compL ℂ SourcePairL2 SourcePairL2 IntervalPairH1)
    (zsResolventH1Lift φ bc z0 hz0)).analyticAt _).comp
    (localInverse_analyticAt φ bc z0 hz0 p hsmall)

lemma local_small_open : IsOpen {p | ‖localKernel φ bc z0 hz0 p‖ < 1} :=
  isOpen_lt (localKernel_continuous φ bc z0 hz0).norm continuous_const

lemma commonDomainResolvent_analyticAt_local
    (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 p‖ < 1) :
    AnalyticAt ℂ (fun q => commonDomainResolvent φ bc q.1 q.2) p := by
  apply (localResolvent_analyticAt φ bc z0 hz0 p hsmall).congr
  filter_upwards [(local_small_open φ bc z0 hz0).mem_nhds hsmall] with q hq
  exact (commonDomainResolvent_eq_local φ bc z0 hz0 q hq).symm

/-- Joint analyticity in arbitrary bounded H1 perturbations and spectral parameter, in operator norm. -/
theorem commonDomain_resolvent_analyticAt
    (Q0 : IntervalPairH1 →L[ℂ] SourcePairL2)
    (hsmall : ‖Q0.comp (zsResolventH1Lift φ bc z0 hz0)‖ < 1) :
    AnalyticAt ℂ
      (fun p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ =>
        commonDomainResolvent φ bc p.1 p.2) (Q0,z0) :=
  commonDomainResolvent_analyticAt_local φ bc z0 hz0 (Q0,z0)
    (by simpa only [localKernel_center] using hsmall)

end Analytic

lemma zsResolventFamily_analyticOnNhd (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    AnalyticOnNhd ℂ (zsResolventFamily φ bc)
      {z : ℂ | HasBoundedResolvent (zsRealization φ bc) z} := by
  intro z hz
  have h := commonDomain_resolvent_analyticAt φ bc z hz 0 (by simp)
  have ht := h.comp (analyticAt_const.prod analyticAt_id)
  change AnalyticAt ℂ (fun w => commonDomainResolvent φ bc 0 w) z at ht
  simpa only [commonDomainResolvent, commonDomainOperator_zero, zsResolventFamily] using ht

lemma zsResolventFamily_continuousOn (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ContinuousOn (zsResolventFamily φ bc)
      {z : ℂ | HasBoundedResolvent (zsRealization φ bc) z} :=
  (zsResolventFamily_analyticOnNhd φ bc).continuousOn

/-- Literal LIB040 resolvent on the actual resolvent subtype; no witness replacement is implicit. -/
theorem zsResolvent_continuous (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    Continuous (fun p : {z : ℂ // HasBoundedResolvent (zsRealization φ bc) z} =>
      zsResolvent φ bc p.val p.property) := by
  have h := (zsResolventFamily_continuousOn φ bc).comp_continuous
    (continuous_subtype_val : Continuous
      (fun p : {z : ℂ // HasBoundedResolvent (zsRealization φ bc) z} => p.val))
    (fun p => p.property)
  exact h.congr (fun p => zsResolventFamily_eq φ bc p.val p.property)

/-- The actual H1 resolvent family, explicitly zero off the same actual resolvent set. -/
def zsResolventH1Family (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    SourcePairL2 →L[ℂ] IntervalPairH1 :=
  if hz : HasBoundedResolvent (zsRealization φ bc) z then zsResolventH1Lift φ bc z hz else 0

lemma zsResolventH1Family_eq (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) :
    zsResolventH1Family φ bc z = zsResolventH1Lift φ bc z hz := by
  simp only [zsResolventH1Family, dite_eq_left hz]

lemma localH1Resolvent_value (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z0 : ℂ)
    (hz0 : HasBoundedResolvent (zsRealization φ bc) z0)
    (p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ) (f : SourcePairL2) :
    intervalH1ToL2 (localH1Resolvent φ bc z0 hz0 p f) = localResolvent φ bc z0 hz0 p f :=
  zsResolventH1Lift_value φ bc z0 hz0 _

lemma zsResolventH1Family_eq_local (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z0 : ℂ)
    (hz0 : HasBoundedResolvent (zsRealization φ bc) z0) (z : ℂ)
    (hsmall : ‖localKernel φ bc z0 hz0 (0,z)‖ < 1) :
    zsResolventH1Family φ bc z = localH1Resolvent φ bc z0 hz0 (0,z) := by
  have hz : HasBoundedResolvent (zsRealization φ bc) z := by
    simpa only [commonDomainOperator_zero] using local_hasBoundedResolvent φ bc z0 hz0 (0,z) hsmall
  apply ContinuousLinearMap.ext
  intro f
  apply intervalH1ToL2_injective
  rw [zsResolventH1Family_eq φ bc z hz, zsResolventH1Lift_value, localH1Resolvent_value]
  rw [← zsResolventFamily_eq φ bc z hz]
  have h := commonDomainResolvent_eq_local φ bc z0 hz0 (0,z) hsmall
  change resolventFamily (commonDomainOperator φ bc 0) z = _ at h
  rw [commonDomainOperator_zero] at h
  exact congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T f) h

lemma zsResolventH1Family_analyticOnNhd (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    AnalyticOnNhd ℂ (zsResolventH1Family φ bc)
      {z : ℂ | HasBoundedResolvent (zsRealization φ bc) z} := by
  intro z hz
  have hs : ‖localKernel φ bc z hz (0,z)‖ < 1 := by rw [localKernel_center]; simp
  have h := (localH1Resolvent_analyticAt φ bc z hz (0,z) hs).comp
    (analyticAt_const.prod analyticAt_id)
  apply h.congr
  have ho : IsOpen {w : ℂ | ‖localKernel φ bc z hz (0,w)‖ < 1} :=
    (local_small_open φ bc z hz).preimage (continuous_const.prodMk continuous_id)
  filter_upwards [ho.mem_nhds hs] with w hw
  exact (zsResolventH1Family_eq_local φ bc z hz w hw).symm

lemma zsResolventH1Family_continuousOn (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ContinuousOn (zsResolventH1Family φ bc)
      {z : ℂ | HasBoundedResolvent (zsRealization φ bc) z} :=
  (zsResolventH1Family_analyticOnNhd φ bc).continuousOn

/-- A genuine uniform open perturbation ball preserves the entire fixed compact contour. -/
theorem compact_contour_perturbation_radius (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (Γ : Set ℂ) (hΓ : IsCompact Γ)
    (hres : ∀ z ∈ Γ, HasBoundedResolvent (zsRealization φ bc) z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q : IntervalPairH1 →L[ℂ] SourcePairL2, ‖Q‖ < ε →
      ∀ z ∈ Γ, ‖Q.comp (zsResolventH1Family φ bc z)‖ < 1 ∧
        HasBoundedResolvent (commonDomainOperator φ bc Q) z ∧
        AnalyticAt ℂ
          (fun p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ =>
            commonDomainResolvent φ bc p.1 p.2) (Q,z) := by
  have hc := (zsResolventH1Family_continuousOn φ bc).mono hres
  obtain ⟨M,hM⟩ := hΓ.exists_bound_of_continuousOn (f := zsResolventH1Family φ bc) hc
  let B := |M| + 1
  have hB : 0 < B + 1 := by dsimp [B]; positivity
  refine ⟨1/(B+1), by positivity, ?_⟩
  intro Q hQ z hz
  have hb : ‖zsResolventH1Family φ bc z‖ ≤ B + 1 :=
    (hM z hz).trans (by dsimp [B]; linarith [le_abs_self M])
  have hs : ‖Q.comp (zsResolventH1Family φ bc z)‖ < 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt
      ((mul_le_mul_of_nonneg_left hb (norm_nonneg Q)).trans_lt ((lt_div_iff₀ hB).mp hQ))
  have hs' : ‖Q.comp (zsResolventH1Lift φ bc z (hres z hz))‖ < 1 := by
    simpa only [zsResolventH1Family_eq φ bc z (hres z hz)] using hs
  exact ⟨hs, (commonDomain_neumann φ bc z (hres z hz) Q hs').1,
    commonDomain_resolvent_analyticAt φ bc z (hres z hz) Q hs'⟩

lemma pairLiteral_add (f g : IntervalPairH1) :
    intervalPairLiteralEquiv.symm (f+g) =
      h1PairAdd (intervalPairLiteralEquiv.symm f) (intervalPairLiteralEquiv.symm g) := by
  apply h1PairValue_injective
  rw [h1PairValue_add, intervalPairToLiteral_value, intervalPairToLiteral_value,
    intervalPairToLiteral_value, intervalH1ToL2.map_add]

lemma pairLiteral_smul (c : ℂ) (f : IntervalPairH1) :
    intervalPairLiteralEquiv.symm (c • f) = h1PairSmul c (intervalPairLiteralEquiv.symm f) := by
  apply h1PairValue_injective
  rw [h1PairValue_smul, intervalPairToLiteral_value, intervalPairToLiteral_value,
    intervalH1ToL2.map_smul]

lemma pairRepresentative_norm_le_three (f : H1Pair) :
    ‖pairRepresentative f‖ ≤ 3 * ‖intervalPairOfLiteral f‖ := by
  have h := pair_sup_le_epsilon_deriv (by norm_num : (0 : ℝ) < 1) f
  simp only [one_mul, inv_one, one_add_one_eq_two] at h
  have hn : 0 ≤ h1Norm f := Real.sqrt_nonneg _
  have hv : ‖h1PairValue f‖ ≤ h1Norm f :=
    (sq_le_sq₀ (norm_nonneg _) hn).1 (by rw [h1Norm_sq]; nlinarith [sq_nonneg ‖pairDerivative f‖])
  have hd : ‖pairDerivative f‖ ≤ h1Norm f :=
    (sq_le_sq₀ (norm_nonneg _) hn).1 (by rw [h1Norm_sq]; nlinarith [sq_nonneg ‖h1PairValue f‖])
  rw [intervalPairOfLiteral_norm]
  linarith

/-- The actual potential is bounded on the genuine H1 graph, before making its CLM. -/
lemma potentialH1_bound (δ : SourcePairL2) (g : IntervalPairH1) :
    ‖potentialProduct δ (intervalPairLiteralEquiv.symm g)‖ ≤ (3 * ‖δ‖) * ‖g‖ := by
  have h := pairRepresentative_norm_le_three (intervalPairLiteralEquiv.symm g)
  rw [show intervalPairOfLiteral (intervalPairLiteralEquiv.symm g) = g from
    intervalPairLiteralEquiv.apply_symm_apply g] at h
  calc
    _ ≤ ‖δ‖ * ‖pairRepresentative (intervalPairLiteralEquiv.symm g)‖ := potentialProduct_norm_le δ _
    _ ≤ ‖δ‖ * (3 * ‖g‖) := mul_le_mul_of_nonneg_left h (norm_nonneg δ)
    _ = _ := by ring

def potentialOnH1 (δ : SourcePairL2) : IntervalPairH1 →L[ℂ] SourcePairL2 :=
  LinearMap.mkContinuous
    { toFun := fun g => potentialProduct δ (intervalPairLiteralEquiv.symm g)
      map_add' := by intro f g; rw [pairLiteral_add, potentialProduct_add]
      map_smul' := by intro c g; rw [pairLiteral_smul, potentialProduct_smul]; rfl }
    (3 * ‖δ‖) (potentialH1_bound δ)

lemma potentialOnH1_norm_le (δ : SourcePairL2) : ‖potentialOnH1 δ‖ ≤ 3 * ‖δ‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

lemma potentialOnH1_ofLiteral (δ : SourcePairL2) (f : H1Pair) :
    potentialOnH1 δ (intervalPairOfLiteral f) = potentialProduct δ f := by
  change potentialProduct δ (intervalPairLiteralEquiv.symm (intervalPairLiteralEquiv f)) = _
  rw [intervalPairLiteralEquiv.symm_apply_apply]

lemma potentialProduct_potential_add (φ δ : SourcePairL2) (f : H1Pair) :
    potentialProduct (φ+δ) f = potentialProduct φ f + potentialProduct δ f := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [potentialProduct_ae (φ+δ) f b, potentialProduct_ae φ f b,
    potentialProduct_ae δ f b, Lp.coeFn_add (φ b) (δ b),
    Lp.coeFn_add (potentialProduct φ f b) (potentialProduct δ f b)] with x h0 hφ hδ hin hout
  change potentialProduct (φ+δ) f b x = (potentialProduct φ f b + potentialProduct δ f b) x
  rw [hout, h0]
  change (φ b + δ b) x * (f (!b)).value x =
    potentialProduct φ f b x + potentialProduct δ f b x
  rw [hφ, hδ, hin]
  change (φ b x + δ b x) * (f (!b)).value x =
    φ b x * (f (!b)).value x + δ b x * (f (!b)).value x
  ring

lemma potentialProduct_potential_smul (c : ℂ) (δ : SourcePairL2) (f : H1Pair) :
    potentialProduct (c • δ) f = c • potentialProduct δ f := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [potentialProduct_ae (c • δ) f b, potentialProduct_ae δ f b,
    Lp.coeFn_smul c (δ b), Lp.coeFn_smul c (potentialProduct δ f b)] with x h0 hδ hin hout
  change potentialProduct (c • δ) f b x = (c • potentialProduct δ f b) x
  rw [hout]
  change potentialProduct (c • δ) f b x = c * potentialProduct δ f b x
  rw [h0, hδ]
  change (c • δ b) x * (f (!b)).value x = _
  rw [hin]
  change (c * δ b x) * (f (!b)).value x = c * (δ b x * (f (!b)).value x)
  ring

lemma potentialOnH1_add (φ δ : SourcePairL2) :
    potentialOnH1 (φ+δ) = potentialOnH1 φ + potentialOnH1 δ := by
  apply ContinuousLinearMap.ext
  intro f
  exact potentialProduct_potential_add φ δ _

lemma potentialOnH1_smul (c : ℂ) (δ : SourcePairL2) :
    potentialOnH1 (c • δ) = c • potentialOnH1 δ := by
  apply ContinuousLinearMap.ext
  intro f
  exact potentialProduct_potential_smul c δ _

/-- Concrete complex-linear L2-potential multiplier, with a proved actual H1→L2 norm bound. -/
def potentialH1Operator : SourcePairL2 →L[ℂ] (IntervalPairH1 →L[ℂ] SourcePairL2) :=
  LinearMap.mkContinuous
    { toFun := potentialOnH1
      map_add' := potentialOnH1_add
      map_smul' := by intro c δ; exact potentialOnH1_smul c δ }
    3 (fun δ => by change ‖potentialOnH1 δ‖ ≤ 3 * ‖δ‖; exact potentialOnH1_norm_le δ)

lemma zsApply_potential_add (φ δ : SourcePairL2) (f : H1Pair) :
    zsApply (φ+δ) f = zsApply φ f + potentialProduct δ f := by
  rw [zsApply_eq_phase_add_potential (φ+δ) f, potentialProduct_potential_add,
    zsApply_eq_phase_add_potential φ f]
  abel

/-- Literal equality of the perturbed common-domain operator with the actual source potential family. -/
lemma commonDomainOperator_potential (φ δ : SourcePairL2) (bc : ZSBoundaryCondition) :
    commonDomainOperator φ bc (potentialOnH1 δ) = zsRealization (φ+δ) bc := by
  apply LinearPMap.ext (f := commonDomainOperator φ bc (potentialOnH1 δ))
    (g := zsRealization (φ+δ) bc) rfl
  intro x hx hy
  change zsApply φ (domainLift ⟨x,hx⟩) +
    potentialOnH1 δ (intervalPairOfLiteral (domainLift ⟨x,hx⟩)) =
      zsApply (φ+δ) (domainLift ⟨x,hy⟩)
  rw [potentialOnH1_ofLiteral, zsApply_potential_add]

/-- Perturbed resolvent existence is constructed, rather than assumed in the formula. -/
theorem zs_resolvent_neumann (φ δ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z)
    (hsmall : ‖(potentialOnH1 δ).comp (zsResolventH1Lift φ bc z hz)‖ < 1) :
    ∃ hz' : HasBoundedResolvent (zsRealization (φ+δ) bc) z,
      zsResolvent (φ+δ) bc z hz' =
        (zsResolvent φ bc z hz).comp
          (Ring.inverse (1-(potentialOnH1 δ).comp (zsResolventH1Lift φ bc z hz))) := by
  obtain ⟨hres,heq⟩ := commonDomain_neumann φ bc z hz (potentialOnH1 δ) hsmall
  have hp : HasBoundedResolvent (zsRealization (φ+δ) bc) z := by
    simpa only [commonDomainOperator_potential] using hres
  refine ⟨hp, ?_⟩
  have he : commonDomainResolvent φ bc (potentialOnH1 δ) z = zsResolventFamily (φ+δ) bc z := by
    simp only [commonDomainResolvent, commonDomainOperator_potential, zsResolventFamily]
  rw [he, zsResolventFamily_eq (φ+δ) bc z hp] at heq
  exact heq

lemma potentialH1Operator_coe :
    (potentialH1Operator : SourcePairL2 → (IntervalPairH1 →L[ℂ] SourcePairL2)) = potentialOnH1 := rfl

lemma potentialOnH1_analyticAt (δ : SourcePairL2) : AnalyticAt ℂ potentialOnH1 δ := by
  refine ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := SourcePairL2)
    (F := IntervalPairH1 →L[ℂ] SourcePairL2)
    { toFun := potentialOnH1
      map_add' := potentialOnH1_add
      map_smul' := by intro c x; exact potentialOnH1_smul c x
      cont := ?_ } δ
  have hL : LipschitzWith 3 potentialOnH1 := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hs := potentialH1Operator.map_sub x y
    change potentialOnH1 (x-y) = potentialOnH1 x-potentialOnH1 y at hs
    rw [← hs]
    exact potentialOnH1_norm_le (x-y)
  exact hL.continuous

lemma commonDomainResolvent_potential (φ δ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ) :
    commonDomainResolvent φ bc (potentialOnH1 δ) z = zsResolventFamily (φ+δ) bc z := by
  simp only [commonDomainResolvent, commonDomainOperator_potential, zsResolventFamily]

/-- Joint complex analyticity of the SAME actual source potential family in operator norm. -/
theorem zs_potential_resolvent_analyticAt (φ δ0 : SourcePairL2) (bc : ZSBoundaryCondition) (z0 : ℂ)
    (hz0 : HasBoundedResolvent (zsRealization φ bc) z0)
    (hsmall : ‖(potentialOnH1 δ0).comp (zsResolventH1Lift φ bc z0 hz0)‖ < 1) :
    AnalyticAt ℂ (fun p : SourcePairL2 × ℂ => zsResolventFamily (φ+p.1) bc p.2) (δ0,z0) := by
  have h := commonDomain_resolvent_analyticAt φ bc z0 hz0 (potentialOnH1 δ0) hsmall
  have hp : AnalyticAt ℂ
      (fun p : SourcePairL2 × ℂ => (potentialOnH1 p.1,p.2)) (δ0,z0) :=
    (AnalyticAt.comp (g := potentialOnH1) (f := fun p : SourcePairL2 × ℂ => p.1)
      (x := (δ0,z0)) (potentialOnH1_analyticAt δ0) analyticAt_fst).prod
        (analyticAt_snd : AnalyticAt ℂ (fun p : SourcePairL2 × ℂ => p.2) (δ0,z0))
  have ht := AnalyticAt.comp
    (f := fun p : SourcePairL2 × ℂ => (potentialOnH1 p.1,p.2))
    (g := fun p : (IntervalPairH1 →L[ℂ] SourcePairL2) × ℂ => commonDomainResolvent φ bc p.1 p.2)
    h hp
  have he : (fun p : SourcePairL2 × ℂ => commonDomainResolvent φ bc (potentialOnH1 p.1) p.2) =
      (fun p => zsResolventFamily (φ+p.1) bc p.2) :=
    funext (fun p => commonDomainResolvent_potential φ p.1 bc p.2)
  change AnalyticAt ℂ (fun p : SourcePairL2 × ℂ =>
    commonDomainResolvent φ bc (potentialOnH1 p.1) p.2) (δ0,z0) at ht
  rw [he] at ht
  exact ht

/-- A single genuine L2 potential neighborhood preserves the whole fixed compact contour. -/
theorem compact_contour_potential_radius (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (Γ : Set ℂ) (hΓ : IsCompact Γ)
    (hres : ∀ z ∈ Γ, HasBoundedResolvent (zsRealization φ bc) z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : SourcePairL2, ‖δ‖ < ε → ∀ z ∈ Γ,
      HasBoundedResolvent (zsRealization (φ+δ) bc) z ∧
      AnalyticAt ℂ (fun p : SourcePairL2 × ℂ => zsResolventFamily (φ+p.1) bc p.2) (δ,z) := by
  obtain ⟨ε,hε,hall⟩ := compact_contour_perturbation_radius φ bc Γ hΓ hres
  refine ⟨ε/3, by positivity, ?_⟩
  intro δ hδ z hz
  have hq : ‖potentialOnH1 δ‖ < ε :=
    (potentialOnH1_norm_le δ).trans_lt (by linarith)
  obtain ⟨hs,hp,_⟩ := hall (potentialOnH1 δ) hq z hz
  have hs' : ‖(potentialOnH1 δ).comp (zsResolventH1Lift φ bc z (hres z hz))‖ < 1 := by
    simpa only [zsResolventH1Family_eq φ bc z (hres z hz)] using hs
  exact ⟨by simpa only [commonDomainOperator_potential] using hp,
    zs_potential_resolvent_analyticAt φ δ bc z (hres z hz) hs'⟩

end NlsGge.Atomic.LIB041
