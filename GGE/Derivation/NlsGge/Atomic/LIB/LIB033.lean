import NlsGge.Atomic.LIB.LIB028
import NlsGge.Atomic.LIB.LIB029
import NlsGge.Atomic.LIB.LIB030
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Actual densely defined selfadjoint Zakharov--Shabat realizations

All carriers and endpoint relations are the literal accepted interval objects.
The operator is Mathlib's LinearPMap with its actual adjoint. Local H1
constructors do not install algebra instances on the shared weak graph.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Classical

namespace NlsGge.Atomic.LIB033
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

lemma representative_eq_of_value_eq {f g : H1} (h : f.value = g.value) :
    representative f = representative g := by
  apply representative_eq_of_ae
  simpa only [h] using representative_ae f

/-- The value class determines the derivative and the entire literal weak graph. -/
theorem h1_value_injective : Function.Injective (fun f : H1 => f.value) := by
  intro f g hv
  have hr := representative_eq_of_value_eq hv
  have hf := (representative_spec f).2
  have hg := (representative_spec g).2
  rw [hr] at hf
  have hd : f.derivative = g.derivative := by
    apply Lp.ext
    filter_upwards [ae_restrict_of_ae hf, ae_restrict_of_ae hg,
      ae_restrict_mem measurableSet_Ioc] with x hfx hgx hx
    have hm : x ∈ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one]
      exact ⟨hx.1.le, hx.2⟩
    exact (hfx hm).unique (hgx hm)
  cases f
  cases g
  cases hv
  cases hd
  rfl

theorem h1PairValue_injective : Function.Injective h1PairValue := by
  intro f g h
  funext b
  apply h1_value_injective
  exact congrArg (fun x : SourcePairL2 => x b) h

lemma l2_mul_continuous_intervalIntegrable (f : SourceIntervalL2)
    (a : ℝ → ℂ) (ha : Continuous a) :
    IntervalIntegrable (fun x => f x * a x) volume 0 1 :=
  (intervalIntegrable_L2 f).mul_continuousOn ha.continuousOn

lemma interval_test_pairing_add (f g : SourceIntervalL2)
    (a : ℝ → ℂ) (ha : Continuous a) :
    (∫ x in (0 : ℝ)..1, (f + g) x * a x) =
      (∫ x in (0 : ℝ)..1, f x * a x) + (∫ x in (0 : ℝ)..1, g x * a x) := by
  have hf := l2_mul_continuous_intervalIntegrable f a ha
  have hg := l2_mul_continuous_intervalIntegrable g a ha
  rw [← intervalIntegral.integral_add hf hg]
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le zero_le_one]
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [hx]
  change (f x + g x) * a x = f x * a x + g x * a x
  ring

lemma interval_test_pairing_smul (c : ℂ) (f : SourceIntervalL2)
    (a : ℝ → ℂ) :
    (∫ x in (0 : ℝ)..1, (c • f) x * a x) =
      c * (∫ x in (0 : ℝ)..1, f x * a x) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le zero_le_one]
  filter_upwards [Lp.coeFn_smul c f] with x hx
  rw [hx]
  change (c * f x) * a x = c * (f x * a x)
  ring

lemma weakDerivative_add {f df g dg : SourceIntervalL2}
    (hf : HasWeakDerivative f df) (hg : HasWeakDerivative g dg) :
    HasWeakDerivative (↑↑(f + g)) (↑↑(df + dg)) := by
  intro ψ hs hc hU
  have hψ : Continuous (fun x => (ψ x : ℂ)) := Complex.continuous_ofReal.comp hs.continuous
  have hdψ : Continuous (fun x => ((deriv ψ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hs.continuous_deriv (by simp))
  rw [interval_test_pairing_add f g _ hdψ, interval_test_pairing_add df dg _ hψ,
    hf ψ hs hc hU, hg ψ hs hc hU]
  ring

lemma weakDerivative_smul (c : ℂ) {f df : SourceIntervalL2}
    (hf : HasWeakDerivative f df) : HasWeakDerivative (↑↑(c • f)) (↑↑(c • df)) := by
  intro ψ hs hc hU
  rw [interval_test_pairing_smul, interval_test_pairing_smul, hf ψ hs hc hU]
  ring

def h1Zero : H1 := NlsGge.Atomic.LIB028.smoothH1 (0 : ℝ → ℂ)
  contDiff_const HasCompactSupport.zero

@[simp] lemma h1Zero_value : h1Zero.value = 0 :=
  MemLp.toLp_zero (NlsGge.Atomic.LIB028.smooth_memLp (0 : ℝ → ℂ)
    contDiff_const HasCompactSupport.zero)

@[simp] lemma h1Zero_traceLeft : traceLeft h1Zero = 0 :=
  NlsGge.Atomic.LIB028.smoothH1_traceLeft _ _ _ (by simp)

@[simp] lemma h1Zero_traceRight : traceRight h1Zero = 0 :=
  NlsGge.Atomic.LIB028.smoothH1_traceRight _ _ _ (by simp)

def h1Add (f g : H1) : H1 where
  value := f.value + g.value
  derivative := f.derivative + g.derivative
  weak := weakDerivative_add f.weak g.weak

def h1Smul (c : ℂ) (f : H1) : H1 where
  value := c • f.value
  derivative := c • f.derivative
  weak := weakDerivative_smul c f.weak

lemma representative_h1Add (f g : H1) :
    representative (h1Add f g) = representative f + representative g := by
  symm
  apply representative_eq_of_ae
  filter_upwards [representative_ae f, representative_ae g,
    Lp.coeFn_add f.value g.value, ae_restrict_mem measurableSet_Ioc] with x hf hg hv hx
  have hm : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  rw [IccExtend_of_mem zero_le_one _ hm] at hf hg ⊢
  change representative f ⟨x, hm⟩ + representative g ⟨x, hm⟩ = (f.value + g.value) x
  rw [hv, hf, hg]
  rfl

lemma representative_h1Smul (c : ℂ) (f : H1) :
    representative (h1Smul c f) = c • representative f := by
  symm
  apply representative_eq_of_ae
  filter_upwards [representative_ae f, Lp.coeFn_smul c f.value,
    ae_restrict_mem measurableSet_Ioc] with x hf hv hx
  have hm : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  rw [IccExtend_of_mem zero_le_one _ hm] at hf ⊢
  change c • representative f ⟨x, hm⟩ = (c • f.value) x
  rw [hv, hf]
  rfl

@[simp] lemma traceLeft_h1Add (f g : H1) :
    traceLeft (h1Add f g) = traceLeft f + traceLeft g := by
  simp [traceLeft, representative_h1Add]

@[simp] lemma traceRight_h1Add (f g : H1) :
    traceRight (h1Add f g) = traceRight f + traceRight g := by
  simp [traceRight, representative_h1Add]

@[simp] lemma traceLeft_h1Smul (c : ℂ) (f : H1) :
    traceLeft (h1Smul c f) = c • traceLeft f := by
  simp [traceLeft, representative_h1Smul]

@[simp] lemma traceRight_h1Smul (c : ℂ) (f : H1) :
    traceRight (h1Smul c f) = c • traceRight f := by
  simp [traceRight, representative_h1Smul]


def h1PairZero : H1Pair := fun _ => h1Zero

def h1PairAdd (f g : H1Pair) : H1Pair := fun b => h1Add (f b) (g b)

def h1PairSmul (c : ℂ) (f : H1Pair) : H1Pair := fun b => h1Smul c (f b)

@[simp] lemma h1PairValue_zero : h1PairValue h1PairZero = 0 := by
  apply PiLp.ext
  intro b
  exact h1Zero_value

@[simp] lemma h1PairValue_add (f g : H1Pair) :
    h1PairValue (h1PairAdd f g) = h1PairValue f + h1PairValue g := by
  apply PiLp.ext
  intro b
  rfl

@[simp] lemma h1PairValue_smul (c : ℂ) (f : H1Pair) :
    h1PairValue (h1PairSmul c f) = c • h1PairValue f := by
  apply PiLp.ext
  intro b
  rfl

lemma boundary_zero (bc : ZSBoundaryCondition) : HasZSBoundaryCondition bc h1PairZero := by
  cases bc <;> simp [HasZSBoundaryCondition, h1PairZero]

lemma boundary_add (bc : ZSBoundaryCondition) {f g : H1Pair}
    (hf : HasZSBoundaryCondition bc f) (hg : HasZSBoundaryCondition bc g) :
    HasZSBoundaryCondition bc (h1PairAdd f g) := by
  cases bc with
  | dirichlet =>
    rcases hf with ⟨hf0, hf1⟩
    rcases hg with ⟨hg0, hg1⟩
    simp [HasZSBoundaryCondition, h1PairAdd, hf0, hf1, hg0, hg1]
  | neumann =>
    rcases hf with ⟨hf0, hf1⟩
    rcases hg with ⟨hg0, hg1⟩
    simp [HasZSBoundaryCondition, h1PairAdd, hf0, hf1, hg0, hg1, add_comm]
  | periodic =>
    change ∀ b, traceRight (f b) = traceLeft (f b) at hf
    change ∀ b, traceRight (g b) = traceLeft (g b) at hg
    simp [HasZSBoundaryCondition, h1PairAdd, hf, hg]
  | antiperiodic =>
    change ∀ b, traceRight (f b) = -traceLeft (f b) at hf
    change ∀ b, traceRight (g b) = -traceLeft (g b) at hg
    simp [HasZSBoundaryCondition, h1PairAdd, hf, hg, add_comm]

lemma boundary_smul (bc : ZSBoundaryCondition) (c : ℂ) {f : H1Pair}
    (hf : HasZSBoundaryCondition bc f) : HasZSBoundaryCondition bc (h1PairSmul c f) := by
  cases bc with
  | dirichlet =>
    rcases hf with ⟨hf0, hf1⟩
    simp [HasZSBoundaryCondition, h1PairSmul, hf0, hf1]
  | neumann =>
    rcases hf with ⟨hf0, hf1⟩
    simp [HasZSBoundaryCondition, h1PairSmul, hf0, hf1]
  | periodic =>
    change ∀ b, traceRight (f b) = traceLeft (f b) at hf
    simp [HasZSBoundaryCondition, h1PairSmul, hf]
  | antiperiodic =>
    change ∀ b, traceRight (f b) = -traceLeft (f b) at hf
    simp [HasZSBoundaryCondition, h1PairSmul, hf]

/-- The actual image domain, with algebraic closure proved from literal traces. -/
def zsDomain (bc : ZSBoundaryCondition) : Submodule ℂ SourcePairL2 where
  carrier := zsBoundaryDomain bc
  zero_mem' := ⟨h1PairZero, boundary_zero bc, h1PairValue_zero⟩
  add_mem' := by
    rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨h1PairAdd f g, boundary_add bc hf hg, h1PairValue_add f g⟩
  smul_mem' := by
    rintro c x ⟨f, hf, rfl⟩
    exact ⟨h1PairSmul c f, boundary_smul bc c hf, h1PairValue_smul c f⟩

lemma zsApply_add (φ : SourcePairL2) (f g : H1Pair) :
    zsApply φ (h1PairAdd f g) = zsApply φ f + zsApply φ g := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [zsApply_ae φ (h1PairAdd f g) b, zsApply_ae φ f b,
    zsApply_ae φ g b, Lp.coeFn_add (zsApply φ f b) (zsApply φ g b),
    Lp.coeFn_add (f b).derivative (g b).derivative,
    Lp.coeFn_add (f (!b)).value (g (!b)).value] with x h h1 h2 ha hd hv
  change zsApply φ (h1PairAdd f g) b x = (zsApply φ f b + zsApply φ g b) x
  rw [ha, h]
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp only [zsExpression, h1PairAdd, h1Add] at hd hv ⊢
  rw [hd, hv]
  simp only [Pi.add_apply]
  ring

lemma zsApply_smul (φ : SourcePairL2) (c : ℂ) (f : H1Pair) :
    zsApply φ (h1PairSmul c f) = c • zsApply φ f := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [zsApply_ae φ (h1PairSmul c f) b, zsApply_ae φ f b,
    Lp.coeFn_smul c (zsApply φ f b), Lp.coeFn_smul c (f b).derivative,
    Lp.coeFn_smul c (f (!b)).value] with x h h1 ha hd hv
  change zsApply φ (h1PairSmul c f) b x = (c • zsApply φ f b) x
  rw [ha, h]
  simp only [Pi.smul_apply]
  rw [h1]
  simp only [zsExpression, h1PairSmul, h1Smul] at hd hv ⊢
  rw [hd, hv]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def domainLift {bc : ZSBoundaryCondition} (x : zsDomain bc) : H1Pair :=
  Classical.choose x.property

lemma domainLift_boundary {bc : ZSBoundaryCondition} (x : zsDomain bc) :
    HasZSBoundaryCondition bc (domainLift x) := (Classical.choose_spec x.property).1

@[simp] lemma domainLift_value {bc : ZSBoundaryCondition} (x : zsDomain bc) :
    h1PairValue (domainLift x) = x := (Classical.choose_spec x.property).2

lemma domainLift_eq {bc : ZSBoundaryCondition} (x : zsDomain bc) (f : H1Pair)
    (hv : h1PairValue f = x) : domainLift x = f := by
  apply h1PairValue_injective
  exact (domainLift_value x).trans hv.symm

/-- The genuine ZS differential expression on the exact source boundary domain. -/
def zsRealization (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    SourcePairL2 →ₗ.[ℂ] SourcePairL2 where
  domain := zsDomain bc
  toFun :=
    { toFun := fun x => zsApply φ (domainLift x)
      map_add' := by
        intro x y
        rw [domainLift_eq (x + y) (h1PairAdd (domainLift x) (domainLift y))
          (by simp), zsApply_add]
      map_smul' := by
        intro c x
        rw [domainLift_eq (c • x) (h1PairSmul c (domainLift x)) (by simp), zsApply_smul]
        rfl }

@[simp] lemma zsRealization_apply (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : H1Pair) (hf : HasZSBoundaryCondition bc f) :
    zsRealization φ bc ⟨h1PairValue f, ⟨f, hf, rfl⟩⟩ = zsApply φ f := by
  change zsApply φ (domainLift (⟨h1PairValue f, ⟨f, hf, rfl⟩⟩ : zsDomain bc)) = zsApply φ f
  exact congrArg (zsApply φ) (domainLift_eq _ f rfl)

@[simp] lemma zsRealization_domain_eq (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ((zsRealization φ bc).domain : Set SourcePairL2) = zsBoundaryDomain bc := rfl

theorem zsRealization_dense (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    Dense ((zsRealization φ bc).domain : Set SourcePairL2) :=
  NlsGge.Atomic.LIB028.zs_boundary_domain_dense bc

lemma zsRealization_formalAdjoint {φ : SourcePairL2} (hφ : IsRealType φ)
    (bc : ZSBoundaryCondition) : (zsRealization φ bc).IsFormalAdjoint (zsRealization φ bc) := by
  intro x y
  change inner ℂ (zsApply φ (domainLift x)) (y : SourcePairL2) =
    inner ℂ (x : SourcePairL2) (zsApply φ (domainLift y))
  rw [← domainLift_value x, ← domainLift_value y]
  exact NlsGge.Atomic.LIB028.zs_boundary_domain_symmetric hφ bc _ _
    (domainLift_boundary x) (domainLift_boundary y)


lemma smoothPair_boundary (bc : ZSBoundaryCondition) (u : Bool → ℝ → ℂ)
    (hus : ∀ b, ContDiff ℝ ∞ (u b)) (huc : ∀ b, HasCompactSupport (u b))
    (huU : ∀ b, tsupport (u b) ⊆ Ioo (0 : ℝ) 1) :
    HasZSBoundaryCondition bc (fun b => NlsGge.Atomic.LIB028.smoothH1 (u b) (hus b) (huc b)) := by
  have hL b := NlsGge.Atomic.LIB028.smoothH1_traceLeft (u b) (hus b) (huc b) (huU b)
  have hR b := NlsGge.Atomic.LIB028.smoothH1_traceRight (u b) (hus b) (huc b) (huU b)
  cases bc <;> simp [HasZSBoundaryCondition, hL, hR]

/-- Actual Hilbert pairings on the domain imply the literal smooth-test witness. -/
lemma witness_of_domain_pairing {φ g h : SourcePairL2} (bc : ZSBoundaryCondition)
    (hp : ∀ f : H1Pair, HasZSBoundaryCondition bc f →
      inner ℂ (zsApply φ f) g = inner ℂ (h1PairValue f) h) :
    IsAdjointDomainWitness φ g h := by
  intro u hus huc huU
  let f : H1Pair := fun b => NlsGge.Atomic.LIB028.smoothH1 (u b) (hus b) (huc b)
  have hv b : (fun x => (f b).value x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] u b :=
    (NlsGge.Atomic.LIB028.smooth_memLp (u b) (hus b) (huc b)).coeFn_toLp
  have hd b : (fun x => (f b).derivative x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv (u b) :=
    (NlsGge.Atomic.LIB028.smooth_deriv_memLp (u b) (hus b) (huc b)).coeFn_toLp
  have heq := hp f (smoothPair_boundary bc u hus huc huU)
  rw [NlsGge.Atomic.LIB027.sourcePair_inner_eq_integral,
    NlsGge.Atomic.LIB027.sourcePair_inner_eq_integral] at heq
  have hleft : (∫ x in (0 : ℝ)..1,
      star (zsApply φ f true x) * g true x + star (zsApply φ f false x) * g false x) =
      ∫ x in (0 : ℝ)..1,
        star (zsExpression φ u (fun b => deriv (u b)) true x) * g true x +
        star (zsExpression φ u (fun b => deriv (u b)) false x) * g false x := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le zero_le_one]
    filter_upwards [zsApply_ae φ f true, zsApply_ae φ f false,
      hv true, hv false, hd true, hd false] with x hat haf hvt hvf hdt hdf
    simp only [zsExpression, Bool.not_true, Bool.not_false, ↓reduceIte] at hat haf ⊢
    rw [hat, haf, hvt, hvf, hdt, hdf]
  have hright : (∫ x in (0 : ℝ)..1,
      star (h1PairValue f true x) * h true x + star (h1PairValue f false x) * h false x) =
      ∫ x in (0 : ℝ)..1, star (u true x) * h true x + star (u false x) * h false x := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le zero_le_one]
    filter_upwards [hv true, hv false] with x ht hf
    change star ((f true).value x) * h true x + star ((f false).value x) * h false x = _
    rw [ht, hf]
  exact hleft.symm.trans (heq.trans hright)

/-- The regularity theorem supplies an actual weak H1 graph, with its proved L2 derivative. -/
def adjointH1 {φ g h : SourcePairL2} (hw : IsAdjointDomainWitness φ g h) : H1Pair :=
  fun b =>
    { value := g b
      derivative := (NlsGge.Atomic.LIB029.adjointDerivative_memLp hw b).toLp
        (NlsGge.Atomic.LIB029.adjointDerivative φ g h b)
      weak := NlsGge.Atomic.LIB029.weakDerivative_congr_right
        (NlsGge.Atomic.LIB029.adjoint_hasWeakDerivative hw b)
        (NlsGge.Atomic.LIB029.adjointDerivative_memLp hw b).coeFn_toLp }

@[simp] lemma adjointH1_value {φ g h : SourcePairL2} (hw : IsAdjointDomainWitness φ g h) :
    h1PairValue (adjointH1 hw) = g := by
  apply PiLp.ext
  intro b
  rfl

lemma realType_swap_ae {φ : SourcePairL2} (hφ : IsRealType φ) (b : Bool) :
    (fun x => star (φ (!b) x)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun x => φ b x) := by
  have heq : φ false = star (φ true) := hφ
  have ha : (fun x => φ false x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => star (φ true x)) := by
    rw [heq]
    exact Lp.coeFn_star (φ true)
  cases b
  · exact ha.symm
  · filter_upwards [ha] with x hx
    simp only [Bool.not_true]
    rw [hx, star_star]

lemma adjointH1_action {φ g h : SourcePairL2} (hφ : IsRealType φ)
    (hw : IsAdjointDomainWitness φ g h) : zsApply φ (adjointH1 hw) = h := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [zsApply_ae φ (adjointH1 hw) b,
    (NlsGge.Atomic.LIB029.adjointDerivative_memLp hw b).coeFn_toLp,
    realType_swap_ae hφ b] with x hA hd hreal
  rw [hA]
  change (if b then Complex.I else -Complex.I) *
    ((NlsGge.Atomic.LIB029.adjointDerivative_memLp hw b).toLp
      (NlsGge.Atomic.LIB029.adjointDerivative φ g h b)) x + φ b x * g (!b) x = h b x
  rw [hd]
  dsimp [NlsGge.Atomic.LIB029.adjointDerivative]
  simp only [starRingEnd_apply]
  rw [hreal]
  cases b <;> simp [mul_sub, ← mul_assoc]
  ring_nf
  simp

lemma adjoint_domain_pairing (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (y : (zsRealization φ bc).adjoint.domain) (f : H1Pair)
    (hf : HasZSBoundaryCondition bc f) :
    inner ℂ (zsApply φ f) (y : SourcePairL2) =
      inner ℂ (h1PairValue f) ((zsRealization φ bc).adjoint y) := by
  have hp := ((zsRealization φ bc).adjoint_isFormalAdjoint
    (zsRealization_dense φ bc)).symm ⟨h1PairValue f, ⟨f, hf, rfl⟩⟩ y
  change inner ℂ (zsApply φ (domainLift
    (⟨h1PairValue f, ⟨f, hf, rfl⟩⟩ : zsDomain bc))) (y : SourcePairL2) =
      inner ℂ (h1PairValue f) ((zsRealization φ bc).adjoint y) at hp
  rw [domainLift_eq _ f rfl] at hp
  exact hp

lemma adjoint_domain_lift {φ : SourcePairL2} (hφ : IsRealType φ)
    (bc : ZSBoundaryCondition) (y : (zsRealization φ bc).adjoint.domain) :
    ∃ (G : H1Pair), HasZSBoundaryCondition bc G ∧
      h1PairValue G = (y : SourcePairL2) ∧
      zsApply φ G = (zsRealization φ bc).adjoint y := by
  have hw : IsAdjointDomainWitness φ (y : SourcePairL2) ((zsRealization φ bc).adjoint y) :=
    witness_of_domain_pairing bc (adjoint_domain_pairing φ bc y)
  let G := adjointH1 hw
  have hval : h1PairValue G = (y : SourcePairL2) := adjointH1_value hw
  have hact : zsApply φ G = (zsRealization φ bc).adjoint y := adjointH1_action hφ hw
  refine ⟨G, ?_, hval, hact⟩
  apply (NlsGge.Atomic.LIB030.zs_adjoint_boundary_iff bc G).mp
  intro f hf
  rw [← NlsGge.Atomic.LIB027.zs_green_identity hφ, hval, hact,
    adjoint_domain_pairing φ bc y f hf, sub_self]

lemma zsRealization_adjoint_le {φ : SourcePairL2} (hφ : IsRealType φ)
    (bc : ZSBoundaryCondition) : (zsRealization φ bc).adjoint ≤ zsRealization φ bc := by
  have hmem (y : (zsRealization φ bc).adjoint.domain) :
      ∃ hy : (y : SourcePairL2) ∈ (zsRealization φ bc).domain,
        zsRealization φ bc ⟨y, hy⟩ = (zsRealization φ bc).adjoint y := by
    obtain ⟨G, hG, hv, ha⟩ := adjoint_domain_lift hφ bc y
    refine ⟨⟨G, hG, hv⟩, ?_⟩
    change zsApply φ (domainLift (⟨(y : SourcePairL2), ⟨G, hG, hv⟩⟩ : zsDomain bc)) =
      (zsRealization φ bc).adjoint y
    exact (congrArg (zsApply φ) (domainLift_eq _ G hv)).trans ha
  refine ⟨fun x hx => (hmem ⟨x, hx⟩).choose, ?_⟩
  intro x y hxy
  obtain ⟨hx, hval⟩ := hmem x
  have hy : y = ⟨(x : SourcePairL2), hx⟩ := Subtype.ext hxy.symm
  subst y
  exact hval.symm

/-- Every real-type L2 potential gives the actual Mathlib selfadjoint realization
on each of the four literal source H1 boundary domains. -/
theorem zs_real_selfAdjoint {φ : SourcePairL2} (hφ : IsRealType φ)
    (bc : ZSBoundaryCondition) : IsSelfAdjoint (zsRealization φ bc) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm (zsRealization_adjoint_le hφ bc)
  exact (zsRealization_formalAdjoint hφ bc).le_adjoint (zsRealization_dense φ bc)

/-- Density and selfadjointness on the exact source domain, with no extra regularity
or boundedness premise on the potential. -/
theorem zs_real_denselyDefined_selfAdjoint {φ : SourcePairL2} (hφ : IsRealType φ)
    (bc : ZSBoundaryCondition) :
    Dense ((zsRealization φ bc).domain : Set SourcePairL2) ∧ IsSelfAdjoint (zsRealization φ bc) :=
  ⟨zsRealization_dense φ bc, zs_real_selfAdjoint hφ bc⟩

end NlsGge.Atomic.LIB033
