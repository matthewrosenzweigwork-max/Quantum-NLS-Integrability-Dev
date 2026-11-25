import Mathlib
import NlsGge.Atomic.LIB.LIB026
import NlsGge.Atomic.IntervalZS

/-!
# LIB-029: H1 regularity of adjoint-domain vectors

The source adjoint hypothesis is only the literal pairing against compactly supported
smooth pairs. Single-component real tests identify the weak derivative, with the
swapped, conjugated potential entries required by the formal adjoint. L2 times L2
first gives L1. LIB-026 constructs AC representatives, which are bounded on the
closed unit interval; this gives essentially bounded original L2 classes.

The potential product and then the weak derivative are consequently L2. Bundling
these proved derivatives gives an H1 pair whose L2 value is exactly the original
state. The potential pair is arbitrary complex L2; no endpoint relation is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal Topology
namespace NlsGge.Atomic.LIB029
open NlsGge.Schur NlsGge.Atomic.LIB026
open Filter

lemma weakDerivative_congr_right {f d d' : ℝ → ℂ}
    (h : Interval.HasWeakDerivative f d)
    (heq : d' =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] d) :
    Interval.HasWeakDerivative f d' := by
  intro ψ hψs hψc hψU
  have hI : (∫ x in (0 : ℝ)..1, d' x * (ψ x : ℂ)) =
      ∫ x in (0 : ℝ)..1, d x * (ψ x : ℂ) := by
    apply intervalIntegral.integral_congr_ae_restrict
    change ∀ᵐ x ∂volume.restrict (uIoc (0 : ℝ) 1), d' x * (ψ x : ℂ) = d x * (ψ x : ℂ)
    simpa only [uIoc_of_le zero_le_one] using
      heq.mono (fun x hx => congrArg (fun z : ℂ => z * (ψ x : ℂ)) hx)
  rw [hI]
  exact h ψ hψs hψc hψU

lemma memLp_top_of_weakDerivative (f : SourceIntervalL2) {d : ℝ → ℂ}
    (hd : IntervalIntegrable d volume 0 1)
    (hweak : Interval.HasWeakDerivative (fun x => f x) d) :
    MemLp (fun x => f x) ∞ (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨F, hF, hfae, _⟩ := exists_ac_rep_of_weakDerivative (intervalIntegrable_L2 f) hd hweak
  obtain ⟨C, hC⟩ := hF.exists_bound
  apply memLp_top_of_bound (Lp.aestronglyMeasurable f) C
  filter_upwards [hfae, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  rw [hx]
  exact hC x (by simpa only [uIcc_of_le zero_le_one] using
    (show x ∈ Icc (0 : ℝ) 1 from ⟨hmem.1.le, hmem.2⟩))

lemma exists_H1_of_memLp_weakDerivative (f : SourceIntervalL2) {d : ℝ → ℂ}
    (hd : MemLp d 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hweak : Interval.HasWeakDerivative (fun x => f x) d) :
    ∃ fH1 : Interval.H1, fH1.value = f := by
  exact ⟨⟨f, hd.toLp d, weakDerivative_congr_right hweak hd.coeFn_toLp⟩, rfl⟩

/-- The derivative forced by the distributional formal adjoint; potential channels swap. -/
def adjointDerivative (φ g h : SourcePairL2) (b : Bool) (x : ℝ) : ℂ :=
  (if b then -Complex.I else Complex.I) *
    (h b x - star (φ (!b) x) * g (!b) x)

lemma adjointDerivative_intervalIntegrable (φ g h : SourcePairL2) (b : Bool) :
    IntervalIntegrable (adjointDerivative φ g h b) volume 0 1 := by
  have hp : Integrable (fun x => star (φ (!b) x) * g (!b) x)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Lp.memLp (φ (!b))).star.integrable_mul (Lp.memLp (g (!b)))
  exact ((intervalIntegrable_L2 (h b)).sub
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hp)).const_mul _


lemma adjoint_normalized_test_pairing {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) (b : Bool)
    (ψ : ℝ → ℝ) (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ Ioo (0 : ℝ) 1) :
    (if b then -Complex.I else Complex.I) *
        (∫ x in (0 : ℝ)..1, g b x * ((deriv ψ x : ℝ) : ℂ)) +
      (∫ x in (0 : ℝ)..1, (star (φ (!b) x) * g (!b) x) * (ψ x : ℂ)) =
        ∫ x in (0 : ℝ)..1, h b x * (ψ x : ℂ) := by
  let test : Bool → ℝ → ℂ := fun c x => if c = b then (ψ x : ℂ) else 0
  have hcast : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψs
  have hcastc : HasCompactSupport (fun x => (ψ x : ℂ)) :=
    hψc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcastU : tsupport (fun x => (ψ x : ℂ)) ⊆ Ioo (0 : ℝ) 1 := by
    simpa [tsupport, Function.support] using hψU
  have htests (c : Bool) : ContDiff ℝ ∞ (test c) := by
    by_cases hcb : c = b
    · simpa only [test, hcb, ↓reduceIte] using hcast
    · simpa only [test, hcb, ↓reduceIte] using (contDiff_const (c := (0 : ℂ)))
  have htestc (c : Bool) : HasCompactSupport (test c) := by
    by_cases hcb : c = b
    · simpa only [test, hcb, ↓reduceIte] using hcastc
    · simp [test, hcb, HasCompactSupport]
  have htestU (c : Bool) : tsupport (test c) ⊆ Ioo (0 : ℝ) 1 := by
    by_cases hcb : c = b
    · simpa only [test, hcb, ↓reduceIte] using hcastU
    · simp [test, hcb]
  have hdercast (x : ℝ) : deriv (fun x => (ψ x : ℂ)) x = ((deriv ψ x : ℝ) : ℂ) :=
    (((hψs.differentiable (by simp)) x).hasDerivAt.ofReal_comp).deriv
  have hpair := hw test htests htestc htestU
  have hp : IntervalIntegrable (fun x => star (φ (!b) x) * g (!b) x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((Lp.memLp (φ (!b))).star.integrable_mul (Lp.memLp (g (!b))))
  have hψcont : Continuous (fun x => (ψ x : ℂ)) := hcast.continuous
  have hψdcont : Continuous (fun x => ((deriv ψ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hψs.continuous_deriv (by simp))
  have hA := (intervalIntegrable_L2 (g b)).mul_continuousOn hψdcont.continuousOn
  have hB := hp.mul_continuousOn hψcont.continuousOn
  have hpoint (x : ℝ) :
      star (Interval.zsExpression φ test (fun c => deriv (test c)) true x) * g true x +
        star (Interval.zsExpression φ test (fun c => deriv (test c)) false x) * g false x =
      (if b then -Complex.I else Complex.I) * (g b x * ((deriv ψ x : ℝ) : ℂ)) +
        (star (φ (!b) x) * g (!b) x) * (ψ x : ℂ) := by
    cases b <;> simp [Interval.zsExpression, test, hdercast] <;> ring
  have hleft :
      (∫ x in (0 : ℝ)..1,
        star (Interval.zsExpression φ test (fun c => deriv (test c)) true x) * g true x +
        star (Interval.zsExpression φ test (fun c => deriv (test c)) false x) * g false x) =
      (if b then -Complex.I else Complex.I) *
        (∫ x in (0 : ℝ)..1, g b x * ((deriv ψ x : ℝ) : ℂ)) +
        (∫ x in (0 : ℝ)..1, (star (φ (!b) x) * g (!b) x) * (ψ x : ℂ)) := by
    rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
      intervalIntegral.integral_add (hA.const_mul _) hB,
      intervalIntegral.integral_const_mul]
  have hright :
      (∫ x in (0 : ℝ)..1, star (test true x) * h true x + star (test false x) * h false x) =
        ∫ x in (0 : ℝ)..1, h b x * (ψ x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x _
    cases b <;> simp [test] <;> ring
  exact hleft.symm.trans (hpair.trans hright)

/-- Scalarization of the adjoint test pairing gives the actual L1 weak derivative. -/
theorem adjoint_hasWeakDerivative {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) (b : Bool) :
    Interval.HasWeakDerivative (fun x => g b x) (adjointDerivative φ g h b) := by
  intro ψ hψs hψc hψU
  have heq := adjoint_normalized_test_pairing hw b ψ hψs hψc hψU
  have hψcont : Continuous (fun x => (ψ x : ℂ)) :=
    Complex.continuous_ofReal.comp hψs.continuous
  have hC := (intervalIntegrable_L2 (h b)).mul_continuousOn hψcont.continuousOn
  have hp : IntervalIntegrable (fun x => star (φ (!b) x) * g (!b) x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((Lp.memLp (φ (!b))).star.integrable_mul (Lp.memLp (g (!b))))
  have hB := hp.mul_continuousOn hψcont.continuousOn
  have hDI : (∫ x in (0 : ℝ)..1, adjointDerivative φ g h b x * (ψ x : ℂ)) =
      (if b then -Complex.I else Complex.I) *
        ((∫ x in (0 : ℝ)..1, h b x * (ψ x : ℂ)) -
          (∫ x in (0 : ℝ)..1, (star (φ (!b) x) * g (!b) x) * (ψ x : ℂ))) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (if b then -Complex.I else Complex.I) *
          (h b x * (ψ x : ℂ) - (star (φ (!b) x) * g (!b) x) * (ψ x : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp [adjointDerivative]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hC hB]
  rw [hDI]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at heq ⊢
    linear_combination (-Complex.I) * heq +
      (∫ x in (0 : ℝ)..1, g false x * ((deriv ψ x : ℝ) : ℂ)) * Complex.I_sq
  · simp only [↓reduceIte] at heq ⊢
    linear_combination Complex.I * heq +
      (∫ x in (0 : ℝ)..1, g true x * ((deriv ψ x : ℝ) : ℂ)) * Complex.I_sq


/-- The distributional derivative is L1, so each component admits a bounded AC representative. -/
theorem adjoint_component_acRepresentative {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) (b : Bool) :
    ∃ F : ℝ → ℂ, AbsolutelyContinuousOnInterval F 0 1 ∧
      (fun x => g b x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] F ∧
      (∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 →
        HasDerivAt F (adjointDerivative φ g h b x) x) ∧
      ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ C := by
  obtain ⟨F, hF, hfae, hd⟩ := exists_ac_rep_of_weakDerivative
    (intervalIntegrable_L2 (g b)) (adjointDerivative_intervalIntegrable φ g h b)
    (adjoint_hasWeakDerivative hw b)
  obtain ⟨C, hC⟩ := hF.exists_bound
  exact ⟨F, hF, hfae, hd, C, by simpa only [uIcc_of_le zero_le_one] using hC⟩

/-- The L2 state components are essentially bounded as a proved consequence of the adjoint tests. -/
theorem adjoint_component_memLp_top {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) (b : Bool) :
    MemLp (fun x => g b x) ∞ (volume.restrict (Ioc (0 : ℝ) 1)) :=
  memLp_top_of_weakDerivative (g b) (adjointDerivative_intervalIntegrable φ g h b)
    (adjoint_hasWeakDerivative hw b)

/-- The bounded representative upgrades the adjoint potential product from L1 to L2. -/
theorem adjoint_potential_product_memLp {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) (b : Bool) :
    MemLp (fun x => star (φ (!b) x) * g (!b) x) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (Lp.memLp (φ (!b))).star.mul (adjoint_component_memLp_top hw (!b))

/-- Reinserting the proved bound makes the actual weak derivative square integrable. -/
theorem adjointDerivative_memLp {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) (b : Bool) :
    MemLp (adjointDerivative φ g h b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ((Lp.memLp (h b)).sub (adjoint_potential_product_memLp hw b)).const_mul _

/-- Every adjoint-domain witness has an H1 lift with exactly its original paired L2 value.
No real-type condition on the complex potential pair or endpoint condition is imposed. -/
theorem zs_adjoint_vector_H1 {φ g h : SourcePairL2}
    (hw : Interval.IsAdjointDomainWitness φ g h) :
    ∃ gH1 : Interval.H1Pair, Interval.h1PairValue gH1 = g := by
  have hcomponent (b : Bool) : ∃ F : Interval.H1, F.value = g b :=
    exists_H1_of_memLp_weakDerivative (g b) (adjointDerivative_memLp hw b)
      (adjoint_hasWeakDerivative hw b)
  choose G hG using hcomponent
  refine ⟨G, ?_⟩
  apply PiLp.ext
  intro b
  exact hG b

end NlsGge.Atomic.LIB029
