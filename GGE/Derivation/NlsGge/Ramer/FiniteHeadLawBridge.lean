import NlsGge.Ramer.FiniteGaussian
import NlsGge.Measure.FiniteGaussian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Finite head-law bridge: product complex Gaussian = standard Gaussian of the CM norm

Let `V` be a finite-dimensional real inner product space and `L : V ≃ₗ[ℝ] (ι → ℂ)` a
real-linear equivalence such that

  `‖v‖² = Σ_i 2 a_i ‖(L v)_i‖²`     (the Cameron–Martin norm, with the factor two).

Then the standard Gaussian of `V` (`finiteStdGaussian V`, density
`(2π)^{-d/2} exp(-‖v‖²/2)` against the inner-product volume) is carried by `L` onto the
project's concrete finite product law `NlsGge.Measure.finiteComplexGaussian a`, whose
factors are the transport to `ℂ` of two independent real Gaussians of variance
`1/(2 a_i)` (`componentVariance`).

The proof uses no Jacobian computation: `volume.map L` is an additive Haar measure on
`ι → ℂ`, hence a constant multiple of the product planar volume; the constant is then
forced by the fact that both sides are probability measures.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

/-- Pushing a density through a measurable equivalence. -/
theorem map_withDensity_comp_measurableEquiv {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (e : X ≃ᵐ Y) (f : Y → ℝ≥0∞) :
    (μ.withDensity (fun x => f (e x))).map e = (μ.map e).withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs, lintegral_map_equiv]

/-- **Finite head-law bridge.** If `L : V ≃ₗ[ℝ] (ι → ℂ)` carries the inner-product norm
of `V` to the Cameron–Martin norm `Σ_i 2 a_i |z_i|²` with all `a_i > 0`, then the
standard Gaussian of `V` is mapped by `L` onto the concrete product law
`finiteComplexGaussian a` (real-component variance `1/(2 a_i)`). -/
theorem finiteStdGaussian_map_eq_finiteComplexGaussian (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (L : V ≃ₗ[ℝ] (ι → ℂ)) (hL : ∀ v, ‖v‖ ^ 2 = ∑ i, 2 * a i * ‖L v i‖ ^ 2) :
    (finiteStdGaussian V).map L = NlsGge.Measure.finiteComplexGaussian a := by
  classical
  set e : V ≃L[ℝ] (ι → ℂ) := L.toContinuousLinearEquiv with he
  have hLe : (L : V → ι → ℂ) = e := rfl
  set em : V ≃ᵐ (ι → ℂ) := e.toHomeomorph.toMeasurableEquiv with hem
  have hLem : (L : V → ι → ℂ) = em := rfl
  -- Haar uniqueness on `ι → ℂ`
  set ν : Measure (ι → ℂ) := NlsGge.Measure.finiteComplexVolume ι with hν
  have : ν.IsAddHaarMeasure := by
    rw [hν, NlsGge.Measure.finiteComplexVolume]; infer_instance
  have : ((volume : Measure V).map e).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map (volume : Measure V)
  have hHaar : (volume : Measure V).map e =
      Measure.addHaarScalarFactor ((volume : Measure V).map e) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ ν
  set c : ℝ≥0∞ := (Measure.addHaarScalarFactor ((volume : Measure V).map e) ν : ℝ≥0∞)
  -- the common Gaussian kernel
  set k : (ι → ℂ) → ℝ := fun z => Real.exp (-∑ i, a i * ‖z i‖ ^ 2) with hk
  have hkm : Measurable (fun z => ENNReal.ofReal (k z)) := by
    simp only [hk]; fun_prop
  set ρ : Measure (ι → ℂ) := ν.withDensity (fun z => ENNReal.ofReal (k z)) with hρ
  set C0 : ℝ := (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) with hC0
  set P : ℝ := ∏ i, a i / π with hP
  have hC0pos : 0 < C0 := by rw [hC0]; have : 0 < 2 * π := by positivity
                             positivity
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => div_pos (ha i) pi_pos)
  -- left side as a constant multiple of ρ
  set g : (ι → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal C0 * ENNReal.ofReal (k z) with hg
  have hdensL : (fun v : V => ENNReal.ofReal (finiteGaussianDensity V v)) =
      fun v => g (em v) := by
    funext v
    simp only [hg]
    rw [← ENNReal.ofReal_mul hC0pos.le]
    congr 1
    simp only [finiteGaussianDensity, hk, ← hLem]
    congr 2
    rw [hL v, neg_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hLHS : (finiteStdGaussian V).map L = (c * ENNReal.ofReal C0) • ρ := by
    rw [finiteStdGaussian, hdensL, hLem, map_withDensity_comp_measurableEquiv volume em g]
    have : ((volume : Measure V).map em) = (volume : Measure V).map e := rfl
    rw [this, hHaar]
    change (c • ν).withDensity g = _
    rw [withDensity_smul_measure,
      show g = ENNReal.ofReal C0 • (fun z => ENNReal.ofReal (k z)) from rfl,
      withDensity_smul _ hkm, smul_smul]
  -- right side as a constant multiple of ρ
  have hRHS : NlsGge.Measure.finiteComplexGaussian a = ENNReal.ofReal P • ρ := by
    rw [NlsGge.Measure.finiteComplexGaussian_density a ha, hρ, ← withDensity_smul _ hkm]
    congr 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, hk, hP]
    rw [← ENNReal.ofReal_mul hPpos.le, Finset.prod_mul_distrib, Real.exp_neg,
      ← Real.exp_neg]
    congr 2
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1; ring
  -- both are probability measures; cancel the common finite nonzero mass of ρ
  have hprobL : ((c * ENNReal.ofReal C0) • ρ) Set.univ = 1 := by
    rw [← hLHS]; exact measure_univ
  have hprobR : (ENNReal.ofReal P • ρ) Set.univ = 1 := by
    rw [← hRHS]; exact measure_univ
  rw [Measure.smul_apply, smul_eq_mul] at hprobL hprobR
  have hP0 : ENNReal.ofReal P ≠ 0 := by simpa using hPpos
  have hM0 : ρ Set.univ ≠ 0 := by
    intro h; rw [h, mul_zero] at hprobR; exact zero_ne_one hprobR
  have hMt : ρ Set.univ ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top hP0] at hprobR; exact ENNReal.top_ne_one hprobR
  have hconst : c * ENNReal.ofReal C0 = ENNReal.ofReal P :=
    (ENNReal.mul_left_inj hM0 hMt).1 (hprobL.trans hprobR.symm)
  rw [hLHS, hRHS, hconst]

/-- **Finite Ramer formula on the concrete product head law.** Under the bridge
hypotheses, let `S` be a homeomorphism of `ι → ℂ` that is real-differentiable. Its
conjugate `T = L⁻¹ ∘ S ∘ L` is a differentiable map of `V`, and the inverse pushforward
of the concrete law `finiteComplexGaussian a` by `S` has density
`J_T(L⁻¹ z) = |det DT(L⁻¹ z)| exp(-(‖T(L⁻¹z)‖² - ‖L⁻¹z‖²)/2)`, where `‖·‖` is the
Cameron–Martin norm `Σ 2 a_i |·_i|²` carried by `V`. -/
theorem finiteComplexGaussian_map_symm_eq_withDensity_ramer (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (L : V ≃ₗ[ℝ] (ι → ℂ))
    (hL : ∀ v, ‖v‖ ^ 2 = ∑ i, 2 * a i * ‖L v i‖ ^ 2)
    (S : (ι → ℂ) ≃ₜ (ι → ℂ)) (hS : Differentiable ℝ S) :
    (NlsGge.Measure.finiteComplexGaussian a).map S.symm =
      (NlsGge.Measure.finiteComplexGaussian a).withDensity (fun z => ENNReal.ofReal
        (finiteRamerDensity (fun v => L.symm (S (L v))) (L.symm z))) := by
  set e : V ≃L[ℝ] (ι → ℂ) := L.toContinuousLinearEquiv with he
  set T : V ≃ₜ V := e.toHomeomorph.trans (S.trans e.symm.toHomeomorph) with hTdef
  have hTfun : (T : V → V) = fun v => L.symm (S (L v)) := rfl
  have hTd : Differentiable ℝ T := by
    rw [hTfun]
    exact e.symm.differentiable.comp (hS.comp e.differentiable)
  set em : V ≃ᵐ (ι → ℂ) := e.toHomeomorph.toMeasurableEquiv with hem
  have hLem : (L : V → ι → ℂ) = em := rfl
  have hbr := finiteStdGaussian_map_eq_finiteComplexGaussian a ha L hL
  rw [← hbr, hLem]
  have hcomp : (S.symm : (ι → ℂ) → (ι → ℂ)) ∘ em = em ∘ T.symm := by
    funext v
    change S.symm (e v) = e (e.symm (S.symm (e v)))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [Measure.map_map S.symm.continuous.measurable em.measurable, hcomp,
    ← Measure.map_map em.measurable T.symm.continuous.measurable,
    finiteStdGaussian_map_symm T hTd]
  have hf : (fun x : V => ENNReal.ofReal (finiteRamerDensity (T : V → V) x)) =
      fun x => (fun z => ENNReal.ofReal
        (finiteRamerDensity (fun v => L.symm (S (L v))) (L.symm z))) (em x) := by
    funext x
    rw [hTfun]
    change _ = ENNReal.ofReal (finiteRamerDensity (fun v => L.symm (S (L v))) (L.symm (L x)))
    rw [LinearEquiv.symm_apply_apply]
  rw [hf]
  exact map_withDensity_comp_measurableEquiv _ em (fun z => ENNReal.ofReal
    (finiteRamerDensity (fun v => L.symm (S (L v))) (L.symm z)))

end NlsGge.Ramer
