import LiebLiniger.FixedPeriod.Quantum.IntegralKernelOperator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Literal almost-everywhere action of the actual L²-kernel Riesz operator.
Author candidate; validation belongs to the root's lane B. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

section LiteralAction
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- The source literal integral, initially a totalized function. Integrability
and its AE identity with the constructed operator are proved below. -/
def kernelApplication (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) (x : X) : ℂ :=
  ∫ y, K (x, y) * u y ∂ν

/-- Fubini applies to the integrable weighted product, without a pointwise
assumption about representatives. -/
theorem inner_integralKernelOperator_eq_iteratedIntegral
    (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    inner ℂ v (integralKernelOperator μ ν K u) =
      ∫ x, conj (v x) * kernelApplication μ ν K u x ∂μ := by
  have hi := integrable_kernelPairingIntegrand μ ν K u v
  rw [inner_integralKernelOperator_eq_integral]
  calc
    _ = ∫ x, ∫ y, conj (v x) * K (x, y) * u y ∂ν ∂μ :=
      integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      unfold kernelApplication
      dsimp only
      rw [← integral_const_mul]
      congr 1
      funext y
      ring

variable [IsFiniteMeasure μ]

/-- On the physical finite output space, the unweighted product K(x,y)u(y)
is integrable before the literal integral is used. -/
theorem integrable_kernelApplicationIntegrand (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) :
    Integrable (fun z : X × Y => K z * u z.2) (μ.prod ν) := by
  have hi := integrable_kernelPairingIntegrand μ ν K u (Lp.const 2 μ (1 : ℂ))
  apply hi.congr
  have hc := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp
    (Lp.coeFn_const 2 μ (1 : ℂ))
  filter_upwards [hc] with z hz
  simp only [Function.comp_apply] at hz
  simp only [kernelPairingIntegrand, hz, Function.const_apply, map_one, one_mul]

/-- The input integral is a genuine integrable function for almost every
output coordinate. -/
theorem integrable_kernelApplication_sections (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * u y) ν :=
  (integrable_kernelApplicationIntegrand μ ν K u).prod_right_ae

theorem integrable_kernelApplication (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) :
    Integrable (kernelApplication μ ν K u) μ :=
  (integrable_kernelApplicationIntegrand μ ν K u).integral_prod_left

/-- The Riesz operator has exactly the literal source kernel action almost
everywhere. The finite-measure premise is realized by physical length measure. -/
theorem integralKernelOperator_coeFn (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) :
    integralKernelOperator μ ν K u =ᵐ[μ] kernelApplication μ ν K u := by
  have hT : Integrable (integralKernelOperator μ ν K u) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top (integralKernelOperator μ ν K u)
        fact_one_le_two_ennreal.elim (measure_ne_top μ Set.univ)
  have hA := integrable_kernelApplication μ ν K u
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hT.integrableOn) (fun _ _ _ => hA.integrableOn)
  intro s hs hμs
  let v : Lp ℂ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℂ)
  calc
    (∫ x in s, integralKernelOperator μ ν K u x ∂μ) =
        inner ℂ v (integralKernelOperator μ ν K u) :=
      (L2.inner_indicatorConstLp_one hs hμs.ne _).symm
    _ = ∫ x, conj (v x) * kernelApplication μ ν K u x ∂μ :=
      inner_integralKernelOperator_eq_iteratedIntegral μ ν K u v
    _ = ∫ x, s.indicator (kernelApplication μ ν K u) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
        (hμs := hμs.ne) (c := (1 : ℂ))] with x hx
      change conj (indicatorConstLp 2 hs hμs.ne (1 : ℂ) x) * _ = _
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = ∫ x in s, kernelApplication μ ν K u x ∂μ := integral_indicator hs

/-- Square integrability follows from the proved literal AE realization. -/
theorem memLp_kernelApplication (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) :
    MemLp (kernelApplication μ ν K u) 2 μ :=
  (Lp.memLp (integralKernelOperator μ ν K u)).ae_eq
    (integralKernelOperator_coeFn μ ν K u)

end LiteralAction

section SymmetricPairing
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Pairing a symmetric test vector with the actual sector projection simply
removes the projection; this is proved from selfadjointness and fixedness. -/
theorem inner_symmetricSectorProjection_eq (r : ℕ) (v : SymmetricSector μ r)
    (w : ProductL2 μ (Fin r)) :
    inner ℂ v (symmetricSectorProjection μ r w) = inner ℂ (v : ProductL2 μ (Fin r)) w := by
  change inner ℂ (v : ProductL2 μ (Fin r)) (symmetrizeL2 μ w) = _
  have hs := symmetrizeL2_isSymmetric (ι := Fin r) μ (v : ProductL2 μ (Fin r)) w
  change inner ℂ (symmetrizeL2 μ (v : ProductL2 μ (Fin r))) w =
    inner ℂ (v : ProductL2 μ (Fin r)) (symmetrizeL2 μ w) at hs
  rw [symmetricSector_fixed μ r v] at hs
  exact hs.symm

end SymmetricPairing

/-- The constructed interval coefficient is characterized on the complete
symmetric sector by the literal separately symmetrized kernel, exactly as in
KA/KD. No unproved output-symmetry identity is used as a premise. -/
theorem transferCoefficientIntervalOperator_pairing {L : ℝ} (hL : 0 ≤ L)
    (ζ : ℂ) (r : ℕ) (u v : SymmetricSector (transferIntervalMeasure L) r) :
    inner ℂ v (transferCoefficientIntervalOperator hL ζ r u) =
      ∫ z, conj ((v : ProductL2 (transferIntervalMeasure L) (Fin r)) z.1) *
        transferCoefficientKernelL2 hL ζ r z *
        (u : ProductL2 (transferIntervalMeasure L) (Fin r)) z.2
          ∂transferKernelMeasure L r := by
  change inner ℂ v (symmetricSectorProjection (transferIntervalMeasure L) r
    (integralKernelOperator (transferCoordinateMeasure L r) (transferCoordinateMeasure L r)
      (transferCoefficientKernelL2 hL ζ r) (u : ProductL2 (transferIntervalMeasure L) (Fin r)))) = _
  rw [inner_symmetricSectorProjection_eq]
  exact inner_integralKernelOperator_eq_integral _ _ _ _ _

end LiebLiniger.FixedPeriod.Quantum
