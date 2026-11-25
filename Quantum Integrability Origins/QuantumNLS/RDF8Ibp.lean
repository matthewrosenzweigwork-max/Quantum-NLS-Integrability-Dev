import Mathlib
import QuantumNLS.RootH1RatioAC
import QuantumNLS.WeakDerivatives
import QuantumNLS.Local001TransportB

/-!
# R-DF8F25DD, stage 1: Fourier coefficients of an absolutely continuous periodic representative

Source: `ROOT_H1_characterization.tex`, proof of `thm:root-H1-characterization`:
"For an entirely explicit regularity argument, Fourier coefficients converge at each fixed index;
for any finite set of indices, their weighted squares pass to the limit."

For `f ∈ L²(𝕋_L)` with an absolutely continuous periodic representative `g`, `g' = d ∈ L²(0,L)`
(the accepted `HaarResolvent.IsH1Rep`, as produced by R-D24009D4 for the ratio `r`):
* `ibp_chi`: periodic integration by parts against `χₙ(x) = e^{−ipₙx}`;
* `hasWeakDeriv_rep`: the circle class of `d` is the weak derivative of `f`;
* `weighted_le`: for every finite set `F` of indices,
  `Σ_{n∈F} pₙ² |f̂(n)|² ≤ ∫₀ᴸ |d|²` (Bessel).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Interval
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent QuantumNLS.Fourier QuantumNLS.WeakDerivatives

namespace QuantumNLS.RDF8Ibp

variable {L : ℝ} [hLf : Fact (0 < L)]

lemma chi_contDiff (n : ℤ) : ContDiff ℝ 1 (chi L n) := by
  unfold chi
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

lemma chi_period (n : ℤ) : chi L n L = 1 := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < L).ne'
  unfold chi
  rw [Complex.exp_eq_one_iff]
  refine ⟨-n, ?_⟩
  field_simp
  push_cast
  ring

lemma chi_zero (n : ℤ) : chi L n 0 = 1 := by
  simp [chi]

lemma intervalIntegrable_rep {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) :
    IntervalIntegrable d volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hLf.out.le).mpr (hf.2.1.integrable (by norm_num))

/-- **Periodic integration by parts** for an absolutely continuous representative. -/
theorem ibp_chi {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) (hp : g L = g 0) (n : ℤ) :
    ∫ x in (0 : ℝ)..L, chi L n x * d x = ikn L n * ∫ x in (0 : ℝ)..L, chi L n x * g x := by
  have hL : 0 < L := hLf.out
  have hgac := RootH1RatioAC.h1_ac hf
  have hgd := RootH1RatioAC.h1_ae_deriv hf
  have hdi := intervalIntegrable_rep hf
  have hchic : Continuous (chi L n) := (chi_contDiff n).continuous
  have hchiac : AbsolutelyContinuousOnInterval (chi L n) 0 L :=
    (chi_contDiff n).contDiffOn.absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval (fun x => chi L n x * g x) 0 L := by
    simpa only [smul_eq_mul] using hchiac.fun_smul hgac
  have hgc : ContinuousOn g (uIcc 0 L) := hgac.continuousOn
  have hi1 : IntervalIntegrable (fun x => -(ikn L n) * chi L n x * g x) volume 0 L :=
    ((continuous_const.mul hchic).continuousOn.mul hgc).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => chi L n x * d x) volume 0 L :=
    hdi.continuousOn_mul hchic.continuousOn
  have hFi := hi1.add hi2
  have hder : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      HasDerivAt (fun x => chi L n x * g x) (-(ikn L n) * chi L n t * g t + chi L n t * d t) t := by
    filter_upwards [hgd] with t ht
    exact (hasDerivAt_chi n t).mul ht
  have he := RootH1RatioAC.ac_integral_eq hL.le hP hFi hder (x := L) ⟨hL.le, le_rfl⟩
  rw [chi_period, chi_zero, hp, intervalIntegral.integral_add hi1 hi2] at he
  have h1 : ∫ x in (0 : ℝ)..L, -(ikn L n) * chi L n x * g x =
      -(ikn L n) * ∫ x in (0 : ℝ)..L, chi L n x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [h1] at he
  linear_combination -he

/-- The representative agrees with `f` almost everywhere on the physical interval. -/
lemma rep_ae {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (0 : ℝ) L)), f (x : AddCircle L) = g x := by
  have h1 := (ResetFreeResolventLOCAL001.CompletionB.circleH1_to_interval f g d hf).1
  have h2 := ResetFreeResolventLOCAL001.CompletionB.circleToInterval_coe_ae (L := L) f
  change ∀ᵐ x ∂(LocalSpectral.μI L), _
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← hx2, hx1]

/-- Interval form of a coefficient, for any function agreeing a.e. on the period. -/
lemma coeff_of_ae {F : AddCircle L → ℂ} {G : ℝ → ℂ}
    (h : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (0 : ℝ) L)), F (x : AddCircle L) = G x) (n : ℤ) :
    coeff L F n = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∫ x in (0 : ℝ)..L, chi L n x * G x := by
  rw [coeff_eq_interval]
  congr 1
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le hLf.out.le]
  have h' := (ae_restrict_iff' measurableSet_Ioc).mp h
  filter_upwards [h'] with x hx hxI
  rw [hx hxI]

/-- The circle class of the derivative. -/
def derivClass {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) : L2T L :=
  ResetFreeResolventLOCAL001.CompletionB.intervalToCircle L (hf.2.1.toLp d)

lemma derivClass_ae {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (0 : ℝ) L)), (derivClass hf : AddCircle L → ℂ) (x : AddCircle L) = d x := by
  have h1 := ResetFreeResolventLOCAL001.CompletionB.intervalToCircle_coe_ae (L := L) (hf.2.1.toLp d)
  have h2 := hf.2.1.coeFn_toLp
  change ∀ᵐ x ∂(LocalSpectral.μI L), _
  filter_upwards [h1, h2] with x hx1 hx2
  unfold derivClass
  rw [hx1]
  exact hx2

/-- **The circle class of `d` is the weak derivative of `f`.** -/
theorem coeff_derivClass {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) (hp : g L = g 0)
    (n : ℤ) :
    coeff L (derivClass hf : AddCircle L → ℂ) n = ikn L n * coeff L (f : AddCircle L → ℂ) n := by
  rw [coeff_of_ae (derivClass_ae hf), coeff_of_ae (rep_ae hf), ibp_chi hf hp]
  ring

theorem hasWeakDeriv_rep {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) (hp : g L = g 0) :
    HasWeakDeriv f (derivClass hf) :=
  hasWeakDeriv_of_coeff (coeff_derivClass hf hp)

/-- `∫_{𝕋_L} |D|² = ∫₀ᴸ |d|²`. -/
lemma integral_derivClass {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) :
    (∫ t, ‖(derivClass hf : AddCircle L → ℂ) t‖ ^ 2 ∂(volume : Measure (AddCircle L))) =
      ∫ x in (0 : ℝ)..L, ‖d x‖ ^ 2 := by
  rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le hLf.out.le]
  have h' := (ae_restrict_iff' measurableSet_Ioc).mp (derivClass_ae hf)
  filter_upwards [h'] with x hx hxI
  rw [hx hxI]

/-- **Weighted Bessel bound**: `Σ_{n∈F} pₙ² |f̂(n)|² ≤ ∫₀ᴸ |d|²` for every finite `F`. -/
theorem weighted_le {f : L2T L} {g d : ℝ → ℂ} (hf : IsH1Rep L f g d) (hp : g L = g 0)
    (F : Finset ℤ) :
    ∑ n ∈ F, freq L n ^ 2 * ‖fourierL2 L f n‖ ^ 2 ≤ ∫ x in (0 : ℝ)..L, ‖d x‖ ^ 2 := by
  have hs := hasSum_sq_coeff L (Lp.memLp (derivClass hf))
  rw [integral_derivClass hf] at hs
  have he : ∀ n, freq L n ^ 2 * ‖fourierL2 L f n‖ ^ 2 =
      ‖coeff L (derivClass hf : AddCircle L → ℂ) n‖ ^ 2 := by
    intro n
    rw [coeff_derivClass hf hp, norm_ikn_mul_sq, fourierL2_apply]
  simp only [he]
  exact sum_le_hasSum F (fun n _ => by positivity) hs

end QuantumNLS.RDF8Ibp

#print axioms QuantumNLS.RDF8Ibp.ibp_chi
#print axioms QuantumNLS.RDF8Ibp.hasWeakDeriv_rep
#print axioms QuantumNLS.RDF8Ibp.weighted_le
