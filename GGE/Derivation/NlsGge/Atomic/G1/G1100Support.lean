import Mathlib
import NlsGge.GK38.PairPotential
import NlsGge.GK38.GradFundamentalL2
import NlsGge.GK38.GradFundamentalPairing
import NlsGge.GK38.GradEigenKernels
import NlsGge.GK38.PoissonMixedTargets
import NlsGge.GK38.GradEigenRealState
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.GradEigenClosedKernelSymmetry
import NlsGge.Atomic.G1.G1062
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.ThirdConsultation.G1.G1098Host

/- G1-100 SUPPORT01 (proof development, AUTHOR; not self-reviewed; semantic fidelity not checked).
   Target NlsGge/Atomic/G1/G1100Support.lean, namespace NlsGge.Atomic.G1100Support.
   Supporting lemmas for G1_100 (Grebert-Kappeler Proposition 10.9). No hypothesis is added; every statement is about
   the landed mixedKernel / mixedColumn / pairKernelL2Class38 / realSlice objects.
   (1) real_inner_eq_integral: the real inner product of PhysicalL2 is the interval integral of Re(conj f * g) of the
       period-one representatives (polarization from integral_sq_coverRep38_one).
   (2) Bform: the real symplectic bracket Im<x,y> as a continuous real bilinear form; wedge_integral_eq: for
       real-symmetric pair kernels the integrated wedge is -2 I * Bform of the first-component classes.
   (3) pairing_eq: for a real-symmetric kernel K the complex bilinear pairing with realSlice W is 2 <star(class K).1, W>.
   (4) mixedKernel_realSymmetric: all mixed squared eigenfunction kernels have second component conj of the first
       (terminal states are anti-symmetric, I times an anti-symmetric kernel is real-symmetric). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38

open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1100Support
noncomputable section

theorem integrable_conj_mul (x y : PhysicalL2) :
    IntervalIntegrable (fun s : ℝ => starRingEnd ℂ (coverRep38 x s) * coverRep38 y s)
      volume 0 1 := by
  have hb : IntervalIntegrable
      (fun s : ℝ => (‖coverRep38 x s‖ ^ 2 + ‖coverRep38 y s‖ ^ 2) / 2) volume 0 1 :=
    ((intervalIntegrable_coverRep38_sq_one x).add
      (intervalIntegrable_coverRep38_sq_one y)).div_const 2
  refine hb.mono_fun' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact (((stronglyMeasurable_coverRep38 x).aestronglyMeasurable.star.mul
      (stronglyMeasurable_coverRep38 y).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self)
  · simp only [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖coverRep38 x s‖ - ‖coverRep38 y s‖), norm_nonneg (coverRep38 x s),
      norm_nonneg (coverRep38 y s)]

theorem sq_norm_add_pt (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (starRingEnd ℂ a * b).re + ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem real_inner_eq_integral (x y : PhysicalL2) :
    inner ℝ x y = ∫ s in (0 : ℝ)..1, (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re := by
  have h1 := norm_add_sq_real x y
  have hx := integral_sq_coverRep38_one x
  have hy := integral_sq_coverRep38_one y
  have hxy := integral_sq_coverRep38_one (x + y)
  have hint : IntervalIntegrable
      (fun s : ℝ => (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re) volume 0 1 :=
    ⟨(integrable_conj_mul x y).1.re, (integrable_conj_mul x y).2.re⟩
  have hsum : ∫ s in (0 : ℝ)..1, ‖coverRep38 (x + y) s‖ ^ 2 =
      ∫ s in (0 : ℝ)..1, (‖coverRep38 x s‖ ^ 2 +
        2 * (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re + ‖coverRep38 y s‖ ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_add_ae x y] with s hs _
    rw [hs, sq_norm_add_pt]
  have hsplit : ∫ s in (0 : ℝ)..1, (‖coverRep38 x s‖ ^ 2 +
        2 * (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re + ‖coverRep38 y s‖ ^ 2) =
      (∫ s in (0 : ℝ)..1, ‖coverRep38 x s‖ ^ 2) +
        2 * (∫ s in (0 : ℝ)..1, (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re) +
        (∫ s in (0 : ℝ)..1, ‖coverRep38 y s‖ ^ 2) := by
    rw [intervalIntegral.integral_add
      ((intervalIntegrable_coverRep38_sq_one x).add (hint.const_mul 2))
      (intervalIntegrable_coverRep38_sq_one y),
      intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one x) (hint.const_mul 2),
      intervalIntegral.integral_const_mul]
  rw [hxy] at hsum
  rw [hsplit, hx, hy] at hsum
  linarith


/-- Multiplication by `I` as a bounded real-linear map on `PhysicalL2`. -/
def Jmul : PhysicalL2 →L[ℝ] PhysicalL2 :=
  (Complex.I • ContinuousLinearMap.id ℂ PhysicalL2).restrictScalars ℝ

theorem Jmul_apply (x : PhysicalL2) : Jmul x = Complex.I • x := rfl

/-- The real symplectic bracket `B x y = Re ⟨I x, y⟩ = Im ⟨x, y⟩` on `PhysicalL2`. -/
def Bform : PhysicalL2 →L[ℝ] PhysicalL2 →L[ℝ] ℝ := (innerSL ℝ).comp Jmul

theorem Bform_apply (x y : PhysicalL2) : Bform x y = inner ℝ (Complex.I • x) y := rfl

theorem Bform_integral (x y : PhysicalL2) :
    Bform x y = ∫ s in (0 : ℝ)..1, (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).im := by
  rw [Bform_apply, real_inner_eq_integral]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [coverRep38_smul_ae Complex.I x] with s hs _
  rw [hs]
  simp only [map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  ring

theorem pairKernelExt38_snd_of_realSymmetric (K : PairKernelCont38) (hK : realSymmetric K)
    (s : ℝ) : pairKernelExt38 K s 1 = star (pairKernelExt38 K s 0) :=
  hK _

theorem class_rep_ae (K : PairKernelCont38) :
    ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      coverRep38 (pairKernelL2Class38 K).1 s = pairKernelExt38 K s 0 := by
  rw [restrict_Ioc_eq_restrict_Icc]
  filter_upwards [pairKernelL2Class38_rep K] with s hs using hs.1

theorem wedge_integral_eq (K K' : PairKernelCont38) (hK : realSymmetric K)
    (hK' : realSymmetric K') :
    (∫ s in (0 : ℝ)..1, kernelWedge38 K K' s) =
      -2 * Complex.I *
        ((Bform (pairKernelL2Class38 K).1 (pairKernelL2Class38 K').1 : ℝ) : ℂ) := by
  rw [Bform_integral, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [class_rep_ae K, class_rep_ae K'] with s h1 h2
  rw [h1, h2]
  unfold kernelWedge38
  rw [pairKernelExt38_snd_of_realSymmetric K hK s, pairKernelExt38_snd_of_realSymmetric K' hK' s]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  · simp only [Complex.star_def, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring

theorem pairing_eq (K : PairKernelCont38) (hK : realSymmetric K) (W : PhysicalL2) :
    integralPairCLM38 K t1 (realSlice W) =
      ((2 * inner ℝ (star (pairKernelL2Class38 K).1) W : ℝ) : ℂ) := by
  rw [integralPairCLM38_apply, real_inner_eq_integral]
  unfold pairIntegral38
  simp only [t1]
  rw [Complex.ofReal_mul, ← intervalIntegral.integral_ofReal, Complex.ofReal_ofNat,
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [class_rep_ae K,
    ae_restrict_of_ae (potRepSnd38_realSlice_ae W),
    ae_restrict_of_ae (coverRep38_star_ae (pairKernelL2Class38 K).1)] with s h1 h2 h3
  rw [h3, h1, h2, pairKernelExt38_snd_of_realSymmetric K hK s]
  change pairKernelExt38 K s 0 * coverRep38 W s +
      star (pairKernelExt38 K s 0) * star (coverRep38 W s) = _
  apply Complex.ext
  · simp only [Complex.star_def, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.conj_conj]
    ring
  · simp only [Complex.star_def, Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.conj_conj]
    ring


/-- Anti-symmetric pair kernels: second component is minus the conjugate of the first. -/
def antiSym (w : PairKernelCont38) : Prop := ∀ t : Time, w t 1 = -star (w t 0)

theorem terminalSeed_anti (u : PhysicalL2) (x : ℝ) :
    terminalSeed (realSlice u) (x : ℂ) 1 = -star (terminalSeed (realSlice u) (x : ℂ) 0) := by
  have h00 : star (monodromyPair (realSlice u) (x : ℂ) 0 0) =
      monodromyPair (realSlice u) (x : ℂ) 1 1 := monodromyPair_real_entry_star38 u x 0 0
  have h01 : star (monodromyPair (realSlice u) (x : ℂ) 0 1) =
      monodromyPair (realSlice u) (x : ℂ) 1 0 := monodromyPair_real_entry_star38 u x 0 1
  have h10 : star (monodromyPair (realSlice u) (x : ℂ) 1 0) =
      monodromyPair (realSlice u) (x : ℂ) 0 1 := monodromyPair_real_entry_star38 u x 1 0
  have h11 : star (monodromyPair (realSlice u) (x : ℂ) 1 1) =
      monodromyPair (realSlice u) (x : ℂ) 0 0 := monodromyPair_real_entry_star38 u x 1 1
  simp only [terminalSeed, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    star_add, h01, h11]
  ring

theorem state_antiSym (u : PhysicalL2) (x : ℝ) (a : PairVec38) (ha : a 1 = -star (a 0)) :
    antiSym (state (realSlice u) (x : ℂ) a) := by
  intro t
  have hs0 : star (a 0) = -a 1 := by rw [ha]; simp
  have hs1 : star (a 1) = -a 0 := by rw [ha]; simp
  have h00 : star (fundPair (realSlice u) (x : ℂ) t 0 0) = fundPair (realSlice u) (x : ℂ) t 1 1 :=
    fundPair_real_entry_star38 u x t 0 0
  have h01 : star (fundPair (realSlice u) (x : ℂ) t 0 1) = fundPair (realSlice u) (x : ℂ) t 1 0 :=
    fundPair_real_entry_star38 u x t 0 1
  simp only [state_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [star_add, star_mul, star_mul, h00, h01, hs0, hs1]
  ring

theorem mixedSquare_realSym_antiSym (g k : PairKernelCont38) (hg : realSymmetric g)
    (hk : antiSym k) : antiSym (mixedSquare g k) := by
  intro t
  have e0 : mixedSquare g k t 0 = g t 1 * k t 1 := rfl
  have e1 : mixedSquare g k t 1 = g t 0 * k t 0 := rfl
  rw [e1, e0, hg t, hk t]
  simp only [star_mul, star_neg, star_star]
  ring

theorem antiSym_add (g k : PairKernelCont38) (hg : antiSym g) (hk : antiSym k) :
    antiSym (g + k) := by
  intro t
  change g t 1 + k t 1 = -star (g t 0 + k t 0)
  rw [star_add, hg t, hk t]
  ring

theorem realSymmetric_I_smul (g : PairKernelCont38) (hg : antiSym g) :
    realSymmetric (Complex.I • g) := by
  intro t
  change Complex.I * g t 1 = star (Complex.I * g t 0)
  rw [star_mul, hg t]
  simp only [Complex.star_def, Complex.conj_I]
  ring

theorem mixedSquare_realSym (g k : PairKernelCont38) (hg : realSymmetric g)
    (hk : realSymmetric k) : realSymmetric (mixedSquare g k) := by
  intro t
  have e0 : mixedSquare g k t 0 = g t 1 * k t 1 := rfl
  have e1 : mixedSquare g k t 1 = g t 0 * k t 0 := rfl
  rw [e1, e0, hg t, hk t, star_mul]
  simp only [star_star]
  ring

theorem terminalState_antiSym (u : PhysicalL2) (n : ℤ) : antiSym (terminalState u n) :=
  state_antiSym u (gkMu u n) _ (terminalSeed_anti u (gkMu u n))

theorem mixedKernel_realSymmetric (u v : PhysicalL2) (n : ℤ) (minus : Bool) :
    realSymmetric (mixedKernel u v n minus) := by
  cases minus
  · exact mixedSquare_realSym _ _ (dirState_real_symmetry u n) (dirState_real_symmetry v n)
  · exact realSymmetric_I_smul _ (antiSym_add _ _
      (mixedSquare_realSym_antiSym _ _ (dirState_real_symmetry u n) (terminalState_antiSym v n))
      (mixedSquare_realSym_antiSym _ _ (dirState_real_symmetry v n) (terminalState_antiSym u n)))

end
end NlsGge.Atomic.G1100Support
