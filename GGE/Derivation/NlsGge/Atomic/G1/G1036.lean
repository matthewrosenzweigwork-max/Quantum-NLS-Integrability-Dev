/- G1-036 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1036.lean,
   namespace NlsGge.GKDefinitionDesign. Head: Pro rounds 7-8 section 23 (G1_036), verbatim.
   Sections inline, byte-identically: HOST01 (proof development), S1b (h198), S2a (h203, h213), S2b/S5/S0 (h250),
   SUP01/SUP02 (h151), S6 + FINAL (h260). -/
import Mathlib
import NlsGge.Analysis.H1Fourier
import NlsGge.Analysis.NaturalCover
import NlsGge.GK38.PairPotential
import NlsGge.GK38.GradEigenDefs
import NlsGge.GK38.PairVolterraDefs
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.GradFundamentalODE
import NlsGge.GK38.GradFundamentalDet
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Atomic.G1.G1062
import NlsGge.Schur.FourierMultiplier
import NlsGge.Atomic.G1.G1035

section Inline_HOST01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 HOST01 (proof development, AUTHOR; not reviewed). Definitions only; no theorem.
   Bodies of fourierRepresentative (DEFINITIONS/G1.lean.md:155), wkbAlpha (:159), wkbPhase (:162) and swappedPotential (:171)
   are byte-identical to the Pro round-4 design text (lexical repair: spectral parameter lambda -> l, a Lean keyword).
   wkbRemainder and wkbSymmetricRemainder: the Pro round 8 section 23 heads. The fundamental matrix is evaluated by
   Set.IccExtend zero_le_one (fundPair phi z) t, as in the corrected G1-067 solution (NlsGge/Atomic/G1/G1067.lean);
   no other change. The earlier defect (fundPair applied to t : Real) is removed by this extension. -/
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

def fourierRepresentative (u : PhysicalL2) (t : ℝ) : ℂ :=
  -∑' n : ℤ, reflectedFourierL2 u n *
    Complex.exp (-2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(t : ℂ))

def wkbAlpha (N : ℕ) (l : ℂ) (φ : PotPair) (t : ℝ) : ℂ :=
  -Complex.I * fourierRepresentative (wkbPartial N l φ) t

def wkbPhase (N : ℕ) (l : ℂ) (φ : PotPair) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I*l*(t : ℂ) + Complex.I *
    ∫ s in (0 : ℝ)..t, potRepFst38 φ s * wkbAlpha N l φ s)

def swappedPotential (φ : PotPair) : PotPair := (-φ.2,-φ.1)

def wkbRemainder (N : ℕ) (z : ℂ) (φ : PotPair)
    (t : ℝ) : PairVec38 :=
  (2 * Complex.I * z)^N •
    ((Set.IccExtend zero_le_one (fundPair φ z) t) *ᵥ
        ![1, wkbAlpha N z φ 0] -
      wkbPhase N z φ t • ![1, wkbAlpha N z φ t])

def wkbSymmetricRemainder (N : ℕ) (z : ℂ) (φ : PotPair)
    (t : ℝ) : PairVec38 :=
  ![wkbRemainder N (-z) (swappedPotential φ) t 1,
    wkbRemainder N (-z) (swappedPotential φ) t 0]

end
end NlsGge.GKDefinitionDesign
end Inline_HOST01

section Inline_S1B01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
namespace NlsGge.GKDefinitionDesign
noncomputable section
/- G1-036 S1b (proof development, AUTHOR; not reviewed). Supporting module, not the theorem G1_036.
   Statements S1b of G1036_STOP.md (proof development): identification of the Fourier representative
   `fourierRepresentative` (inlined byte-identically from proof development G1036_HOST01.lean.txt in the SELFTEST)
   with the continuous H1 representative `physicalH1Continuous` pointwise on R, and with the L2 class
   `coverRep38` almost everywhere. Totalization: the summability hypothesis of `physicalH1Continuous` is
   derived from `physicalSobolev 1 u` before use. -/

open NlsGge.Analysis

local instance g36_s1b_isProb : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-! ### S1b.0: the physical Sobolev condition transfers to the ordinary Fourier coefficients -/

theorem g36_s1b_physical_sobolev_summable (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    SobolevSquareSummable 1 (physicalFourier u) := by
  have hu' : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖reflectedFourierL2 u n‖ ^ 2) := hu
  have h := (Equiv.summable_iff (Equiv.neg ℤ)).2 hu'
  have hjap : ∀ n : ℤ, japaneseBracket (-n) = japaneseBracket n := by
    intro n
    unfold japaneseBracket
    simp
  unfold SobolevSquareSummable
  refine h.congr (fun n => ?_)
  simp only [Function.comp_apply, Equiv.neg_apply, reflectedFourierL2_apply, reflectedFourier,
    neg_neg, norm_neg, hjap]

/-! ### S1b.1: pointwise identity on R -/

theorem g36_s1b_fourierRepresentative_eq (u : PhysicalL2) (hu : physicalSobolev 1 u) (t : ℝ) :
    fourierRepresentative u t =
      physicalH1Continuous u (g36_s1b_physical_sobolev_summable u hu) (t : PhysicalCircle) := by
  have hS := g36_s1b_physical_sobolev_summable u hu
  have hterm : ∀ n : ℤ, reflectedFourierL2 u n *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))
      = -(physicalFourier u (-n) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (t : ℂ))) := by
    intro n
    have harg : (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (t : ℂ) := by
      push_cast
      ring
    rw [reflectedFourierL2_apply, harg]
    unfold reflectedFourier
    ring
  have hrhs : ∀ p : ℤ,
      (physicalFourier u p • fourier (T := (1 : ℝ)) p) (t : PhysicalCircle)
      = physicalFourier u p * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (t : ℂ)) := by
    intro p
    rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_coe_apply]
    simp
  unfold physicalH1Continuous
  rw [← ContinuousMap.tsum_apply (physicalH1_continuous_fourier_summable u hS)]
  unfold fourierRepresentative
  simp only [hterm, hrhs]
  rw [tsum_neg, neg_neg]
  exact Equiv.tsum_eq (Equiv.neg ℤ) (fun p : ℤ =>
    physicalFourier u p * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (t : ℂ)))

/-! ### S1b.2: almost everywhere transfer from the physical circle to R -/

theorem g36_s1b_ae_real_phys {p : PhysicalCircle → Prop} (h : ∀ᵐ y ∂spatialMeasure, p y) :
    ∀ᵐ t : ℝ, p (t : PhysicalCircle) := by
  have h1 : ∀ᵐ x ∂NlsGge.Schur.spectralHaar, p (NlsGge.Analysis.naturalPhysicalCover x) :=
    NlsGge.Analysis.naturalPhysicalCover_preserving.quasiMeasurePreserving.ae h
  have h2 := ae_real_of_ae_spectral h1
  simpa only [NlsGge.Analysis.naturalPhysicalCover_coe] using h2

/-! ### S1b.3: almost everywhere identification with the L2 class -/

theorem g36_s1b_fourierRepresentative_ae (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    ∀ᵐ t : ℝ, fourierRepresentative u t = coverRep38 u t := by
  have hS := g36_s1b_physical_sobolev_summable u hu
  have hc : ∀ᵐ y ∂spatialMeasure,
      (physicalH1Continuous u hS : PhysicalCircle → ℂ) y = (u : PhysicalCircle → ℂ) y := by
    have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
      (physicalH1Continuous u hS)
    rw [physicalH1Continuous_toLp] at h
    exact h.symm
  have h1 : ∀ᵐ t : ℝ, (physicalH1Continuous u hS : PhysicalCircle → ℂ) (t : PhysicalCircle)
      = (u : PhysicalCircle → ℂ) (t : PhysicalCircle) :=
    g36_s1b_ae_real_phys (p := fun y => (physicalH1Continuous u hS : PhysicalCircle → ℂ) y
      = (u : PhysicalCircle → ℂ) y) hc
  filter_upwards [h1, coverRep38_ae_phys u] with t ht1 ht2
  rw [g36_s1b_fourierRepresentative_eq u hu t, ht2]
  exact ht1

end
end NlsGge.GKDefinitionDesign
end Inline_S1B01

section Inline_S2A01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S2a.1 (proof development, AUTHOR; not reviewed). Supporting module, not the theorem G1_036.
   Partial-sum fundamental theorem of calculus for the Fourier representative `fourierRepresentative`
   (inlined byte-identically from proof development G1036_HOST01.lean.txt in the SELFTEST), together with the
   termwise FTC for the period-one modes `fourier p` and the pointwise absolutely convergent series.
   Totalization: summability of the Fourier coefficients and of the derivative coefficients is proved
   from `physicalSobolev 1 u` before any identity uses it. -/

namespace NlsGge.GKDefinitionDesign
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators

/-! ### S2a.1.0 the derivative coefficients are l2 (totalization before identities) -/

theorem g36_s2a_weak_memℓp (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
      reflectedFourierL2 u n) 2 := by
  have hu' : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖reflectedFourierL2 u n‖ ^ 2) := hu
  have hb : Summable (fun n : ℤ => (4 * Real.pi ^ 2) *
      (Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖reflectedFourierL2 u n‖ ^ 2)) :=
    hu'.mul_left _
  have hJ : ∀ n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) = 1 + (n : ℝ) ^ 2 := by
    intro n
    unfold japaneseBracket
    show Real.sqrt (1 + (n : ℝ) ^ 2) ^ (2 * (1 : ℝ)) = 1 + (n : ℝ) ^ 2
    rw [show (2 : ℝ) * 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt (by positivity)]
  have hc : ∀ n : ℤ, ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ ^ 2 =
      4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    intro n
    rw [show (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) =
        ((-2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
  rw [norm_mul, mul_pow, hc n, hJ n]
  have h1 : (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by linarith
  have h2 : 0 ≤ ‖reflectedFourierL2 u n‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2, Real.pi_pos]

theorem g36_s2a_weakDerivative_coeff (u : PhysicalL2) (hu : physicalSobolev 1 u) (n : ℤ) :
    reflectedFourierL2 (weakDerivative u) n =
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * reflectedFourierL2 u n := by
  have hm := g36_s2a_weak_memℓp u hu
  unfold weakDerivative
  rw [dif_pos hm]
  simp

/-- The physical coefficients of the weak derivative are `2πi p` times those of `u`. -/
theorem g36_s2a_weak_fourier (u : PhysicalL2) (hu : physicalSobolev 1 u) (p : ℤ) :
    physicalFourier (weakDerivative u) p =
      2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * physicalFourier u p := by
  have h1 : reflectedFourier (weakDerivative u) (-p) = -physicalFourier (weakDerivative u) p := by
    unfold reflectedFourier
    rw [neg_neg]
  have h2 : reflectedFourier (weakDerivative u) (-p) =
      (-2 * (Real.pi : ℂ) * Complex.I * ((-p : ℤ) : ℂ)) * reflectedFourier u (-p) := by
    rw [← reflectedFourierL2_apply, g36_s2a_weakDerivative_coeff u hu, reflectedFourierL2_apply]
  have h3 : reflectedFourier u (-p) = -physicalFourier u p := by
    unfold reflectedFourier
    rw [neg_neg]
  rw [h2, h3] at h1
  push_cast at h1
  linear_combination h1

/-! ### S2a.1.1 termwise fundamental theorem of calculus for the period-one modes -/

theorem g36_s2a_hasDerivAt_fourier (p : ℤ) (s : ℝ) :
    HasDerivAt (fun x : ℝ => fourier (T := (1 : ℝ)) p (x : PhysicalCircle))
      (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) *
        fourier (T := (1 : ℝ)) p (s : PhysicalCircle)) s := by
  have hfun : (fun x : ℝ => fourier (T := (1 : ℝ)) p (x : PhysicalCircle)) =
      fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (x : ℂ)) := by
    funext x
    rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  have hs : fourier (T := (1 : ℝ)) p (s : PhysicalCircle) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (s : ℂ)) := by
    rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  have hc : HasDerivAt (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * z))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * (s : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * 1)) (s : ℂ) :=
    ((hasDerivAt_id' (s : ℂ)).const_mul (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ))).cexp
  rw [hfun, hs]
  convert hc.comp_ofReal using 1
  ring

theorem g36_s2a_continuous_fourier (p : ℤ) :
    Continuous (fun s : ℝ => fourier (T := (1 : ℝ)) p (s : PhysicalCircle)) :=
  continuous_iff_continuousAt.2 fun s => (g36_s2a_hasDerivAt_fourier p s).continuousAt

theorem g36_s2a_integral_fourier (p : ℤ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, 2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) *
        fourier (T := (1 : ℝ)) p (s : PhysicalCircle)
      = fourier (T := (1 : ℝ)) p (t : PhysicalCircle) -
        fourier (T := (1 : ℝ)) p ((0 : ℝ) : PhysicalCircle) := by
  have hint : IntervalIntegrable (fun s : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) *
      fourier (T := (1 : ℝ)) p (s : PhysicalCircle)) volume 0 t :=
    (continuous_const.mul (g36_s2a_continuous_fourier p)).intervalIntegrable 0 t
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => fourier (T := (1 : ℝ)) p (x : PhysicalCircle))
    (fun s _ => g36_s2a_hasDerivAt_fourier p s) hint

/-- Finite partial sums: termwise integration of the coefficient series for a general
coefficient `c` and derivative coefficient `d = 2πi p c`. -/
theorem g36_s2a_partial_ftc (c d : ℤ → ℂ)
    (hd : ∀ p : ℤ, d p = 2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * c p)
    (I : Finset ℤ) (t : ℝ) :
    ∑ p ∈ I, (c p * fourier (T := (1 : ℝ)) p (t : PhysicalCircle) -
        c p * fourier (T := (1 : ℝ)) p ((0 : ℝ) : PhysicalCircle))
      = ∫ s in (0 : ℝ)..t, ∑ p ∈ I, d p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle) := by
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    have hterm : ∫ s in (0 : ℝ)..t, d p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle)
        = c p * ∫ s in (0 : ℝ)..t, 2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) *
            fourier (T := (1 : ℝ)) p (s : PhysicalCircle) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext s
      rw [hd p]
      ring
    rw [hterm, g36_s2a_integral_fourier p t, mul_sub]
  · intro p _
    exact (continuous_const.mul (g36_s2a_continuous_fourier p)).intervalIntegrable 0 t

/-! ### S2a.1.2 pointwise absolutely convergent series for the Fourier representative -/

theorem g36_s2a_hasSum_representative (u : PhysicalL2) (hu : physicalSobolev 1 u) (t : ℝ) :
    HasSum (fun p : ℤ => physicalFourier u p * fourier (T := (1 : ℝ)) p (t : PhysicalCircle))
      (fourierRepresentative u t) := by
  have hS := g36_s1b_physical_sobolev_summable u hu
  have hA : Summable (fun p : ℤ => ‖physicalFourier u p‖) :=
    NlsGge.Analysis.physicalH1_absolute_fourier_summable u hS
  have hn : ∀ p : ℤ, ‖fourier (T := (1 : ℝ)) p (t : PhysicalCircle)‖ = 1 :=
    fun p => Circle.norm_coe _
  have hsum : Summable (fun p : ℤ =>
      physicalFourier u p * fourier (T := (1 : ℝ)) p (t : PhysicalCircle)) := by
    refine Summable.of_norm_bounded hA (fun p => ?_)
    rw [norm_mul, hn p, mul_one]
  have heq : NlsGge.Analysis.physicalH1Continuous u hS (t : PhysicalCircle) =
      ∑' p : ℤ, physicalFourier u p * fourier (T := (1 : ℝ)) p (t : PhysicalCircle) := by
    unfold NlsGge.Analysis.physicalH1Continuous
    rw [← ContinuousMap.tsum_apply (NlsGge.Analysis.physicalH1_continuous_fourier_summable u hS)]
    refine tsum_congr (fun p => ?_)
    simp [ContinuousMap.smul_apply, smul_eq_mul]
  rw [g36_s1b_fourierRepresentative_eq u hu t, heq]
  exact hsum.hasSum

end
end NlsGge.GKDefinitionDesign
end Inline_S2A01

section Inline_S2A02v2
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S2a.2 (proof development repair of proof development G1036_S2A02.lean.txt; AUTHOR, not reviewed).
   Only the insert-case block changed: generic `g36_s2a_coverRep38_sum_gen_ae` added; the
   Fourier-monomial lemma is now its specialisation. Statements of all other declarations are unchanged. -/
namespace NlsGge.GKDefinitionDesign
noncomputable section
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.GK38
open scoped BigOperators

/-! ### S2a.2.0 the period-one Fourier monomials as representatives -/

theorem g36_s2a_fourierLp_ae (p : ℤ) :
    ∀ᵐ s : ℝ, coverRep38 (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) s
      = fourier (T := (1 : ℝ)) p (s : PhysicalCircle) := by
  have h1 := coverRep38_ae_phys (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2)
  have h2 : ∀ᵐ x ∂spatialMeasure,
      (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) x = fourier (T := (1 : ℝ)) p x :=
    coeFn_fourierLp (T := (1 : ℝ)) 2 p
  have h3 : ∀ᵐ s : ℝ, (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) (s : PhysicalCircle)
      = fourier (T := (1 : ℝ)) p (s : PhysicalCircle) :=
    g36_s1b_ae_real_phys (p := fun x : PhysicalCircle =>
      (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) x = fourier (T := (1 : ℝ)) p x) h2
  filter_upwards [h1, h3] with s hs1 hs3
  exact hs1.trans hs3

/-- Finite sums of representatives for an arbitrary family in `PhysicalL2` (proof development repair:
generic form, so that the sum is typed `PhysicalL2` throughout and `Finset.sum_insert` matches). -/
theorem g36_s2a_coverRep38_sum_gen_ae (I : Finset ℤ) (g : ℤ → PhysicalL2) (f : ℤ → ℝ → ℂ)
    (hg : ∀ p : ℤ, ∀ᵐ s : ℝ, coverRep38 (g p) s = f p s) :
    ∀ᵐ s : ℝ, coverRep38 (∑ p ∈ I, g p) s = ∑ p ∈ I, f p s := by
  induction I using Finset.induction_on with
  | empty =>
    have h0 := coverRep38_smul_ae (0 : ℂ) (0 : PhysicalL2)
    simp only [zero_smul, zero_mul] at h0
    simp only [Finset.sum_empty]
    exact h0
  | @insert a I ha ih =>
    filter_upwards [coverRep38_add_ae (g a) (∑ p ∈ I, g p), hg a, ih] with s h1 h2 h3
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h2, h3]

/-- A finite Fourier sum of monomials has as representative the pointwise finite sum. -/
theorem g36_s2a_coverRep38_sum_ae (I : Finset ℤ) (d : ℤ → ℂ) :
    ∀ᵐ s : ℝ, coverRep38 ((∑ p ∈ I, d p • (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2)) : PhysicalL2) s
      = ∑ p ∈ I, d p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle) :=
  g36_s2a_coverRep38_sum_gen_ae I (fun p => d p • (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2))
    (fun p s => d p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle))
    (fun p => by
      show ∀ᵐ s : ℝ, coverRep38 (d p • (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2)) s
        = d p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle)
      filter_upwards [coverRep38_smul_ae (d p) (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2),
        g36_s2a_fourierLp_ae p] with s h1 h2
      exact h1.trans (by rw [h2]))

/-! ### S2a.2.1 the L2 bound for the integral over [0,t], t in [0,1] -/

theorem g36_s2a_integral_bound (K : PhysicalL2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖∫ s in (0 : ℝ)..t, coverRep38 K s‖ ≤ ‖K‖ := by
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 1 :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ht0, ht1⟩))
  have hK2 : IntervalIntegrable (fun s => ‖coverRep38 K s‖ ^ 2) volume 0 t :=
    (intervalIntegrable_coverRep38_sq_one K).mono_set hsub
  have hmono : ∫ s in (0 : ℝ)..t, ‖coverRep38 K s‖ ^ 2 ≤
      ∫ s in (0 : ℝ)..1, ‖coverRep38 K s‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl ht0 ht1
      (Filter.Eventually.of_forall fun s => sq_nonneg (‖coverRep38 K s‖))
      (intervalIntegrable_coverRep38_sq_one K)
  have hm : AEStronglyMeasurable (coverRep38 K) volume :=
    (stronglyMeasurable_coverRep38 K).aestronglyMeasurable
  have hCS := integral_norm_le_sqrt_mul ht0 hm hK2
  have hsq : Real.sqrt (t - 0) ≤ 1 := by
    rw [sub_zero, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  calc ‖∫ s in (0 : ℝ)..t, coverRep38 K s‖
      ≤ ∫ s in (0 : ℝ)..t, ‖coverRep38 K s‖ := intervalIntegral.norm_integral_le_integral_norm ht0
    _ ≤ Real.sqrt (t - 0) * Real.sqrt (∫ s in (0 : ℝ)..t, ‖coverRep38 K s‖ ^ 2) := hCS
    _ ≤ 1 * Real.sqrt (∫ s in (0 : ℝ)..1, ‖coverRep38 K s‖ ^ 2) :=
        mul_le_mul hsq (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _) zero_le_one
    _ = ‖K‖ := by
        rw [one_mul, integral_sq_coverRep38_one K, Real.sqrt_sq (norm_nonneg K)]

/-! ### S2a.2.2 the fundamental theorem of calculus on [0,1] (statement S2a) -/

theorem g36_s2a_fourierRepresentative_ftc (u : PhysicalL2) (hu : physicalSobolev 1 u) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    fourierRepresentative u t - fourierRepresentative u 0
      = ∫ s in (0 : ℝ)..t, coverRep38 (weakDerivative u) s := by
  obtain ⟨ht0, ht1⟩ := ht
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 1 :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ht0, ht1⟩))
  -- L2 convergence of the Fourier partial sums of the weak derivative
  have hH : Tendsto (fun I : Finset ℤ => ∑ p ∈ I, physicalFourier (weakDerivative u) p •
      (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2)) atTop (𝓝 (weakDerivative u)) :=
    hasSum_fourier_series_L2 (T := (1 : ℝ)) (weakDerivative u)
  have hHn : Tendsto (fun I : Finset ℤ => ‖((∑ p ∈ I, physicalFourier (weakDerivative u) p •
      (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) : PhysicalL2)) - weakDerivative u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hH
  -- integrability on [0,t] of the partial sums and of the derivative representative
  have hW : IntervalIntegrable (fun s => coverRep38 (weakDerivative u) s) volume 0 t :=
    (intervalIntegrable_coverRep38_one (weakDerivative u)).mono_set hsub
  have hTc : ∀ I : Finset ℤ, IntervalIntegrable (fun s : ℝ => ∑ p ∈ I,
      physicalFourier (weakDerivative u) p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle))
      volume 0 t := fun I =>
    (continuous_finsetSum I (fun p _ =>
      continuous_const.mul (g36_s2a_continuous_fourier p))).intervalIntegrable 0 t
  -- almost everywhere identification of the remainder on the real line
  have hae : ∀ I : Finset ℤ, ∀ᵐ s : ℝ,
      coverRep38 (((∑ p ∈ I, physicalFourier (weakDerivative u) p •
        (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) : PhysicalL2)) - weakDerivative u) s =
      (∑ p ∈ I, physicalFourier (weakDerivative u) p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle))
        - coverRep38 (weakDerivative u) s := by
    intro I
    filter_upwards [coverRep38_sub_ae ((∑ p ∈ I, physicalFourier (weakDerivative u) p •
        (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) : PhysicalL2)) (weakDerivative u),
      g36_s2a_coverRep38_sum_ae I (physicalFourier (weakDerivative u))] with s h1 h2
    rw [h1, h2]
  -- the integral error is bounded by the L2 error of the partial sums
  have hbound : ∀ I : Finset ℤ,
      ‖(∫ s in (0 : ℝ)..t, ∑ p ∈ I, physicalFourier (weakDerivative u) p *
          fourier (T := (1 : ℝ)) p (s : PhysicalCircle))
        - ∫ s in (0 : ℝ)..t, coverRep38 (weakDerivative u) s‖
      ≤ ‖((∑ p ∈ I, physicalFourier (weakDerivative u) p •
          (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) : PhysicalL2)) - weakDerivative u‖ := by
    intro I
    have hsplit : (∫ s in (0 : ℝ)..t, ∑ p ∈ I, physicalFourier (weakDerivative u) p *
          fourier (T := (1 : ℝ)) p (s : PhysicalCircle))
        - ∫ s in (0 : ℝ)..t, coverRep38 (weakDerivative u) s
        = ∫ s in (0 : ℝ)..t, coverRep38 (((∑ p ∈ I, physicalFourier (weakDerivative u) p •
            (fourierLp (T := (1 : ℝ)) 2 p : PhysicalL2) : PhysicalL2)) - weakDerivative u) s := by
      rw [← intervalIntegral.integral_sub (hTc I) hW]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hae I] with s hs
      exact fun _ => hs.symm
    rw [hsplit]
    exact g36_s2a_integral_bound _ ht0 ht1
  -- the integrals of the partial sums converge to the integral of the representative
  have hTint : Tendsto (fun I : Finset ℤ => ∫ s in (0 : ℝ)..t, ∑ p ∈ I,
      physicalFourier (weakDerivative u) p * fourier (T := (1 : ℝ)) p (s : PhysicalCircle))
      atTop (𝓝 (∫ s in (0 : ℝ)..t, coverRep38 (weakDerivative u) s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun I => norm_nonneg _) hbound hHn
  -- the left side converges by absolute summability of the coefficients of u
  have hLeft : Tendsto (fun I : Finset ℤ => ∑ p ∈ I,
      (physicalFourier u p * fourier (T := (1 : ℝ)) p (t : PhysicalCircle) -
        physicalFourier u p * fourier (T := (1 : ℝ)) p ((0 : ℝ) : PhysicalCircle)))
      atTop (𝓝 (fourierRepresentative u t - fourierRepresentative u 0)) :=
    ((g36_s2a_hasSum_representative u hu t).sub
      (g36_s2a_hasSum_representative u hu 0))
  have hconv := hLeft.congr (fun I => g36_s2a_partial_ftc (physicalFourier u)
    (physicalFourier (weakDerivative u)) (fun p => g36_s2a_weak_fourier u hu p) I t)
  exact tendsto_nhds_unique hconv hTint

end
end NlsGge.GKDefinitionDesign
end Inline_S2A02v2

section Inline_G1036_S2B01a
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S2b (proof development, AUTHOR; not reviewed). Supporting module, not the theorem G1_036.
   Defect integral identity (MAP02 step S2b) for the fixed-period variation of constants:
     D(t) := M(t) *ᵥ v0 - ϕ(t) • ![1, α t],  M = Set.IccExtend zero_le_one (fundPair φ z),
     v0 = ![1, α 0],  α = wkbAlpha N z φ,  ϕ = wkbPhase N z φ,
   and, for t in [0,1] and each component i,
     D(t) i = ∫ s in 0..t, ((zsCoeffPot38 φ z s *ᵥ D s) + (I * ϕ s) • ![0, Res s]) i,
   with Res = coverRep38 (wkbResidual N z φ) (the L2 class of the residual, identified a.e. with
   F' - 2izF + p1 F^2 - p2 in g36_s2b_residual_ae; F = fourierRepresentative of wkbPartial).
   Hypotheses (true statements; realized in production: hq and hp are conjuncts of G1_035, and
   hP is the H1 membership from NlsGge/Atomic/G1/G1035.lean lemmas g35_H1_sum/g35_H1_smul/g35_H1_wkbR;
   to be discharged in the final assembly, not assumed as targets):
     hP : physicalSobolev 1 (wkbPartial N z φ),
     hp : productInL2 P P,   hq : productInL2 φ.1 (physicalProduct P P).
   Totalization: integrability, absolute continuity (complex FTC g36_s2b_ftc, proved from Mathlib's
   real-normed `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`, no re/im split needed)
   and the a.e. derivatives are proved before the FTC is applied. -/

namespace NlsGge.GKDefinitionDesign
noncomputable section
open MeasureTheory Filter Topology Set
open NlsGge.Pilot NlsGge.GK38
open scoped BigOperators Matrix

/-! ### S2b.0 the defect D and its initial value -/

/-- The defect `D(t) = M(t) v0 - Y(t)`; `wkbRemainder N z φ t = (2 I z)^N • g36_s2b_D N z φ t`. -/
def g36_s2b_D (N : ℕ) (z : ℂ) (φ : PotPair) (t : ℝ) : PairVec38 :=
  Matrix.mulVec (Set.IccExtend zero_le_one (fundPair φ z) t) ![1, wkbAlpha N z φ 0] -
    wkbPhase N z φ t • ![1, wkbAlpha N z φ t]

theorem g36_s2b_M_eq (φ : PotPair) (z : ℂ) (r : ℝ) :
    Set.IccExtend zero_le_one (fundPair φ z) r = ext38 (fundContP φ z) r := rfl

theorem g36_s2b_D_zero (N : ℕ) (z : ℂ) (φ : PotPair) : g36_s2b_D N z φ 0 = 0 := by
  have h1 : Set.IccExtend zero_le_one (fundPair φ z) 0 = 1 := by
    rw [Set.IccExtend_of_mem _ _ (Set.left_mem_Icc.2 zero_le_one)]
    exact fundPair_zero φ z
  have h2 : wkbPhase N z φ 0 = 1 := by
    unfold wkbPhase
    simp
  unfold g36_s2b_D
  rw [h1, h2]
  simp

theorem g36_s2b_D0_eq (N : ℕ) (z : ℂ) (φ : PotPair) :
    (fun r => g36_s2b_D N z φ r 0) = fun r => ext38 (fundContP φ z) r 0 0 +
      ext38 (fundContP φ z) r 0 1 * wkbAlpha N z φ 0 - wkbPhase N z φ r := by
  funext r
  simp [g36_s2b_D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g36_s2b_M_eq] <;> ring

theorem g36_s2b_D1_eq (N : ℕ) (z : ℂ) (φ : PotPair) :
    (fun r => g36_s2b_D N z φ r 1) = fun r => ext38 (fundContP φ z) r 1 0 +
      ext38 (fundContP φ z) r 1 1 * wkbAlpha N z φ 0 - wkbPhase N z φ r * wkbAlpha N z φ r := by
  funext r
  simp [g36_s2b_D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g36_s2b_M_eq] <;> ring

theorem g36_s2b_B_entries (φ : PotPair) (z : ℂ) (s : ℝ) :
    zsCoeffPot38 φ z s 0 0 = -(Complex.I * z) ∧
    zsCoeffPot38 φ z s 0 1 = Complex.I * potRepFst38 φ s ∧
    zsCoeffPot38 φ z s 1 0 = -(Complex.I * potRepSnd38 φ s) ∧
    zsCoeffPot38 φ z s 1 1 = Complex.I * z := by
  rw [zsCoeffPot38_eq]
  simp [potCoeff38]

/-! ### S2b.1 complex absolutely continuous FTC on [0,1] -/

theorem g36_s2b_ftc (f g : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hd : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt f (g x) x) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    f t = f 0 + ∫ s in (0 : ℝ)..t, g s := by
  have hac : AbsolutelyContinuousOnInterval (fun x => f x - ∫ r in (0 : ℝ)..x, g r) 0 1 :=
    hf.sub (ac_primitive38 hg Set.left_mem_uIcc)
  have hz : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun x => f x - ∫ r in (0 : ℝ)..x, g r) 0 x := by
    filter_upwards [hd, hg.ae_hasDerivAt_integral, Measure.ae_ne (volume : Measure ℝ) 0,
      Measure.ae_ne (volume : Measure ℝ) 1] with x hx1 hx2 h0 h1 hxu
    have hxI : x ∈ Ioo (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one] at hxu
      exact ⟨lt_of_le_of_ne hxu.1 (Ne.symm h0), lt_of_le_of_ne hxu.2 h1⟩
    have h := (hx1 hxI).sub (hx2 hxu 0 Set.left_mem_uIcc)
    rw [sub_self] at h
    exact h
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hz
  have hA := hC 0 Set.left_mem_uIcc
  have hB := hC t (by rw [uIcc_of_le zero_le_one]; exact ht)
  have hA' : f 0 - ∫ r in (0 : ℝ)..0, g r = C := hA
  have hB' : f t - ∫ r in (0 : ℝ)..t, g r = C := hB
  simp only [intervalIntegral.integral_same, sub_zero] at hA'
  linear_combination hB' - hA'

/-! ### S2b.2 continuity, absolute continuity and a.e. derivatives of the phase and of F -/

theorem g36_s2b_F_continuous (P : PhysicalL2) (hP : physicalSobolev 1 P) :
    Continuous (fourierRepresentative P) := by
  have hS := g36_s1b_physical_sobolev_summable P hP
  have hfun : fourierRepresentative P =
      fun t : ℝ => NlsGge.Analysis.physicalH1Continuous P hS (t : PhysicalCircle) :=
    funext fun t => g36_s1b_fourierRepresentative_eq P hP t
  rw [hfun]
  exact (NlsGge.Analysis.physicalH1Continuous P hS).continuous.comp continuous_quotient_mk'

theorem g36_s2b_alpha_continuous (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) : Continuous (wkbAlpha N z φ) := by
  unfold wkbAlpha
  exact continuous_const.mul (g36_s2b_F_continuous _ hP)

theorem g36_s2b_phase_integrable (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    IntervalIntegrable (fun s => potRepFst38 φ s * wkbAlpha N z φ s) volume 0 1 :=
  (intervalIntegrable_coverRep38_one φ.1).mul_continuousOn
    (g36_s2b_alpha_continuous N z φ hP).continuousOn

theorem g36_s2b_phase_ac (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    AbsolutelyContinuousOnInterval (wkbPhase N z φ) 0 1 := by
  have hJ := ac_primitive38 (g36_s2b_phase_integrable N z φ hP) Set.left_mem_uIcc
  have hcd : ContDiff ℝ 1 (fun x : ℝ => -Complex.I * z * (x : ℂ)) := by
    have h : ContDiff ℝ 1 (fun x : ℝ => (-Complex.I * z) * Complex.ofRealCLM x) :=
      contDiff_const.mul Complex.ofRealCLM.contDiff
    simpa using h
  have hL : AbsolutelyContinuousOnInterval (fun x : ℝ => -Complex.I * z * (x : ℂ)) 0 1 :=
    ContDiffOn.absolutelyContinuousOnInterval hcd.contDiffOn
  have hG : AbsolutelyContinuousOnInterval (fun x : ℝ => -Complex.I * z * (x : ℂ) +
      Complex.I * ∫ s in (0 : ℝ)..x, potRepFst38 φ s * wkbAlpha N z φ s) 0 1 :=
    (hL.add (hJ.const_smul Complex.I)).congr (fun x _ => by simp [smul_eq_mul])
  obtain ⟨R, hR⟩ := hG.exists_bound
  have hLip : LipschitzOnWith (Real.toNNReal (Real.exp R)) Complex.exp
      (Metric.closedBall 0 R) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℂ) (f := Complex.exp)
      (s := Metric.closedBall 0 R) (fun x _ => Complex.differentiableAt_exp) (fun x hx => ?_)
      (convex_closedBall 0 R)
    rw [Complex.deriv_exp, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (Real.exp_pos R).le, Complex.norm_exp]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm x).trans (by simpa using hx))
  have hmaps : MapsTo (fun x : ℝ => -Complex.I * z * (x : ℂ) +
      Complex.I * ∫ s in (0 : ℝ)..x, potRepFst38 φ s * wkbAlpha N z φ s)
      (uIcc (0 : ℝ) 1) (Metric.closedBall 0 R) := fun x hx => by
    rw [mem_closedBall_zero_iff]
    exact hR x hx
  exact hLip.comp_absolutelyContinuousOnInterval hmaps hG

theorem g36_s2b_phase_deriv_ae (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt (wkbPhase N z φ)
      (wkbPhase N z φ x * (-Complex.I * z + Complex.I * (potRepFst38 φ x * wkbAlpha N z φ x))) x := by
  filter_upwards [(g36_s2b_phase_integrable N z φ hP).ae_hasDerivAt_integral] with x hx hxI
  have hxu : x ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self hxI
  have hJx := hx hxu 0 Set.left_mem_uIcc
  have hL : HasDerivAt (fun y : ℝ => -Complex.I * z * (y : ℂ)) (-Complex.I * z) x := by
    simpa using ((hasDerivAt_id' x).ofReal_comp).const_mul (-Complex.I * z)
  exact (hL.add (hJx.const_mul Complex.I)).cexp

theorem g36_s2b_F_deriv_ae (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt (fourierRepresentative (wkbPartial N z φ))
      (coverRep38 (weakDerivative (wkbPartial N z φ)) x) x := by
  filter_upwards [(intervalIntegrable_coverRep38_one
    (weakDerivative (wkbPartial N z φ))).ae_hasDerivAt_integral] with x hx hxI
  have hxu : x ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self hxI
  have h := (hx hxu 0 Set.left_mem_uIcc).const_add (fourierRepresentative (wkbPartial N z φ) 0)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
  have hf := g36_s2a_fourierRepresentative_ftc (wkbPartial N z φ) hP y ⟨hy.1.le, hy.2.le⟩
  linear_combination hf

theorem g36_s2b_F_ac (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    AbsolutelyContinuousOnInterval (fourierRepresentative (wkbPartial N z φ)) 0 1 := by
  have h := (absolutelyContinuousOnInterval_const38
      (fourierRepresentative (wkbPartial N z φ) 0) 0 1).add
    (ac_primitive38 (intervalIntegrable_coverRep38_one (weakDerivative (wkbPartial N z φ)))
      Set.left_mem_uIcc)
  refine h.congr (fun y hy => ?_)
  have hy' : y ∈ Icc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one] at hy; exact hy
  have hf := g36_s2a_fourierRepresentative_ftc (wkbPartial N z φ) hP y hy'
  show fourierRepresentative (wkbPartial N z φ) 0 +
      ∫ s in (0 : ℝ)..y, coverRep38 (weakDerivative (wkbPartial N z φ)) s =
    fourierRepresentative (wkbPartial N z φ) y
  linear_combination -hf

theorem g36_s2b_alpha_ac (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    AbsolutelyContinuousOnInterval (wkbAlpha N z φ) 0 1 := by
  refine ((g36_s2b_F_ac N z φ hP).const_smul (-Complex.I)).congr (fun x _ => ?_)
  simp [wkbAlpha]

/-! ### S2b.3 the residual identity a.e. and the product lemma -/

theorem g36_s2b_coverRep_mul_ae (u v : PhysicalL2) (huv : productInL2 u v) :
    ∀ᵐ s : ℝ, coverRep38 (physicalProduct u v) s = coverRep38 u s * coverRep38 v s := by
  have h1 : ∀ᵐ x ∂spatialMeasure, (physicalProduct u v : PhysicalCircle → ℂ) x = u x * v x :=
    physicalProduct_ae u v huv
  have h2 := g36_s1b_ae_real_phys (p := fun x : PhysicalCircle =>
    (physicalProduct u v : PhysicalCircle → ℂ) x = u x * v x) h1
  filter_upwards [h2, coverRep38_ae_phys (physicalProduct u v), coverRep38_ae_phys u,
    coverRep38_ae_phys v] with s hs1 hs2 hs3 hs4
  rw [hs2, hs3, hs4]
  exact hs1

theorem g36_s2b_residual_ae (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ))
    (hp : productInL2 (wkbPartial N z φ) (wkbPartial N z φ))
    (hq : productInL2 φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ))) :
    ∀ᵐ s : ℝ, coverRep38 (wkbResidual N z φ) s =
      coverRep38 (weakDerivative (wkbPartial N z φ)) s
        - (2 * Complex.I * z) * fourierRepresentative (wkbPartial N z φ) s
        + potRepFst38 φ s * fourierRepresentative (wkbPartial N z φ) s ^ 2
        - potRepSnd38 φ s := by
  have hF := g36_s1b_fourierRepresentative_ae (wkbPartial N z φ) hP
  unfold wkbResidual
  unfold potRepFst38 potRepSnd38
  filter_upwards [coverRep38_sub_ae (weakDerivative (wkbPartial N z φ) -
      (2 * Complex.I * z) • wkbPartial N z φ + physicalProduct φ.1
        (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ))) φ.2,
    coverRep38_add_ae (weakDerivative (wkbPartial N z φ) - (2 * Complex.I * z) • wkbPartial N z φ)
      (physicalProduct φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ))),
    coverRep38_sub_ae (weakDerivative (wkbPartial N z φ)) ((2 * Complex.I * z) • wkbPartial N z φ),
    coverRep38_smul_ae (2 * Complex.I * z) (wkbPartial N z φ),
    g36_s2b_coverRep_mul_ae φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ)) hq,
    g36_s2b_coverRep_mul_ae (wkbPartial N z φ) (wkbPartial N z φ) hp, hF] with s h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_S2B01a

section Inline_G1036_S2B01b
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S2b part b (proof development, AUTHOR; not reviewed): components, a.e. ODE and defect identity. Continues G1036_S2B01a (same namespace; closes it). -/
namespace NlsGge.GKDefinitionDesign
noncomputable section
open MeasureTheory Filter Topology Set
open NlsGge.Pilot NlsGge.GK38
open scoped BigOperators Matrix

/-! ### S2b.4 integrability and absolute continuity of the components -/

theorem g36_s2b_B_integrable (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun s => zsCoeffPot38 φ z s i j) volume 0 1 :=
  (intervalIntegrable_zsCoeffPot38_entry φ z i j).mono_set (by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num))

theorem g36_s2b_D0_ac (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    AbsolutelyContinuousOnInterval (fun r => g36_s2b_D N z φ r 0) 0 1 := by
  have h := ((ac_fundContP_entry38 φ z 0 0).add
    ((ac_fundContP_entry38 φ z 0 1).const_smul (wkbAlpha N z φ 0))).sub
    (g36_s2b_phase_ac N z φ hP)
  refine h.congr (fun r _ => ?_)
  simp [g36_s2b_D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g36_s2b_M_eq, smul_eq_mul] <;> ring

theorem g36_s2b_D1_ac (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    AbsolutelyContinuousOnInterval (fun r => g36_s2b_D N z φ r 1) 0 1 := by
  have h := ((ac_fundContP_entry38 φ z 1 0).add
    ((ac_fundContP_entry38 φ z 1 1).const_smul (wkbAlpha N z φ 0))).sub
    ((g36_s2b_phase_ac N z φ hP).smul (g36_s2b_alpha_ac N z φ hP))
  refine h.congr (fun r _ => ?_)
  simp [g36_s2b_D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g36_s2b_M_eq, smul_eq_mul] <;> ring

theorem g36_s2b_int_comp0 (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    IntervalIntegrable (fun s => (Matrix.mulVec (zsCoeffPot38 φ z s) (g36_s2b_D N z φ s) +
      (Complex.I * wkbPhase N z φ s) • ![0, coverRep38 (wkbResidual N z φ) s]) 0) volume 0 1 := by
  have hc0 : ContinuousOn (fun s => g36_s2b_D N z φ s 0) (uIcc 0 1) :=
    (g36_s2b_D0_ac N z φ hP).continuousOn
  have hc1 : ContinuousOn (fun s => g36_s2b_D N z φ s 1) (uIcc 0 1) :=
    (g36_s2b_D1_ac N z φ hP).continuousOn
  have hfun : (fun s => (Matrix.mulVec (zsCoeffPot38 φ z s) (g36_s2b_D N z φ s) +
      (Complex.I * wkbPhase N z φ s) • ![0, coverRep38 (wkbResidual N z φ) s]) 0) =
      fun s => zsCoeffPot38 φ z s 0 0 * g36_s2b_D N z φ s 0 +
        zsCoeffPot38 φ z s 0 1 * g36_s2b_D N z φ s 1 := by
    funext s
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hfun]
  exact ((g36_s2b_B_integrable φ z 0 0).mul_continuousOn hc0).add
    ((g36_s2b_B_integrable φ z 0 1).mul_continuousOn hc1)

theorem g36_s2b_int_comp1 (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    IntervalIntegrable (fun s => (Matrix.mulVec (zsCoeffPot38 φ z s) (g36_s2b_D N z φ s) +
      (Complex.I * wkbPhase N z φ s) • ![0, coverRep38 (wkbResidual N z φ) s]) 1) volume 0 1 := by
  have hc0 : ContinuousOn (fun s => g36_s2b_D N z φ s 0) (uIcc 0 1) :=
    (g36_s2b_D0_ac N z φ hP).continuousOn
  have hc1 : ContinuousOn (fun s => g36_s2b_D N z φ s 1) (uIcc 0 1) :=
    (g36_s2b_D1_ac N z φ hP).continuousOn
  have hcϕ : ContinuousOn (fun s => Complex.I * wkbPhase N z φ s) (uIcc 0 1) :=
    continuousOn_const.mul (g36_s2b_phase_ac N z φ hP).continuousOn
  have hfun : (fun s => (Matrix.mulVec (zsCoeffPot38 φ z s) (g36_s2b_D N z φ s) +
      (Complex.I * wkbPhase N z φ s) • ![0, coverRep38 (wkbResidual N z φ) s]) 1) =
      fun s => zsCoeffPot38 φ z s 1 0 * g36_s2b_D N z φ s 0 +
        zsCoeffPot38 φ z s 1 1 * g36_s2b_D N z φ s 1 +
        (Complex.I * wkbPhase N z φ s) * coverRep38 (wkbResidual N z φ) s := by
    funext s
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hfun]
  exact (((g36_s2b_B_integrable φ z 1 0).mul_continuousOn hc0).add
    ((g36_s2b_B_integrable φ z 1 1).mul_continuousOn hc1)).add
    ((intervalIntegrable_coverRep38_one (wkbResidual N z φ)).continuousOn_mul hcϕ)

/-! ### S2b.5 the almost everywhere ODE for the two components -/

theorem g36_s2b_D0_deriv_ae (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt (fun r => g36_s2b_D N z φ r 0)
      ((Matrix.mulVec (zsCoeffPot38 φ z x) (g36_s2b_D N z φ x) +
        (Complex.I * wkbPhase N z φ x) • ![0, coverRep38 (wkbResidual N z φ) x]) 0) x := by
  filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z 0 0,
    ae_hasDerivAt_fundContP_entry38 φ z 0 1, g36_s2b_phase_deriv_ae N z φ hP] with x h00 h01 hϕ hxI
  have hxc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hxI
  rw [g36_s2b_D0_eq]
  have hd := ((h00 hxc).add ((h01 hxc).mul_const (wkbAlpha N z φ 0))).sub (hϕ hxI)
  refine hd.congr_deriv ?_
  obtain ⟨b00, b01, b10, b11⟩ := g36_s2b_B_entries φ z x
  simp [g36_s2b_D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    g36_s2b_M_eq, b00, b01, b10, b11, smul_eq_mul]
  ring

theorem g36_s2b_D1_deriv_ae (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ))
    (hp : productInL2 (wkbPartial N z φ) (wkbPartial N z φ))
    (hq : productInL2 φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ))) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 → HasDerivAt (fun r => g36_s2b_D N z φ r 1)
      ((Matrix.mulVec (zsCoeffPot38 φ z x) (g36_s2b_D N z φ x) +
        (Complex.I * wkbPhase N z φ x) • ![0, coverRep38 (wkbResidual N z φ) x]) 1) x := by
  filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z 1 0,
    ae_hasDerivAt_fundContP_entry38 φ z 1 1, g36_s2b_phase_deriv_ae N z φ hP,
    g36_s2b_F_deriv_ae N z φ hP, g36_s2b_residual_ae N z φ hP hp hq] with
    x h10 h11 hϕ hF hres hxI
  have hxc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hxI
  rw [g36_s2b_D1_eq]
  have hα : HasDerivAt (wkbAlpha N z φ)
      (-Complex.I * coverRep38 (weakDerivative (wkbPartial N z φ)) x) x := by
    unfold wkbAlpha
    exact (hF hxI).const_mul (-Complex.I)
  have hd := ((h10 hxc).add ((h11 hxc).mul_const (wkbAlpha N z φ 0))).sub ((hϕ hxI).mul hα)
  refine hd.congr_deriv ?_
  obtain ⟨b00, b01, b10, b11⟩ := g36_s2b_B_entries φ z x
  simp only [wkbAlpha] at hd ⊢
  simp [g36_s2b_D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    g36_s2b_M_eq, b00, b01, b10, b11, smul_eq_mul, wkbAlpha]
  linear_combination (-Complex.I * wkbPhase N z φ x) * hres +
    (-Complex.I * wkbPhase N z φ x * potRepFst38 φ x * fourierRepresentative (wkbPartial N z φ) x ^ 2) *
      Complex.I_sq

/-! ### S2b.6 the defect integral identity (components 0 and 1) -/

theorem g36_s2b_defect_0 (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ))
    (hp : productInL2 (wkbPartial N z φ) (wkbPartial N z φ))
    (hq : productInL2 φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ)))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    g36_s2b_D N z φ t 0 = ∫ s in (0 : ℝ)..t, (Matrix.mulVec (zsCoeffPot38 φ z s)
      (g36_s2b_D N z φ s) + (Complex.I * wkbPhase N z φ s) •
        ![0, coverRep38 (wkbResidual N z φ) s]) 0 := by
  have key := g36_s2b_ftc (fun r => g36_s2b_D N z φ r 0) _ (g36_s2b_D0_ac N z φ hP)
    (g36_s2b_int_comp0 N z φ hP) (g36_s2b_D0_deriv_ae N z φ hP) t ht
  simpa [g36_s2b_D_zero] using key

theorem g36_s2b_defect_1 (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ))
    (hp : productInL2 (wkbPartial N z φ) (wkbPartial N z φ))
    (hq : productInL2 φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ)))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    g36_s2b_D N z φ t 1 = ∫ s in (0 : ℝ)..t, (Matrix.mulVec (zsCoeffPot38 φ z s)
      (g36_s2b_D N z φ s) + (Complex.I * wkbPhase N z φ s) •
        ![0, coverRep38 (wkbResidual N z φ) s]) 1 := by
  have key := g36_s2b_ftc (fun r => g36_s2b_D N z φ r 1) _ (g36_s2b_D1_ac N z φ hP)
    (g36_s2b_int_comp1 N z φ hP) (g36_s2b_D1_deriv_ae N z φ hP hp hq) t ht
  simpa [g36_s2b_D_zero] using key

/-- S2b (defect integral identity), both components, for `t` in the unit interval. -/
theorem g36_s2b_defect_integral (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ))
    (hp : productInL2 (wkbPartial N z φ) (wkbPartial N z φ))
    (hq : productInL2 φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ)))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    g36_s2b_D N z φ t i = ∫ s in (0 : ℝ)..t, (Matrix.mulVec (zsCoeffPot38 φ z s)
      (g36_s2b_D N z φ s) + (Complex.I * wkbPhase N z φ s) •
        ![0, coverRep38 (wkbResidual N z φ) s]) i := by
  fin_cases i
  · exact g36_s2b_defect_0 N z φ hP hp hq t ht
  · exact g36_s2b_defect_1 N z φ hP hp hq t ht

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_S2B01b

section Inline_G1036_SUP01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 SUP01 (proof development, AUTHOR; not reviewed). Supporting statements S0, S1, S4 of G1036_MAP02.md.
   Target: NlsGge/Atomic/G1/G1036.lean is NOT claimed. No theorem G1_036 here.
   Definitions (fourierRepresentative, wkbAlpha, wkbPhase, swappedPotential, wkbRemainder,
   wkbSymmetricRemainder) come from proof development G1036_HOST01.lean.txt, inlined byte-identically in the selftest.
   Landed inputs used: fundPair_zero, norm_fundPair_entry_le, potPrim38_le_one, integral_coverRep38_le_one,
   intervalIntegrable_norm_coverRep38_one (GK38), reciprocalBracketL2, japaneseBracket_h1_weight (NlsGge.Analysis),
   weightedL2Element, weightedCoordinates_norm_sq, weightedL2Element_norm_sq (NlsGge.Pilot). -/
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Analysis
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-! ### S0: initial values -/

theorem g36_fundPair_zero_extend (φ : PotPair) (z : ℂ) :
    Set.IccExtend zero_le_one (fundPair φ z) 0 = 1 := by
  rw [Set.IccExtend_left]
  exact fundPair_zero φ z

theorem g36_wkbRemainder_zero (N : ℕ) (z : ℂ) (φ : PotPair) :
    wkbRemainder N z φ 0 = 0 := by
  have hphase : wkbPhase N z φ 0 = 1 := by
    unfold wkbPhase
    simp
  unfold wkbRemainder
  rw [g36_fundPair_zero_extend, hphase, Matrix.one_mulVec, one_smul, sub_self, smul_zero]

theorem g36_wkbSymmetricRemainder_zero (N : ℕ) (z : ℂ) (φ : PotPair) :
    wkbSymmetricRemainder N z φ 0 = 0 := by
  ext i
  fin_cases i <;> simp [wkbSymmetricRemainder, g36_wkbRemainder_zero]

/-! ### S1: uniform sup bound of the H1 Fourier representative -/

/-- Hölder in l2 for a Sobolev-weighted sequence: the l1 norm is bounded by the H1 norm times
`‖reciprocalBracketL2‖`. -/
theorem g36_abs_tsum_le_sobolev1 (x : ℤ → ℂ)
    (hx : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖x n‖ ^ 2)) :
    Summable (fun n : ℤ => ‖x n‖) ∧
      ∑' n : ℤ, ‖x n‖ ≤ ‖reciprocalBracketL2‖ *
        Real.sqrt (∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖x n‖ ^ 2) := by
  set w : ℤ → ℝ := fun n => Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) with hw_def
  have hw : ∀ n, 0 ≤ w n := fun n => (Real.rpow_pos_of_pos (japaneseBracket_pos n) _).le
  set H : lp (fun _ : ℤ => ℂ) 2 := weightedL2Element w hw x hx with hH_def
  set G : lp (fun _ : ℤ => ℂ) 2 := reciprocalBracketL2 with hG_def
  have hper : ∀ n : ℤ, ‖H n‖ * ‖G n‖ = ‖x n‖ := by
    intro n
    have hf : ‖H n‖ ^ 2 = w n * ‖x n‖ ^ 2 := weightedCoordinates_norm_sq w hw x n
    have hg : ‖G n‖ ^ 2 = 1 / (1 + (n : ℝ) ^ 2) := by
      change ‖weightedCoordinates (fun q : ℤ => 1 / (1 + (q : ℝ) ^ 2)) (fun _ => (1 : ℂ)) n‖ ^ 2 = _
      rw [weightedCoordinates_norm_sq _ (fun q => by positivity)]
      simp
    have hwn : w n = 1 + (n : ℝ) ^ 2 := japaneseBracket_h1_weight n
    apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).1
    have hden : 1 + (n : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    rw [mul_pow, hf, hg, hwn]
    field_simp
  have hsum : Summable (fun n : ℤ => ‖x n‖) := by
    have h := (lp.tsum_mul_le_mul_norm (by rw [Real.holderConjugate_iff]; norm_num) H G).1
    exact h.congr (fun n => hper n)
  have hle : ∑' n : ℤ, ‖x n‖ ≤ ‖H‖ * ‖G‖ := by
    have e : ∑' n : ℤ, ‖x n‖ = ∑' n : ℤ, ‖H n‖ * ‖G n‖ := tsum_congr (fun n => (hper n).symm)
    rw [e]
    exact lp.tsum_mul_le_mul_norm' (by rw [Real.holderConjugate_iff]; norm_num) H G
  have hHnorm : ‖H‖ = Real.sqrt (∑' n : ℤ, w n * ‖x n‖ ^ 2) := by
    rw [← weightedL2Element_norm_sq w hw x hx, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨hsum, ?_⟩
  calc ∑' n : ℤ, ‖x n‖ ≤ ‖H‖ * ‖G‖ := hle
    _ = ‖G‖ * Real.sqrt (∑' n : ℤ, w n * ‖x n‖ ^ 2) := by rw [hHnorm, mul_comm]

/-- Uniform sup bound: `|fourierRepresentative u t| ≤ ‖reciprocalBracketL2‖ · ‖u‖_{H1}` for all real `t`. -/
theorem g36_fourierRepresentative_norm_le (u : PhysicalL2) (hu : physicalSobolev 1 u) (t : ℝ) :
    ‖fourierRepresentative u t‖ ≤ ‖reciprocalBracketL2‖ * physicalSobolevNorm 1 u := by
  have hu' : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖reflectedFourierL2 u n‖ ^ 2) := hu
  obtain ⟨hs, hb⟩ := g36_abs_tsum_le_sobolev1 (fun n : ℤ => reflectedFourierL2 u n) hu'
  have he : ∀ n : ℤ,
      ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖ = 1 := by
    intro n
    rw [Complex.norm_exp]
    simp
  have hterm : ∀ n : ℤ,
      ‖reflectedFourierL2 u n * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖
        = ‖reflectedFourierL2 u n‖ := by
    intro n
    rw [norm_mul, he n, mul_one]
  have hs2 := hs.congr (fun n => (hterm n).symm)
  unfold fourierRepresentative
  rw [norm_neg]
  calc ‖∑' n : ℤ, reflectedFourierL2 u n *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖
      ≤ ∑' n : ℤ, ‖reflectedFourierL2 u n *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))‖ :=
        norm_tsum_le_tsum_norm hs2
    _ = ∑' n : ℤ, ‖reflectedFourierL2 u n‖ := tsum_congr hterm
    _ ≤ ‖reciprocalBracketL2‖ * Real.sqrt (∑' n : ℤ,
          Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖reflectedFourierL2 u n‖ ^ 2) := hb
    _ = ‖reciprocalBracketL2‖ * physicalSobolevNorm 1 u := rfl

/-! ### S4: uniform strip bound and the L1 size of the potentials -/

theorem g36_fundPair_strip_entry_le (φ : PotPair) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    ‖Set.IccExtend zero_le_one (fundPair φ z) t i j‖ ≤ Real.exp (|z.im| + potL1Norm38 φ) := by
  rw [Set.IccExtend_of_mem (h := zero_le_one) (f := fundPair φ z) (hx := ht)]
  have hbound := norm_fundPair_entry_le φ z ⟨t, ht⟩ i j
  have hcoe : ((⟨t, ht⟩ : Set.Icc (0 : ℝ) 1) : ℝ) = t := rfl
  rw [hcoe] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have h1 : |z.im| * t ≤ |z.im| := mul_le_of_le_one_right (abs_nonneg _) ht.2
  have h2 : potPrim38 φ t ≤ potL1Norm38 φ := potPrim38_le_one φ ht
  linarith

theorem g36_potL1Norm38_le (φ : PotPair) : potL1Norm38 φ ≤ ‖φ.1‖ + ‖φ.2‖ := by
  unfold potL1Norm38
  show ∫ t in (0 : ℝ)..1, (‖coverRep38 φ.1 t‖ + ‖coverRep38 φ.2 t‖) ≤ ‖φ.1‖ + ‖φ.2‖
  rw [intervalIntegral.integral_add (intervalIntegrable_norm_coverRep38_one φ.1)
    (intervalIntegrable_norm_coverRep38_one φ.2)]
  exact add_le_add (integral_coverRep38_le_one φ.1) (integral_coverRep38_le_one φ.2)

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_SUP01

section Inline_G1036_SUP02
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 SUP02 (proof development, AUTHOR; not reviewed). Supporting statements S5a and S3a of G1036_MAP02.md.
   S5a: pointwise variation-of-constants algebra for a traceless 2x2 coefficient: if M' = B M and D' = B D + g at s,
        then (adj(M) D)' = adj(M) g at s (componentwise). No absolute continuity is used here.
   S3a: L1 size of the residual's pointwise class is bounded by its L2 norm.
   The complex-valued absolutely continuous FTC needed to integrate S5a is NOT here (Mathlib's
   AbsolutelyContinuousOnInterval.integral_deriv_eq_sub is real-valued only). -/
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Analysis
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-! ### S5a: pointwise derivative of the adjugate-transformed vector -/

theorem g36_adj_mulVec_hasDerivAt (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (D g : ℝ → PairVec38)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) (htr : B 0 0 + B 1 1 = 0)
    (hM : ∀ i j : Fin 2, HasDerivAt (fun r => M r i j) ((B * M s) i j) s)
    (hD : ∀ i : Fin 2, HasDerivAt (fun r => D r i) ((B *ᵥ D s) i + g s i) s) :
    HasDerivAt (fun r => (Matrix.adjugate (M r) *ᵥ D r) 0)
        ((Matrix.adjugate (M s) *ᵥ g s) 0) s ∧
      HasDerivAt (fun r => (Matrix.adjugate (M r) *ᵥ D r) 1)
        ((Matrix.adjugate (M s) *ᵥ g s) 1) s := by
  constructor
  · have h := ((hM 1 1).mul (hD 0)).sub ((hM 0 1).mul (hD 1))
    have hfun : (fun r => (Matrix.adjugate (M r) *ᵥ D r) 0) =
        fun r => M r 1 1 * D r 0 - M r 0 1 * D r 1 := by
      funext r
      simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [hfun]
    convert h using 1
    simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    linear_combination (-(M s 1 1 * D s 0 - M s 0 1 * D s 1)) * htr
  · have h := ((hM 1 0).mul (hD 0)).neg.add ((hM 0 0).mul (hD 1))
    have hfun : (fun r => (Matrix.adjugate (M r) *ᵥ D r) 1) =
        fun r => -(M r 1 0 * D r 0) + M r 0 0 * D r 1 := by
      funext r
      simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [hfun]
    convert h using 1
    simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    linear_combination (-(M s 0 0 * D s 1 - M s 1 0 * D s 0)) * htr

/-! ### S3a: L1 size of the pointwise residual class -/

theorem g36_residual_integral_le (N : ℕ) (l : ℂ) (φ : PotPair) :
    ∫ s in (0 : ℝ)..1, ‖coverRep38 (wkbResidual N l φ) s‖ ≤ ‖wkbResidual N l φ‖ :=
  integral_coverRep38_le_one (wkbResidual N l φ)

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_SUP02

section Inline_G1036_S5_01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S5 and S3-composed (proof development, AUTHOR; not reviewed). Supporting module, not G1_036.
   S5 (MAP02): variation of constants with det M = 1, general form. Hypotheses: traceless B,
   M' = B M and D' = B D + g a.e. on (0,1), det M = 1 on [0,1], D(0) = 0, entries of M and D absolutely
   continuous on [0,1], g integrable. Conclusion (t in [0,1]):
     D t = M t *ᵥ (fun j => ∫ s in 0..t, (adjugate (M s) *ᵥ g s) j).
   The complex AC FTC is g36_s2b_ftc (S2b.1); the pointwise derivative of adj(M) D is
   g36_adj_mulVec_hasDerivAt (proof development SUP02, inlined byte-identically by the selftest).
   No Gronwall, no uniformity in z is used here.
   S3-composed: the L1 norm of the weighted residual is bounded through the G1_035 bound
   (hypothesis hG is exactly the fourth conjunct of G1_035; it is realized by production G1_035). -/

namespace NlsGge.GKDefinitionDesign
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators Matrix

/-! ### S5.1 the adjugate-transformed defect is absolutely continuous -/

theorem g36_s5_Q_ac (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (D : ℝ → PairVec38)
    (hMac : ∀ i j, AbsolutelyContinuousOnInterval (fun r => M r i j) 0 1)
    (hDac : ∀ i, AbsolutelyContinuousOnInterval (fun r => D r i) 0 1) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun r => (Matrix.adjugate (M r) *ᵥ D r) i) 0 1 := by
  fin_cases i
  · refine (((hMac 1 1).smul (hDac 0)).sub ((hMac 0 1).smul (hDac 1))).congr (fun r _ => ?_)
    simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · refine ((((hMac 1 0).smul (hDac 0)).neg).add ((hMac 0 0).smul (hDac 1))).congr
      (fun r _ => ?_)
    simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-! ### S5.2 integrability of the adjugate times g -/

theorem g36_s5_adj_integrable (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (g : ℝ → PairVec38)
    (hMac : ∀ i j, AbsolutelyContinuousOnInterval (fun r => M r i j) 0 1)
    (hgint : ∀ j, IntervalIntegrable (fun s => g s j) volume 0 1) (i : Fin 2) :
    IntervalIntegrable (fun s => (Matrix.adjugate (M s) *ᵥ g s) i) volume 0 1 := by
  have hc : ∀ a b : Fin 2, ContinuousOn (fun s => M s a b) (uIcc 0 1) :=
    fun a b => (hMac a b).continuousOn
  fin_cases i
  · show IntervalIntegrable (fun s => (Matrix.adjugate (M s) *ᵥ g s) 0) volume 0 1
    have hfun : (fun s => (Matrix.adjugate (M s) *ᵥ g s) 0) =
        fun s => M s 1 1 * g s 0 - M s 0 1 * g s 1 := by
      funext s
      simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [hfun]
    exact ((hgint 0).continuousOn_mul (hc 1 1)).sub ((hgint 1).continuousOn_mul (hc 0 1))
  · show IntervalIntegrable (fun s => (Matrix.adjugate (M s) *ᵥ g s) 1) volume 0 1
    have hfun : (fun s => (Matrix.adjugate (M s) *ᵥ g s) 1) =
        fun s => -(M s 1 0 * g s 0) + M s 0 0 * g s 1 := by
      funext s
      simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [hfun]
    exact (((hgint 0).continuousOn_mul (hc 1 0)).neg).add ((hgint 1).continuousOn_mul (hc 0 0))

/-! ### S5.3 variation of constants -/

theorem g36_s5_variation_of_constants (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (D g : ℝ → PairVec38)
    (htr : ∀ s, B s 0 0 + B s 1 1 = 0)
    (hdet : ∀ s ∈ Icc (0 : ℝ) 1, (M s).det = 1)
    (hMac : ∀ i j, AbsolutelyContinuousOnInterval (fun r => M r i j) 0 1)
    (hMode : ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ i j,
      HasDerivAt (fun r => M r i j) ((B s * M s) i j) s)
    (hDac : ∀ i, AbsolutelyContinuousOnInterval (fun r => D r i) 0 1)
    (hDode : ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ i,
      HasDerivAt (fun r => D r i) ((B s *ᵥ D s) i + g s i) s)
    (hD0 : D 0 = 0)
    (hgint : ∀ j, IntervalIntegrable (fun s => g s j) volume 0 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    D t = Matrix.mulVec (M t) (fun j => ∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) j) := by
  have hQ : ∀ i : Fin 2, (Matrix.adjugate (M t) *ᵥ D t) i =
      ∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) i := by
    intro i
    have hd : ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
        HasDerivAt (fun r => (Matrix.adjugate (M r) *ᵥ D r) i)
          ((Matrix.adjugate (M s) *ᵥ g s) i) s := by
      filter_upwards [hMode, hDode] with s hM hD hsI
      have h := g36_adj_mulVec_hasDerivAt M D g (B s) s (htr s)
        (fun a b => hM hsI a b) (fun a => hD hsI a)
      fin_cases i
      · exact h.1
      · exact h.2
    have key : (Matrix.adjugate (M t) *ᵥ D t) i = (Matrix.adjugate (M 0) *ᵥ D 0) i +
        ∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) i :=
      g36_s2b_ftc (fun r => (Matrix.adjugate (M r) *ᵥ D r) i)
        (fun s => (Matrix.adjugate (M s) *ᵥ g s) i) (g36_s5_Q_ac M D hMac hDac i)
        (g36_s5_adj_integrable M g hMac hgint i) hd t ht
    have h0 : (Matrix.adjugate (M 0) *ᵥ D 0) i = 0 := by
      rw [hD0, Matrix.mulVec_zero]
      rfl
    rw [h0, zero_add] at key
    exact key
  have hdt : M t * Matrix.adjugate (M t) = 1 := by
    rw [Matrix.mul_adjugate, hdet t ht, one_smul]
  calc D t = (M t * Matrix.adjugate (M t)) *ᵥ D t := by rw [hdt, Matrix.one_mulVec]
    _ = Matrix.mulVec (M t) (Matrix.adjugate (M t) *ᵥ D t) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = Matrix.mulVec (M t) (fun j => ∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) j) := by
        congr 1
        funext j
        exact hQ j

/-! ### S3-composed: the L1 bound of the weighted residual through the G1_035 bound -/

theorem g36_s3_source_L1 (N : ℕ) (l : ℂ) (φ : PotPair) (C X : ℝ) (p : ℕ) (hl : 1 ≤ ‖l‖)
    (hG : ‖wkbResidual N l φ‖ ≤ C * (1 + X) ^ p / ‖l‖ ^ N) :
    ∫ s in (0 : ℝ)..1, ‖(2 * Complex.I * l) ^ N • coverRep38 (wkbResidual N l φ) s‖ ≤
      2 ^ N * (C * (1 + X) ^ p) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hn : ∀ s : ℝ, ‖(2 * Complex.I * l) ^ N • coverRep38 (wkbResidual N l φ) s‖ =
      (2 * ‖l‖) ^ N * ‖coverRep38 (wkbResidual N l φ) s‖ := by
    intro s
    rw [norm_smul, norm_pow, show ‖2 * Complex.I * l‖ = 2 * ‖l‖ by simp [norm_mul]]
  simp only [hn]
  rw [intervalIntegral.integral_const_mul]
  have hint := integral_coverRep38_le_one (wkbResidual N l φ)
  calc (2 * ‖l‖) ^ N * ∫ s in (0 : ℝ)..1, ‖coverRep38 (wkbResidual N l φ) s‖
      ≤ (2 * ‖l‖) ^ N * ‖wkbResidual N l φ‖ := mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ (2 * ‖l‖) ^ N * (C * (1 + X) ^ p / ‖l‖ ^ N) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ = 2 ^ N * (C * (1 + X) ^ p) := by
        rw [mul_pow]
        field_simp

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_S5_01

section Inline_G1036_S0_01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S0 (proof development, AUTHOR; not reviewed). Initial-value clauses of the head G1_036:
   wkbRemainder N z φ 0 = 0 and wkbSymmetricRemainder N z φ 0 = 0. Both follow from D(0) = 0
   (g36_s2b_D_zero, S2b.0) because wkbRemainder N z φ t = (2 I z)^N • g36_s2b_D N z φ t by definition.
   The swapped clause is the same statement at (-z, swappedPotential φ). -/

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g36_s0_wkbRemainder_zero (N : ℕ) (z : ℂ) (φ : PotPair) : wkbRemainder N z φ 0 = 0 := by
  show (2 * Complex.I * z) ^ N • g36_s2b_D N z φ 0 = 0
  rw [g36_s2b_D_zero, smul_zero]

theorem g36_s0_wkbSymmetricRemainder_zero (N : ℕ) (z : ℂ) (φ : PotPair) :
    wkbSymmetricRemainder N z φ 0 = 0 := by
  funext i
  fin_cases i
  · simp [wkbSymmetricRemainder, g36_s0_wkbRemainder_zero]
  · simp [wkbSymmetricRemainder, g36_s0_wkbRemainder_zero]

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_S0_01

section Inline_G1036_S6_01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 S6 (proof development, AUTHOR; not reviewed). Supporting lemmas S6.1-S6.5 of the assembly of G1_036.
   S6.1  H1 bound of wkbPartial for |z| >= 1 (G1_034 wkb_bound, psn_sum; scalar norm g36_psn_smul copied from h161_psn_smul).
   S6.2  sup bound of wkbAlpha (proof development SUP01: g36_fourierRepresentative_norm_le).
   S6.3  phase modulus on [0,1].
   S6.4  strip bound of the fundamental matrix (SUP01 g36_fundPair_strip_entry_le) and its adjugate.
   S6.5  remainder bound on [0,1] via S5 (variation of constants), S2b (defect ODE), S6.3, S6.4 and S3-composed.
   No Gronwall. Constants are produced in g36_s6_main from N, B, tau only. -/

namespace NlsGge.GKDefinitionDesign
noncomputable section
open MeasureTheory Filter Topology Set
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped BigOperators Matrix

/-! ### S6.1 H1 bound of the partial sum -/

theorem g36_psn_smul (m : ℕ) (c : ℂ) (u : PhysicalL2) :
    physicalSobolevNorm (m : ℝ) (c • u) = ‖c‖ * physicalSobolevNorm (m : ℝ) u := by
  rw [psn_eq_hn, psn_eq_hn]
  have hf : fourierSeq38 (c • u) = fun n => c * fourierSeq38 u n := by
    funext n
    unfold fourierSeq38
    simp
  rw [hf]
  unfold hn
  beta_reduce
  have key : ∑' n : ℤ, (japaneseBracket n) ^ (2 * m) * ‖c * fourierSeq38 u n‖ ^ 2 =
      ‖c‖ ^ 2 * ∑' n : ℤ, (japaneseBracket n) ^ (2 * m) * ‖fourierSeq38 u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    congr 1
    funext n
    rw [norm_mul]
    ring
  rw [key, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem g36_s6_partial_H1 (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 < K ∧ ∃ p : ℕ, ∀ φ : PotPair, pairSobolev (N : ℝ) φ → ∀ z : ℂ, 1 ≤ ‖z‖ →
      physicalSobolev 1 (wkbPartial N z φ) ∧
        physicalSobolevNorm 1 (wkbPartial N z φ) ≤ K * (1 + pairSobolevNorm (N : ℝ) φ) ^ p := by
  obtain ⟨C0, hC0, p0, hw⟩ := wkb_bound N N hN le_rfl
  refine ⟨((N : ℝ) + 1) * C0, by positivity, p0, ?_⟩
  intro φ hφ z hz
  have hX : 0 ≤ pairSobolevNorm (N : ℝ) φ := (pairSobolevNorm_ge N φ).1
  have hY : 0 ≤ (1 + pairSobolevNorm (N : ℝ) φ) ^ p0 := pow_nonneg (by linarith) _
  have hcoef : ∀ n : ℕ, ‖((2 * Complex.I * z) ^ n)⁻¹‖ ≤ 1 := by
    intro n
    rw [norm_inv, norm_pow]
    have h2 : (1 : ℝ) ≤ ‖2 * Complex.I * z‖ := by
      have : ‖2 * Complex.I * z‖ = 2 * ‖z‖ := by simp [norm_mul]
      rw [this]
      linarith
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h2)
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      physicalSobolev ((1 : ℕ) : ℝ) (((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) ∧
      physicalSobolevNorm ((1 : ℕ) : ℝ) (((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) ≤
        C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0 := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨h1, h2⟩ := hw φ hφ n hn1 hn2
    obtain ⟨h3, h4⟩ := psn_mono (show 1 ≤ N + 1 - n by omega) h1
    refine ⟨g35_H1_cast _ (g35_H1_smul _ (g35_H1_nat _ h3)), ?_⟩
    rw [g36_psn_smul]
    calc ‖((2 * Complex.I * z) ^ n)⁻¹‖ * physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ n)
        ≤ 1 * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0) :=
          mul_le_mul (hcoef n) (h4.trans h2) (psn_nonneg 1 _) zero_le_one
      _ = C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0 := one_mul _
  obtain ⟨hs1, hs2⟩ := psn_sum 1 (Finset.Icc 1 N)
    (fun n => ((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) (fun n hn => (hterm n hn).1)
  have hsum : ∑ n ∈ Finset.Icc 1 N,
      physicalSobolevNorm ((1 : ℕ) : ℝ) (((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n) ≤
      (N : ℝ) * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0) := by
    calc _ ≤ ∑ n ∈ Finset.Icc 1 N, C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0 :=
          Finset.sum_le_sum (fun n hn => (hterm n hn).2)
      _ = (N : ℝ) * (C0 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p0) := by simp
  have hcast : physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbPartial N z φ) =
      physicalSobolevNorm 1 (wkbPartial N z φ) := by rw [Nat.cast_one]
  unfold wkbPartial at hcast ⊢
  refine ⟨g35_H1_nat _ hs1, ?_⟩
  rw [← hcast]
  refine hs2.trans (hsum.trans ?_)
  nlinarith [mul_nonneg hC0.le hY]

/-! ### S6.2 sup bound of the WKB phase integrand -/

theorem g36_s6_alpha_norm_le (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ)) (s : ℝ) :
    ‖wkbAlpha N z φ s‖ ≤
      ‖NlsGge.Analysis.reciprocalBracketL2‖ * physicalSobolevNorm 1 (wkbPartial N z φ) := by
  unfold wkbAlpha
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact g36_fourierRepresentative_norm_le _ hP s

/-! ### S6.3 the phase modulus on the unit interval -/

theorem g36_s6_phase_exp_le (z : ℂ) (t A a : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (J : ℂ)
    (hJ : ‖J‖ ≤ A * a) :
    ‖Complex.exp (-Complex.I * z * (t : ℂ) + Complex.I * J)‖ ≤ Real.exp (|z.im| + A * a) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-Complex.I * z * (t : ℂ) + Complex.I * J).re = z.im * t - J.im := by
    simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hre]
  have h4 : z.im * t ≤ |z.im| :=
    calc z.im * t ≤ |z.im| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht.1
      _ ≤ |z.im| := mul_le_of_le_one_right (abs_nonneg _) ht.2
  have h5 : -J.im ≤ ‖J‖ := (neg_le_abs J.im).trans (Complex.abs_im_le_norm J)
  linarith

theorem g36_s6_phase_norm_le (N : ℕ) (z : ℂ) (φ : PotPair) (A : ℝ)
    (hα : ∀ s : ℝ, ‖wkbAlpha N z φ s‖ ≤ A) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖wkbPhase N z φ t‖ ≤ Real.exp (|z.im| + A * ‖φ.1‖) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hα 0)
  have hgint : IntervalIntegrable (fun s => A * ‖potRepFst38 φ s‖) volume 0 1 :=
    (intervalIntegrable_norm_coverRep38_one φ.1).const_mul A
  have hgint_t : IntervalIntegrable (fun s => A * ‖potRepFst38 φ s‖) volume 0 t :=
    hgint.mono_set (Set.uIcc_subset_uIcc_left (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ht))
  have h1 : ‖∫ s in (0 : ℝ)..t, potRepFst38 φ s * wkbAlpha N z φ s‖ ≤
      ∫ s in (0 : ℝ)..t, A * ‖potRepFst38 φ s‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ hgint_t
    refine Filter.Eventually.of_forall (fun s _ => ?_)
    rw [norm_mul]
    calc ‖potRepFst38 φ s‖ * ‖wkbAlpha N z φ s‖ ≤ ‖potRepFst38 φ s‖ * A :=
          mul_le_mul_of_nonneg_left (hα s) (norm_nonneg _)
      _ = A * ‖potRepFst38 φ s‖ := mul_comm _ _
  have h2 : ∫ s in (0 : ℝ)..t, A * ‖potRepFst38 φ s‖ ≤ ∫ s in (0 : ℝ)..1, A * ‖potRepFst38 φ s‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun s => mul_nonneg hA (norm_nonneg _))) hgint
  have h3 : ∫ s in (0 : ℝ)..1, A * ‖potRepFst38 φ s‖ ≤ A * ‖φ.1‖ := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_coverRep38_le_one φ.1) hA
  unfold wkbPhase
  exact g36_s6_phase_exp_le z t A ‖φ.1‖ ht _ ((h1.trans h2).trans h3)

/-! ### S6.4 matrix bookkeeping for the variation of constants -/

theorem g36_s6_mulVec_two (A : Matrix (Fin 2) (Fin 2) ℂ) (v : PairVec38) (j : Fin 2) :
    ‖(A *ᵥ v) j‖ ≤ ‖A j 0‖ * ‖v 0‖ + ‖A j 1‖ * ‖v 1‖ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (norm_add_le _ _).trans (le_of_eq (by rw [norm_mul, norm_mul]))

theorem g36_s6_adj_entry (M : Matrix (Fin 2) (Fin 2) ℂ) (E : ℝ) (h : ∀ a b, ‖M a b‖ ≤ E)
    (a b : Fin 2) : ‖Matrix.adjugate M a b‖ ≤ E := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_two, h]

theorem g36_s6_vc_bound (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (g : ℝ → PairVec38) (E : ℝ)
    (h : ℝ → ℝ)
    (hE : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a b, ‖M s a b‖ ≤ E)
    (hh : IntervalIntegrable h volume 0 1) (hh0 : ∀ s, 0 ≤ h s)
    (hgb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, ‖g s k‖ ≤ h s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    ‖Matrix.mulVec (M t) (fun j => ∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) j) i‖ ≤
      4 * E ^ 2 * ∫ s in (0 : ℝ)..1, h s := by
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0 h0I 0 0)
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ j, ‖(Matrix.adjugate (M s) *ᵥ g s) j‖ ≤ 2 * E * h s := by
    intro s hs j
    refine (g36_s6_mulVec_two _ _ j).trans ?_
    have a0 := g36_s6_adj_entry (M s) E (hE s hs) j 0
    have a1 := g36_s6_adj_entry (M s) E (hE s hs) j 1
    have b0 := mul_le_mul a0 (hgb s hs 0) (norm_nonneg _) hE0
    have b1 := mul_le_mul a1 (hgb s hs 1) (norm_nonneg _) hE0
    linarith
  have hIt : ∫ s in (0 : ℝ)..t, h s ≤ ∫ s in (0 : ℝ)..1, h s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun s => hh0 s)) hh
  have hint_t : IntervalIntegrable (fun s => 2 * E * h s) volume 0 t :=
    (hh.const_mul (2 * E)).mono_set
      (Set.uIcc_subset_uIcc_left (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ht))
  have hw : ∀ j, ‖∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) j‖ ≤
      2 * E * ∫ s in (0 : ℝ)..1, h s := by
    intro j
    have h1 : ‖∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) j‖ ≤
        ∫ s in (0 : ℝ)..t, 2 * E * h s :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall (fun s hs => hpt s ⟨hs.1.le, hs.2.trans ht.2⟩ j)) hint_t
    rw [intervalIntegral.integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hIt (by linarith))
  have h0 := g36_s6_mulVec_two (M t)
    (fun j => ∫ s in (0 : ℝ)..t, (Matrix.adjugate (M s) *ᵥ g s) j) i
  beta_reduce at h0
  have c0 := mul_le_mul (hE t ht i 0) (hw 0) (norm_nonneg _) hE0
  have c1 := mul_le_mul (hE t ht i 1) (hw 1) (norm_nonneg _) hE0
  nlinarith

/-! ### S6.5 the remainder bound on the unit interval -/

theorem g36_s6_remainder_bound (N : ℕ) (z : ℂ) (φ : PotPair)
    (hP : physicalSobolev 1 (wkbPartial N z φ))
    (hp : productInL2 (wkbPartial N z φ) (wkbPartial N z φ))
    (hq : productInL2 φ.1 (physicalProduct (wkbPartial N z φ) (wkbPartial N z φ)))
    (E Φ : ℝ)
    (hΦ : ∀ s ∈ Icc (0 : ℝ) 1, ‖wkbPhase N z φ s‖ ≤ Φ)
    (hE : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a b, ‖Set.IccExtend zero_le_one (fundPair φ z) s a b‖ ≤ E)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    ‖(wkbRemainder N z φ t) i‖ ≤ 4 * E ^ 2 * Φ *
      ∫ s in (0 : ℝ)..1, ‖(2 * Complex.I * z) ^ N • coverRep38 (wkbResidual N z φ) s‖ := by
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (hΦ 0 h0I)
  have htr : ∀ s : ℝ, zsCoeffPot38 φ z s 0 0 + zsCoeffPot38 φ z s 1 1 = 0 := by
    intro s
    obtain ⟨b00, -, -, b11⟩ := g36_s2b_B_entries φ z s
    rw [b00, b11]
    ring
  have hdet : ∀ s ∈ Icc (0 : ℝ) 1, (Set.IccExtend zero_le_one (fundPair φ z) s).det = 1 := by
    intro s hs
    rw [Set.IccExtend_of_mem (h := zero_le_one) (f := fundPair φ z) (hx := hs)]
    exact det_fundPair38 φ z ⟨s, hs⟩
  have hMac : ∀ a b : Fin 2,
      AbsolutelyContinuousOnInterval (fun r => ext38 (fundContP φ z) r a b) 0 1 :=
    fun a b => ac_fundContP_entry38 φ z a b
  have hMode : ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ a b : Fin 2,
      HasDerivAt (fun r => ext38 (fundContP φ z) r a b)
        ((zsCoeffPot38 φ z s * ext38 (fundContP φ z) s) a b) s := by
    have h4 : ∀ᵐ s : ℝ, ∀ a b : Fin 2, s ∈ Icc (0 : ℝ) 1 →
        HasDerivAt (fun r => ext38 (fundContP φ z) r a b)
          ((zsCoeffPot38 φ z s * ext38 (fundContP φ z) s) a b) s :=
      ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_hasDerivAt_fundContP_entry38 φ z a b
    filter_upwards [h4] with s hs hsI a b
    exact hs a b (Ioo_subset_Icc_self hsI)
  have hDac : ∀ a : Fin 2, AbsolutelyContinuousOnInterval (fun r => g36_s2b_D N z φ r a) 0 1 :=
    Fin.forall_fin_two.2 ⟨g36_s2b_D0_ac N z φ hP, g36_s2b_D1_ac N z φ hP⟩
  have hDode : ∀ᵐ s : ℝ, s ∈ Ioo (0 : ℝ) 1 → ∀ a : Fin 2,
      HasDerivAt (fun r => g36_s2b_D N z φ r a)
        ((Matrix.mulVec (zsCoeffPot38 φ z s) (g36_s2b_D N z φ s)) a +
          ((Complex.I * wkbPhase N z φ s) •
            ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) a) s := by
    filter_upwards [g36_s2b_D0_deriv_ae N z φ hP, g36_s2b_D1_deriv_ae N z φ hP hp hq] with
      s h0 h1 hsI
    exact Fin.forall_fin_two.2 ⟨h0 hsI, h1 hsI⟩
  have hcϕ : ContinuousOn (fun s => Complex.I * wkbPhase N z φ s) (uIcc 0 1) :=
    continuousOn_const.mul (g36_s2b_phase_ac N z φ hP).continuousOn
  have hgint : ∀ j : Fin 2, IntervalIntegrable (fun s => ((Complex.I * wkbPhase N z φ s) •
      ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) j) volume 0 1 := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have e : (fun s => ((Complex.I * wkbPhase N z φ s) •
          ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) 0) = fun _ => (0 : ℂ) := by
        funext s
        simp
      rw [e]
      exact intervalIntegrable_const
    · have e : (fun s => ((Complex.I * wkbPhase N z φ s) •
          ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) 1) =
          fun s => (Complex.I * wkbPhase N z φ s) * coverRep38 (wkbResidual N z φ) s := by
        funext s
        simp
      rw [e]
      exact (intervalIntegrable_coverRep38_one (wkbResidual N z φ)).continuousOn_mul hcϕ
  have vc := g36_s5_variation_of_constants
    (fun r => Set.IccExtend zero_le_one (fundPair φ z) r) (zsCoeffPot38 φ z)
    (g36_s2b_D N z φ)
    (fun s => (Complex.I * wkbPhase N z φ s) •
      ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s])
    htr hdet hMac hMode hDac hDode (g36_s2b_D_zero N z φ) hgint t ht
  have hh : IntervalIntegrable (fun s => Φ * ‖coverRep38 (wkbResidual N z φ) s‖) volume 0 1 :=
    (intervalIntegrable_norm_coverRep38_one (wkbResidual N z φ)).const_mul Φ
  have hh0 : ∀ s : ℝ, 0 ≤ Φ * ‖coverRep38 (wkbResidual N z φ) s‖ :=
    fun s => mul_nonneg hΦ0 (norm_nonneg _)
  have hgb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k : Fin 2, ‖((Complex.I * wkbPhase N z φ s) •
      ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) k‖ ≤
      Φ * ‖coverRep38 (wkbResidual N z φ) s‖ := by
    intro s hs
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have e : ‖((Complex.I * wkbPhase N z φ s) •
          ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) 0‖ = 0 := by simp
      rw [e]
      exact hh0 s
    · have e : ‖((Complex.I * wkbPhase N z φ s) •
          ![(0 : ℂ), coverRep38 (wkbResidual N z φ) s]) 1‖ =
          ‖wkbPhase N z φ s‖ * ‖coverRep38 (wkbResidual N z φ) s‖ := by
        simp [norm_mul]
      rw [e]
      exact mul_le_mul_of_nonneg_right (hΦ s hs) (norm_nonneg _)
  have hD : ‖g36_s2b_D N z φ t i‖ ≤
      4 * E ^ 2 * ∫ s in (0 : ℝ)..1, Φ * ‖coverRep38 (wkbResidual N z φ) s‖ := by
    rw [vc]
    exact g36_s6_vc_bound (fun r => Set.IccExtend zero_le_one (fundPair φ z) r) _ E
      (fun s => Φ * ‖coverRep38 (wkbResidual N z φ) s‖) hE hh hh0 hgb t ht i
  have e1 : ∫ s in (0 : ℝ)..1, ‖(2 * Complex.I * z) ^ N • coverRep38 (wkbResidual N z φ) s‖ =
      ‖2 * Complex.I * z‖ ^ N * ∫ s in (0 : ℝ)..1, ‖coverRep38 (wkbResidual N z φ) s‖ := by
    simp_rw [norm_smul, norm_pow]
    exact intervalIntegral.integral_const_mul _ _
  have e2 : ∫ s in (0 : ℝ)..1, Φ * ‖coverRep38 (wkbResidual N z φ) s‖ =
      Φ * ∫ s in (0 : ℝ)..1, ‖coverRep38 (wkbResidual N z φ) s‖ :=
    intervalIntegral.integral_const_mul _ _
  rw [e1]
  rw [e2] at hD
  show ‖((2 * Complex.I * z) ^ N • g36_s2b_D N z φ t) i‖ ≤ _
  rw [Pi.smul_apply, norm_smul, norm_pow]
  calc ‖2 * Complex.I * z‖ ^ N * ‖g36_s2b_D N z φ t i‖
      ≤ ‖2 * Complex.I * z‖ ^ N * (4 * E ^ 2 * (Φ *
          ∫ s in (0 : ℝ)..1, ‖coverRep38 (wkbResidual N z φ) s‖)) :=
        mul_le_mul_of_nonneg_left hD (pow_nonneg (norm_nonneg _) _)
    _ = 4 * E ^ 2 * Φ * (‖2 * Complex.I * z‖ ^ N *
          ∫ s in (0 : ℝ)..1, ‖coverRep38 (wkbResidual N z φ) s‖) := by ring

/-! ### S6 norms of the potentials on the Sobolev ball -/

theorem g36_s6_norm_le_pair (N : ℕ) (φ : PotPair) (hφ : pairSobolev (N : ℝ) φ) :
    ‖φ.1‖ ≤ pairSobolevNorm (N : ℝ) φ ∧ ‖φ.2‖ ≤ pairSobolevNorm (N : ℝ) φ := by
  obtain ⟨-, h1, h2⟩ := pairSobolevNorm_ge N φ
  refine ⟨?_, ?_⟩
  · calc ‖φ.1‖ = physicalSobolevNorm ((0 : ℕ) : ℝ) φ.1 := (g35_psn_zero _).symm
      _ ≤ physicalSobolevNorm (N : ℝ) φ.1 := (psn_mono (Nat.zero_le N) hφ.1).2
      _ ≤ _ := h1
  · calc ‖φ.2‖ = physicalSobolevNorm ((0 : ℕ) : ℝ) φ.2 := (g35_psn_zero _).symm
      _ ≤ physicalSobolevNorm (N : ℝ) φ.2 := (psn_mono (Nat.zero_le N) hφ.2).2
      _ ≤ _ := h2

/-! ### S6.7 uniform remainder bound with explicit constants (Lambda = 1) -/

theorem g36_s6_main (N : ℕ) (hN : 1 ≤ N) (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : PotPair, pairSobolev (N : ℝ) φ → pairSobolevNorm (N : ℝ) φ ≤ B →
      ∀ z : ℂ, |z.im| ≤ τ → 1 ≤ ‖z‖ → ∀ t ∈ Icc (0 : ℝ) 1, ‖wkbRemainder N z φ t‖ ≤ C := by
  obtain ⟨K, hK, p1, hH⟩ := g36_s6_partial_H1 N hN
  obtain ⟨C35, hC35, p35, hG⟩ := G1_035 N hN
  have hR : 0 ≤ ‖NlsGge.Analysis.reciprocalBracketL2‖ := norm_nonneg _
  have hB1 : 0 ≤ 1 + B := by linarith
  have hA0 : 0 ≤ ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) :=
    mul_nonneg hR (mul_nonneg hK.le (pow_nonneg hB1 _))
  have hbig : 0 ≤ 4 * (Real.exp (τ + 2 * B)) ^ 2 *
      Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.exp_pos _).le
  refine ⟨4 * (Real.exp (τ + 2 * B)) ^ 2 *
      Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) *
      (2 ^ N * (C35 * (1 + B) ^ p35)) + 1, ?_, ?_⟩
  · have : 0 ≤ 4 * (Real.exp (τ + 2 * B)) ^ 2 *
        Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) *
        (2 ^ N * (C35 * (1 + B) ^ p35)) :=
      mul_nonneg hbig (mul_nonneg (by positivity) (mul_nonneg hC35.le (pow_nonneg hB1 _)))
    linarith
  intro φ hφ hnorm z hzτ hz t ht
  have hX0 : 0 ≤ pairSobolevNorm (N : ℝ) φ := (pairSobolevNorm_ge N φ).1
  obtain ⟨hP, hnP⟩ := hH φ hφ z hz
  obtain ⟨hp, hq, -, hres⟩ := hG φ hφ z hz
  obtain ⟨hn1, hn2⟩ := g36_s6_norm_le_pair N φ hφ
  have hpow1 : (1 + pairSobolevNorm (N : ℝ) φ) ^ p1 ≤ (1 + B) ^ p1 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hpow2 : (1 + pairSobolevNorm (N : ℝ) φ) ^ p35 ≤ (1 + B) ^ p35 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hα : ∀ s : ℝ, ‖wkbAlpha N z φ s‖ ≤
      ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) := fun s =>
    (g36_s6_alpha_norm_le N z φ hP s).trans
      (mul_le_mul_of_nonneg_left (hnP.trans (mul_le_mul_of_nonneg_left hpow1 hK.le)) hR)
  have hΦ : ∀ s ∈ Icc (0 : ℝ) 1, ‖wkbPhase N z φ s‖ ≤
      Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) := by
    intro s hs
    refine (g36_s6_phase_norm_le N z φ _ hα s hs).trans (Real.exp_le_exp.mpr ?_)
    have h1 : ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * ‖φ.1‖ ≤
        ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B :=
      mul_le_mul_of_nonneg_left (hn1.trans hnorm) hA0
    linarith
  have hE : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a b : Fin 2,
      ‖Set.IccExtend zero_le_one (fundPair φ z) s a b‖ ≤ Real.exp (τ + 2 * B) := by
    intro s hs a b
    refine (g36_fundPair_strip_entry_le φ z s hs a b).trans (Real.exp_le_exp.mpr ?_)
    have := g36_potL1Norm38_le φ
    linarith [hn1.trans hnorm, hn2.trans hnorm]
  have hint := g36_s3_source_L1 N z φ C35 (pairSobolevNorm (N : ℝ) φ) p35 hz hres
  refine (pi_norm_le_iff_of_nonempty _).2 (fun i => ?_)
  have hnn : 0 ≤ 4 * (Real.exp (τ + 2 * B)) ^ 2 *
      Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) := hbig
  calc ‖wkbRemainder N z φ t i‖
      ≤ 4 * (Real.exp (τ + 2 * B)) ^ 2 *
        Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) *
        ∫ s in (0 : ℝ)..1, ‖(2 * Complex.I * z) ^ N • coverRep38 (wkbResidual N z φ) s‖ :=
        g36_s6_remainder_bound N z φ hP hp hq _ _ hΦ hE t ht i
    _ ≤ 4 * (Real.exp (τ + 2 * B)) ^ 2 *
        Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) *
        (2 ^ N * (C35 * (1 + pairSobolevNorm (N : ℝ) φ) ^ p35)) :=
        mul_le_mul_of_nonneg_left hint hnn
    _ ≤ 4 * (Real.exp (τ + 2 * B)) ^ 2 *
        Real.exp (τ + ‖NlsGge.Analysis.reciprocalBracketL2‖ * (K * (1 + B) ^ p1) * B) *
        (2 ^ N * (C35 * (1 + B) ^ p35)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow2 hC35.le) (by positivity)) hnn
    _ ≤ _ := le_add_of_nonneg_right zero_le_one

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_S6_01

section Inline_G1036_FINAL01
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix
/- G1-036 FINAL01 (proof development, AUTHOR; not reviewed). The head G1_036 (Pro rounds 7-8 section 23), statement verbatim;
   the proof assembles S0 (clauses 1-2), S6 (clause 3, g36_s6_main with Lambda = 1) and the swapped case. -/

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g36_s6_swapped (N : ℕ) (φ : PotPair) (hφ : pairSobolev (N : ℝ) φ) :
    pairSobolev (N : ℝ) (swappedPotential φ) ∧
      pairSobolevNorm (N : ℝ) (swappedPotential φ) = pairSobolevNorm (N : ℝ) φ := by
  refine ⟨⟨(psn_neg N hφ.2).1, (psn_neg N hφ.1).1⟩, ?_⟩
  unfold pairSobolevNorm
  show Real.sqrt (physicalSobolevNorm (N : ℝ) (-φ.2) ^ 2 + physicalSobolevNorm (N : ℝ) (-φ.1) ^ 2) = _
  rw [(psn_neg N hφ.2).2, (psn_neg N hφ.1).2, add_comm]

theorem G1_036 (N : ℕ) (hN : 1 ≤ N)
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ) :
    ∃ C Λ : ℝ, 0 < C ∧ 1 ≤ Λ ∧
      ∀ φ : PotPair, pairSobolev (N : ℝ) φ →
        pairSobolevNorm (N : ℝ) φ ≤ B →
      ∀ z : ℂ, |z.im| ≤ τ → Λ ≤ ‖z‖ →
        wkbRemainder N z φ 0 = 0 ∧
        wkbSymmetricRemainder N z φ 0 = 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖wkbRemainder N z φ t‖ ≤ C ∧
          ‖wkbSymmetricRemainder N z φ t‖ ≤ C) := by
  obtain ⟨C, hC, hmain⟩ := g36_s6_main N hN B τ hB hτ
  refine ⟨C, 1, hC, le_rfl, ?_⟩
  intro φ hφ hnorm z hzτ hz
  refine ⟨g36_s0_wkbRemainder_zero N z φ, g36_s0_wkbSymmetricRemainder_zero N z φ, ?_⟩
  intro t ht
  refine ⟨hmain φ hφ hnorm z hzτ hz t ht, ?_⟩
  obtain ⟨hsw, hswn⟩ := g36_s6_swapped N φ hφ
  have hb : ‖wkbRemainder N (-z) (swappedPotential φ) t‖ ≤ C :=
    hmain (swappedPotential φ) hsw (hswn ▸ hnorm) (-z) (by simpa using hzτ) (by simpa using hz) t ht
  refine (pi_norm_le_iff_of_nonempty _).2 (fun i => ?_)
  fin_cases i
  · exact (norm_le_pi_norm (wkbRemainder N (-z) (swappedPotential φ) t) 1).trans hb
  · exact (norm_le_pi_norm (wkbRemainder N (-z) (swappedPotential φ) t) 0).trans hb

end
end NlsGge.GKDefinitionDesign
end Inline_G1036_FINAL01

