import Mathlib
import NlsGge.Atomic.I.I009
import NlsGge.Atomic.I.I010
import NlsGge.Atomic.I.I013
import NlsGge.ThirdConsultation.I.SymmetricKernel
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualQuasimomentumMonotoneE02_38

/- I-014 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/I/I014.lean, namespace
   NlsGge.Atomic.I014. Head VERBATIM from followup7 STATEMENTS/I.md, the I-014 block (sha256 a00da165...).
   Route: composition of accepted production, no new hypothesis, no new definition:
     I-009 finiteGap_convex_difference: integrability of W(2x)v, summability, remainder identity;
     I-010 i010: tangent inequality, integrability of f'(p)(x-p)v;
     I-013 i013: integrability of symmetricKernel and (2/pi) int f'(p)(x-p)v = (1/pi^2) int K;
     monotone_actualQuasimomentumRealPartE02_38, actualGapHeightE02_38_nonneg;
     I-010 hasDerivAt_scaled and ConvexOn.monotoneOn_deriv (Mathlib) for monotonicity of deriv f.
   spectralEnergy is the accepted I-010 copy of DEFINITIONS/I.lean.md:76-77 (same body). -/
set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation.I (symmetricKernel)

namespace NlsGge.Atomic.I014

theorem i014 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hc : ConvexOn ℝ Set.univ W) :
    let v := actualGapHeightE02_38 u
    let p := actualQuasimomentumRealPartE02_38 u
    let f := fun x : ℝ => W (2 * x)
    let D := fun x => (f x - f (p x) - deriv f (p x) * (x - p x)) * v x
    Integrable (fun x => f x * v x) ∧
    Summable (fun n : ℤ => W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n) ∧
    Integrable (symmetricKernel f p v) ∧
    Monotone p ∧ Monotone (deriv f) ∧
    (∀ q : ℝ × ℝ, 0 ≤ symmetricKernel f p v q) ∧
    (∀ x : ℝ, 0 ≤ D x) ∧ Integrable D ∧
    spectralEnergy W u -
      (∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n) =
      (2 / Real.pi) * (∫ x : ℝ, D x) +
        (1 / Real.pi ^ 2) * (∫ q : ℝ × ℝ, symmetricKernel f p v q) ∧
    (∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n) ≤
      spectralEnergy W u := by
  intro v p f D
  obtain ⟨htanPair, hint1₀, hsum₀, hintT₀, -⟩ := NlsGge.Atomic.I010.i010 u hu hfin W hW hc
  obtain ⟨-, hR₀, -, hid9₀⟩ := NlsGge.Atomic.I009.finiteGap_convex_difference u hu hfin W hW hc
  obtain ⟨-, -, -, -, hKint₀, -, -, -, -, hid13₀⟩ := NlsGge.ThirdConsultation.I.i013 u hu hfin W hW hc
  have htan : ∀ x : ℝ, deriv f (p x) * (x - p x) ≤ f x - f (p x) := fun x => (htanPair x).1
  have hint1 : Integrable (fun x : ℝ => f x * v x) := hint1₀
  have hsum : Summable (fun n : ℤ => W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n) := hsum₀
  have hintT : Integrable (fun x : ℝ => deriv f (p x) * (x - p x) * v x) := hintT₀
  have hR : Integrable (remainderIntegrandE02_38 W u) := hR₀
  have hid9 : spectralEnergy W u - ∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n =
      (2 / Real.pi) * ∫ x : ℝ, remainderIntegrandE02_38 W u x := hid9₀
  have hKint : Integrable (symmetricKernel f p v) := hKint₀
  have hid13 : (2 / Real.pi) * (∫ x : ℝ, deriv f (p x) * (x - p x) * v x) =
      (1 / Real.pi ^ 2) * ∫ q : ℝ × ℝ, symmetricKernel f p v q := hid13₀
  have hpm : Monotone p := monotone_actualQuasimomentumRealPartE02_38 u
  have hv0 : ∀ x : ℝ, 0 ≤ v x := fun x => actualGapHeightE02_38_nonneg u x
  have hdf : ∀ x : ℝ, deriv f x = 2 * deriv W (2 * x) := fun x =>
    (NlsGge.Atomic.I010.hasDerivAt_scaled W hW x).deriv
  have hdm : Monotone (deriv f) := by
    intro a b hab
    rw [hdf a, hdf b]
    have hmono : MonotoneOn (deriv W) Set.univ :=
      hc.monotoneOn_deriv (fun x _ => hW.differentiable (by norm_num) x)
    exact mul_le_mul_of_nonneg_left
      (hmono (Set.mem_univ _) (Set.mem_univ _) (by linarith)) (by norm_num)
  have hKnn : ∀ q : ℝ × ℝ, 0 ≤ symmetricKernel f p v q := by
    intro q
    show 0 ≤ (deriv f (p q.1) - deriv f (p q.2)) / (q.1 - q.2) * v q.1 * v q.2
    have hquot : 0 ≤ (deriv f (p q.1) - deriv f (p q.2)) / (q.1 - q.2) := by
      rcases lt_trichotomy q.1 q.2 with h | h | h
      · have hd : deriv f (p q.1) ≤ deriv f (p q.2) := hdm (hpm h.le)
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · rw [h]
        simp
      · have hd : deriv f (p q.2) ≤ deriv f (p q.1) := hdm (hpm h.le)
        exact div_nonneg (by linarith) (by linarith)
    exact mul_nonneg (mul_nonneg hquot (hv0 q.1)) (hv0 q.2)
  have hDnn : ∀ x : ℝ, 0 ≤ D x := by
    intro x
    show 0 ≤ (f x - f (p x) - deriv f (p x) * (x - p x)) * v x
    exact mul_nonneg (by linarith [htan x]) (hv0 x)
  have hD : Integrable D := by
    have hDeq : D = fun x : ℝ => (f x - f (p x)) * v x - deriv f (p x) * (x - p x) * v x := by
      funext x
      show (f x - f (p x) - deriv f (p x) * (x - p x)) * v x =
        (f x - f (p x)) * v x - deriv f (p x) * (x - p x) * v x
      ring
    rw [hDeq]
    exact hR.sub hintT
  have hpt : ∀ x : ℝ, remainderIntegrandE02_38 W u x = D x + deriv f (p x) * (x - p x) * v x := by
    intro x
    show (f x - f (p x)) * v x =
      (f x - f (p x) - deriv f (p x) * (x - p x)) * v x + deriv f (p x) * (x - p x) * v x
    ring
  have hsplit : (∫ x : ℝ, remainderIntegrandE02_38 W u x) =
      (∫ x : ℝ, D x) + ∫ x : ℝ, deriv f (p x) * (x - p x) * v x := by
    rw [← integral_add hD hintT]
    congr 1
    funext x
    exact hpt x
  have hid : spectralEnergy W u - ∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n =
      (2 / Real.pi) * (∫ x : ℝ, D x) + (1 / Real.pi ^ 2) * (∫ q : ℝ × ℝ, symmetricKernel f p v q) := by
    linear_combination hid9 + (2 / Real.pi) * hsplit + hid13
  have hD0 : 0 ≤ ∫ x : ℝ, D x := integral_nonneg fun x => hDnn x
  have hK0 : 0 ≤ ∫ q : ℝ × ℝ, symmetricKernel f p v q := integral_nonneg fun q => hKnn q
  have hnn : 0 ≤ (2 / Real.pi) * (∫ x : ℝ, D x) + (1 / Real.pi ^ 2) * (∫ q : ℝ × ℝ, symmetricKernel f p v q) :=
    add_nonneg (mul_nonneg (by positivity) hD0) (mul_nonneg (by positivity) hK0)
  refine ⟨hint1, hsum, hKint, hpm, hdm, hKnn, hDnn, hD, hid, ?_⟩
  linarith [hid, hnn]

end NlsGge.Atomic.I014
