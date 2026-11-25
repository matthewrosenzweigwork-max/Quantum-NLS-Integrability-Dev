/- KST-019 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/KST019_PROOF02.lean.txt (author proof development; independent review PENDING (author is proof development)), byte-identical except this header and the removed `#print axioms` line.
   Target NlsGge/Atomic/KST/KST019.lean, namespace NlsGge.ThirdConsultation.KST. -/
import NlsGge.Atomic.KST.KST018
import NlsGge.GK38.Lib.Rouche
import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013
open NlsGge.Analysis NlsGge.Pilot
open NlsGge.GK38

def determinant (n : ℤ) (a b c : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - center n - a z)^2 - b z * c z

def SmallCoefficients (n : ℤ) (a b c : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ a (spectralStrip n) ∧
  AnalyticOnNhd ℂ b (spectralStrip n) ∧
  AnalyticOnNhd ℂ c (spectralStrip n) ∧
  ∀ z ∈ spectralStrip n,
    ‖a z‖ ≤ Real.pi / 48 ∧ ‖b z‖ ≤ Real.pi / 48 ∧ ‖c z‖ ≤ Real.pi / 48

theorem closedBall_subset_strip (n : ℤ) :
    Metric.closedBall (center n) (Real.pi / 3) ⊆ spectralStrip n := by
  intro z hz
  simp only [spectralStrip, Set.mem_setOf_eq]
  have h1 : ‖z - center n‖ ≤ Real.pi / 3 := by
    simpa [dist_eq_norm] using Metric.mem_closedBall.1 hz
  have hre : (z - center n).re = z.re - (n : ℝ) * Real.pi := by simp [center]
  have h2 : |z.re - (n : ℝ) * Real.pi| ≤ ‖z - center n‖ := by
    have := Complex.abs_re_le_norm (z - center n)
    rwa [hre] at this
  linarith [Real.pi_pos]

theorem kst019 (n : ℤ) (a b c : ℂ → ℂ)
    (h : SmallCoefficients n a b c) :
  (Lib.zeroMultiset (determinant n a b c)
    (Metric.ball (center n) (Real.pi/3))).card = 2 ∧
  (∀ z ∈ spectralStrip n, Real.pi/3 ≤ ‖z-center n‖ →
    determinant n a b c z ≠ 0) ∧
  (Function.support (Lib.zeroMult (determinant n a b c)
    (Metric.ball (center n) (Real.pi/3)))).Finite := by
  obtain ⟨ha, hb, hc, hbd⟩ := h
  have hR : 0 < Real.pi / 3 := by positivity
  have hsub := closedBall_subset_strip n
  set f : ℂ → ℂ := fun z => (z - center n) ^ 2 with hf
  have hfA : AnalyticOnNhd ℂ f (Metric.closedBall (center n) (Real.pi / 3)) := fun z _ =>
    (analyticAt_id.sub analyticAt_const).pow 2
  have hgA : AnalyticOnNhd ℂ (determinant n a b c)
      (Metric.closedBall (center n) (Real.pi / 3)) := fun z hz => by
    have hz' := hsub hz
    exact (((analyticAt_id.sub analyticAt_const).sub (ha z hz')).pow 2).sub
      ((hb z hz').mul (hc z hz'))
  have hrouche : ∀ z ∈ Metric.sphere (center n) (Real.pi / 3),
      ‖determinant n a b c z - f z‖ < ‖f z‖ := by
    intro z hz
    have hzc : ‖z - center n‖ = Real.pi / 3 := by
      simpa [dist_eq_norm] using Metric.mem_sphere.1 hz
    have hz' := hsub (Metric.sphere_subset_closedBall hz)
    obtain ⟨hab, hbb, hcb⟩ := hbd z hz'
    have e : determinant n a b c z - f z =
        -(2 * (z - center n) * a z) + (a z) ^ 2 - b z * c z := by
      simp only [determinant, hf]; ring
    have hfz : ‖f z‖ = (Real.pi / 3) ^ 2 := by
      simp only [hf, norm_pow, hzc]
    rw [e, hfz]
    have n1 : ‖-(2 * (z - center n) * a z) + (a z) ^ 2 - b z * c z‖ ≤
        ‖2 * (z - center n) * a z‖ + ‖a z‖ ^ 2 + ‖b z‖ * ‖c z‖ := by
      calc _ ≤ ‖-(2 * (z - center n) * a z) + (a z) ^ 2‖ + ‖b z * c z‖ := norm_sub_le _ _
        _ ≤ (‖-(2 * (z - center n) * a z)‖ + ‖(a z) ^ 2‖) + ‖b z * c z‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖2 * (z - center n) * a z‖ + ‖a z‖ ^ 2 + ‖b z‖ * ‖c z‖ := by
            rw [norm_neg, norm_pow, norm_mul (b z) (c z)]
    have n2 : ‖2 * (z - center n) * a z‖ = 2 * (Real.pi / 3) * ‖a z‖ := by
      rw [norm_mul, norm_mul, hzc]; simp
    have hπ := Real.pi_pos
    have hnn := norm_nonneg (a z)
    have hnb := norm_nonneg (b z)
    have hnc := norm_nonneg (c z)
    calc _ ≤ _ := n1
      _ ≤ 2 * (Real.pi / 3) * (Real.pi / 48) + (Real.pi / 48) ^ 2 +
          (Real.pi / 48) * (Real.pi / 48) := by
            rw [n2]
            gcongr
      _ < (Real.pi / 3) ^ 2 := by nlinarith [sq_nonneg Real.pi]
  have hcard := NlsGge.GK38.Lib.rouche_circle hR hfA hgA hrouche
  have hf0 : ∀ z ∈ Metric.closedBall (center n) (Real.pi / 3), z ≠ center n → f z ≠ 0 :=
    fun z _ hne => pow_ne_zero 2 (sub_ne_zero.2 hne)
  have hrep := NlsGge.GK38.Lib.zeroMultiset_ball_eq_replicate hR hfA hf0
  have hord : analyticOrderNatAt f (center n) = 2 := by
    have : f = (fun z => z - center n) ^ 2 := rfl
    unfold analyticOrderNatAt
    rw [this, analyticOrderAt_centeredMonomial]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard, hrep, Multiset.card_replicate, hord]
  · intro z hz hzR h0
    obtain ⟨hab, hbb, hcb⟩ := hbd z hz
    have h1 : (z - center n - a z) ^ 2 = b z * c z := by
      have : determinant n a b c z = 0 := h0
      unfold determinant at this
      linear_combination this
    have h2 : ‖z - center n - a z‖ ^ 2 ≤ (Real.pi / 48) ^ 2 := by
      calc ‖z - center n - a z‖ ^ 2 = ‖(z - center n - a z) ^ 2‖ := by rw [norm_pow]
        _ = ‖b z * c z‖ := by rw [h1]
        _ ≤ ‖b z‖ * ‖c z‖ := norm_mul_le _ _
        _ ≤ (Real.pi / 48) * (Real.pi / 48) :=
            mul_le_mul hbb hcb (norm_nonneg _) (by positivity)
        _ = (Real.pi / 48) ^ 2 := by ring
    have h3 : ‖z - center n - a z‖ ≤ Real.pi / 48 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [norm_nonneg (z - center n - a z), Real.pi_pos]
    have h4 : ‖z - center n‖ ≤ ‖z - center n - a z‖ + ‖a z‖ := by
      calc ‖z - center n‖ = ‖(z - center n - a z) + a z‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith [Real.pi_pos]
  · exact NlsGge.GK38.Lib.zeroMult_support_finite hgA.meromorphicOn (isCompact_closedBall _ _)
      Metric.ball_subset_closedBall


end NlsGge.ThirdConsultation.KST
