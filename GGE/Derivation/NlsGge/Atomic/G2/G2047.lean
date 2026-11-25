import Mathlib
import NlsGge.GK38.AbelianRealMeanValue
import NlsGge.GK38.AbelianStdRootAverage

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G2047Aux

theorem ofReal_mem_segment (a b x : ℝ) (hx : x ∈ segment ℝ a b) :
    (x : ℂ) ∈ segment ℝ (a : ℂ) (b : ℂ) := by
  obtain ⟨s, t, hs, ht, hst, h⟩ := hx
  exact ⟨s, t, hs, ht, hst, by
    rw [← h]; simp [Complex.real_smul]⟩

theorem ordered (a b : ℝ) (hab : a ≤ b) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcut : segment ℝ (a : ℂ) (b : ℂ) ⊆ Metric.ball c r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r))
    (hfR : ∀ z ∈ segment ℝ (a : ℂ) (b : ℂ), (f z).im = 0) :
    ∃ x ∈ segment ℝ (a : ℂ) (b : ℂ),
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z => f z / stdRoot38 (((a : ℂ) + b) / 2) (((b : ℂ) - a) ^ 2) z) c r
          = -f x := by
  obtain ⟨x, hx, h⟩ := p2StdRoot_real_mean_value38 a b hab c r hr hcut f hf
    (fun x hx => hfR _ (ofReal_mem_segment a b x (by rwa [segment_eq_Icc hab])))
  refine ⟨(x : ℂ), ofReal_mem_segment a b x (by rwa [segment_eq_Icc hab]), ?_⟩
  rw [← h]; simp

end G2047Aux

open G2047Aux

theorem G2_047 (a b c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcut : segment ℝ a b ⊆ Metric.ball c r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r)) :
    CircleIntegrable (fun z => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r ∧
    (∀ M : ℝ, 0 ≤ M → (∀ z ∈ segment ℝ a b, ‖f z‖ ≤ M) →
      ‖circleIntegral (fun z => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r‖ ≤
        2*Real.pi*M) ∧
    (a.im=0 → b.im=0 → (∀ z ∈ segment ℝ a b, (f z).im=0) →
      ∃ x ∈ segment ℝ a b,
        (2*(Real.pi : ℂ)*Complex.I)⁻¹ *
          circleIntegral (fun z => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r = -f x) := by
  refine ⟨(p2StdRoot_cosine_average38 a b c r hr hcut f hf).1, ?_, ?_⟩
  · intro M hM hfM
    exact (p2StdRoot_integral_norm_bound38 a b c r M hr hcut f hf hM hfM).2
  · intro ha hb hfR
    obtain ⟨a0, rfl⟩ : ∃ a0 : ℝ, a = (a0 : ℂ) := ⟨a.re, Complex.ext (by simp) (by simpa using ha)⟩
    obtain ⟨b0, rfl⟩ : ∃ b0 : ℝ, b = (b0 : ℂ) := ⟨b.re, Complex.ext (by simp) (by simpa using hb)⟩
    rcases le_total a0 b0 with hab | hab
    · exact ordered a0 b0 hab c r hr hcut f hf hfR
    · have hcut' : segment ℝ (b0 : ℂ) (a0 : ℂ) ⊆ Metric.ball c r := by
        rwa [segment_symm]
      have hfR' : ∀ z ∈ segment ℝ (b0 : ℂ) (a0 : ℂ), (f z).im = 0 := by
        rwa [segment_symm]
      obtain ⟨x, hx, h⟩ := ordered b0 a0 hab c r hr hcut' f hf hfR'
      have e1 : ((b0 : ℂ) + a0) / 2 = ((a0 : ℂ) + b0) / 2 := by ring
      have e2 : ((a0 : ℂ) - b0) ^ 2 = ((b0 : ℂ) - a0) ^ 2 := by ring
      rw [e1, e2] at h
      exact ⟨x, by rwa [segment_symm], h⟩


end
end NlsGge.GKDefinitionDesign
