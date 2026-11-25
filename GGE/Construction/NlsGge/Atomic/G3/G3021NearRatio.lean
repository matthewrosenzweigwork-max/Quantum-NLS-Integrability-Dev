import Mathlib
import NlsGge.Atomic.G2.G2074
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G3.G3008
import NlsGge.Atomic.G3.G3009
import NlsGge.Atomic.G3.G3021NearBase
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.IsolatingDefs

                                                                                                    
                                                                                    
                                                                                             
                                                                                                    
                                                                                                             
                                                                                                
                                                                                                               
                                                                                 
                                                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G3021N

theorem ratio_core (a b μ τ ν g2 : ℂ) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hτd : τ = (b + a) / 2) (hg2d : g2 = (b - a) ^ 2)
    (hντ : ‖ν - τ‖ ≤ Real.sqrt B * ‖b - a‖ ^ 2) (hgM : ‖b - a‖ ≤ 2 * M)
    (hnear : ‖μ - a‖ ≤ ‖μ - b‖) (hω : μ - a ≠ 0) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    stdRoot38 τ g2 (a + (t : ℂ) * (μ - a)) ≠ 0 ∧
      ‖(ν - (a + (t : ℂ) * (μ - a))) / stdRoot38 τ g2 (a + (t : ℂ) * (μ - a))‖ ≤
        (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
          Real.sqrt (‖b - a‖ + ‖μ - a‖) / (Real.sqrt t * Real.sqrt ‖μ - a‖) := by
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have hωpos : 0 < ‖μ - a‖ := norm_pos_iff.2 hω
  set z : ℂ := a + (t : ℂ) * (μ - a) with hz
  have hgd : ‖b - a‖ / 2 ≤ ‖b - z‖ := by
    by_cases hγ : b = a
    · rw [hγ, sub_self, norm_zero, zero_div]
      exact norm_nonneg _
    · have hab : a ≠ b := fun h => hγ h.symm
      exact NlsGge.Atomic.G3.nearest_endpoint_segment a b μ t hab hnear ⟨ht0.le, ht1.le⟩
  have hdw : ‖b - z‖ ≤ ‖b - a‖ + ‖μ - a‖ := by
    have e : b - z = (b - a) - (t : ℂ) * (μ - a) := by
      rw [hz]; ring
    rw [e]
    have h1 : ‖(t : ℂ) * (μ - a)‖ ≤ ‖μ - a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1.le
    calc ‖(b - a) - (t : ℂ) * (μ - a)‖
        ≤ ‖b - a‖ + ‖(t : ℂ) * (μ - a)‖ := norm_sub_le _ _
      _ ≤ ‖b - a‖ + ‖μ - a‖ := by linarith
  have hτz_le : ‖τ - z‖ ≤ 2 * ‖b - z‖ := by
    have e : τ - z = (b - z) - ((1 / 2 : ℝ) : ℂ) * (b - a) := by
      rw [hτd]
      push_cast
      ring
    rw [e]
    calc ‖(b - z) - ((1 / 2 : ℝ) : ℂ) * (b - a)‖
        ≤ ‖b - z‖ + ‖((1 / 2 : ℝ) : ℂ) * (b - a)‖ := norm_sub_le _ _
      _ = ‖b - z‖ + ‖b - a‖ / 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          ring
      _ ≤ 2 * ‖b - z‖ := by linarith [hgd]
  have hzτ : z ≠ τ := by
    intro h
    have h' : a + (t : ℂ) * (μ - a) = (b + a) / 2 := by
      rw [← hτd]
      exact h
    have hγω : b - a = 2 * (t : ℂ) * (μ - a) := by
      linear_combination (-2 : ℂ) * h'
    have hμb : μ - b = (1 - 2 * (t : ℂ)) * (μ - a) := by
      linear_combination hγω * (-1 : ℂ)
    have hle' : ‖μ - a‖ ≤ ‖(1 - 2 * (t : ℂ)) * (μ - a)‖ := by
      rw [← hμb]
      exact hnear
    have hc : ‖(1 - 2 * (t : ℂ))‖ = |1 - 2 * t| := by
      have e : (1 - 2 * (t : ℂ)) = ((1 - 2 * t : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hc] at hle'
    have habs : |1 - 2 * t| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
    nlinarith [hωpos, habs]
  have hdpos : 0 < ‖b - z‖ := by
    rcases (norm_nonneg (b - z)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : b - z = 0 := norm_eq_zero.1 h.symm
      have hbz : b = a + (t : ℂ) * (μ - a) := by
        rw [hz] at h0
        exact sub_eq_zero.1 h0
      have hg0 : ‖b - a‖ = 0 := by
        rw [← h] at hgd
        exact le_antisymm (by linarith) (norm_nonneg _)
      have hab : b = a := sub_eq_zero.1 (norm_eq_zero.1 hg0)
      have htω : (t : ℂ) * (μ - a) = 0 := by
        linear_combination hab - hbz
      exact hω ((mul_eq_zero.1 htω).resolve_left (Complex.ofReal_ne_zero.2 ht0.ne'))
  have hτz0 : τ - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzτ)
  have hstdsq : stdRoot38 τ g2 z ^ 2 = (a - z) * (b - z) := by
    rw [stdRoot_sq_of_ne38 hτz0, hg2d, hτd]
    ring
  have hstdnorm : ‖stdRoot38 τ g2 z‖ =
      Real.sqrt t * Real.sqrt ‖μ - a‖ * Real.sqrt ‖b - z‖ := by
    have haz : ‖a - z‖ = t * ‖μ - a‖ := by
      have e : a - z = -((t : ℂ) * (μ - a)) := by
        rw [hz]; ring
      rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hsq2 : ‖stdRoot38 τ g2 z‖ ^ 2 = t * ‖μ - a‖ * ‖b - z‖ := by
      rw [← norm_pow, hstdsq, norm_mul, haz]
    rw [← Real.sqrt_sq (norm_nonneg (stdRoot38 τ g2 z)), hsq2,
      Real.sqrt_mul (mul_nonneg ht0.le (norm_nonneg _)), Real.sqrt_mul ht0.le]
  have hstdpos : 0 < ‖stdRoot38 τ g2 z‖ := by
    rw [hstdnorm]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 ht0) (Real.sqrt_pos.2 hωpos))
      (Real.sqrt_pos.2 hdpos)
  have hstd0 : stdRoot38 τ g2 z ≠ 0 := norm_pos_iff.1 hstdpos
  have hR := G3009Aux.real_ineq ‖b - a‖ ‖μ - a‖ ‖b - z‖ B M (norm_nonneg _) hωpos hdpos hgd hdw hgM
    hB hM
  have hsplit : ν - z = (ν - τ) + (τ - z) := by ring
  have htri := norm_add_le (ν - τ) (τ - z)
  have hnum : ‖ν - z‖ ≤
      (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
        (Real.sqrt (‖b - a‖ + ‖μ - a‖) * Real.sqrt ‖b - z‖) := by
    rw [hsplit]
    linarith [htri, hντ, hτz_le, hR]
  refine ⟨hstd0, ?_⟩
  rw [norm_div, div_le_iff₀ hstdpos, hstdnorm]
  have hsr : Real.sqrt t * Real.sqrt ‖μ - a‖ ≠ 0 :=
    (mul_pos (Real.sqrt_pos.2 ht0) (Real.sqrt_pos.2 hωpos)).ne'
  have key : (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
        Real.sqrt (‖b - a‖ + ‖μ - a‖) /
          (Real.sqrt t * Real.sqrt ‖μ - a‖) *
        (Real.sqrt t * Real.sqrt ‖μ - a‖ * Real.sqrt ‖b - z‖) =
      (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
        (Real.sqrt (‖b - a‖ + ‖μ - a‖) * Real.sqrt ‖b - z‖) := by
    rw [div_mul_eq_mul_div, div_eq_iff hsr]
    ring
  rw [key]
  exact hnum

end G3021N

/-- Generic form of G3_009: the ratio bound along the segment from the nearer endpoint. -/
theorem near_ratio_bound (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
  ∃ V : Set PotPair, ∃ C : ℝ,
    IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW ∧ 0 < C ∧
    ∀ φ ∈ V, ∀ n m : ℤ, m ≠ n →
      nearOmega m φ ≠ 0 → ∀ t ∈ Ioo (0 : ℝ) 1,
        standardRoot φ m (nearSegPoint m φ t) ≠ 0 ∧
        ‖nearRatio n m φ t‖ ≤
          C * Real.sqrt (‖gap φ m‖ + ‖nearOmega m φ‖) /
            (Real.sqrt t * Real.sqrt ‖nearOmega m φ‖) := by
  obtain ⟨V74, hV74o, hφV74, hV74W, B, hB, hA74⟩ := G2_074 φ0 hφ0
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨U, hUo, hφU, hUgk, C₀, R, c, N, hgeo, hspec⟩ := g2019_leaf_family φ0 hgk0
  obtain ⟨M, hM0, hM⟩ := G3009Aux.radius_bound hgeo
  refine ⟨V74 ∩ U, 2 + Real.sqrt 2 * Real.sqrt B * (2 * M), hV74o.inter hUo,
    ⟨hφV74, hφU⟩, fun φ hφ => hV74W hφ.1, ?_, ?_⟩
  · have h0 : 0 ≤ Real.sqrt 2 * Real.sqrt B * (2 * M) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg B)) (by linarith)
    linarith
  intro φ hφ n m hmn hω t ht
  have hgk : φ ∈ gkW := hUgk hφ.2
  have hsp : IsolatingSpectral38 φ C₀ R := hspec φ hφ.2
  obtain ⟨A, hfac, hsum, hle⟩ := hA74 φ hφ.1 n
  have hν : normalizedRoot n m φ = tauN φ m + gamma2 φ m * A ⟨m, hmn⟩ := hfac ⟨m, hmn⟩
  have hAsq : ‖A ⟨m, hmn⟩‖ ^ 2 ≤ B :=
    le_trans (hsum.le_tsum ⟨m, hmn⟩ (fun j _ => sq_nonneg _)) hle
  have hAn : ‖A ⟨m, hmn⟩‖ ≤ Real.sqrt B := by
    have h := Real.abs_le_sqrt hAsq
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have hg2d : gamma2 φ m = (farEnd m φ - nearEnd m φ) ^ 2 := G3021N.gamma2_eq_near_far m φ hgk
  have hτd : tauN φ m = (farEnd m φ + nearEnd m φ) / 2 := G3021N.tauN_eq_near_far m φ hgk
  have hgM : ‖farEnd m φ - nearEnd m φ‖ ≤ 2 * M := by
    rw [G3021N.norm_far_sub_near]
    exact le_trans (G3009Aux.gap_le hsp m).le (by linarith [hM m])
  have hντ : ‖normalizedRoot n m φ - tauN φ m‖ ≤
      Real.sqrt B * ‖farEnd m φ - nearEnd m φ‖ ^ 2 := by
    rw [hν, add_sub_cancel_left, norm_mul, hg2d, norm_pow, mul_comm (Real.sqrt B)]
    exact mul_le_mul_of_nonneg_left hAn (sq_nonneg _)
  have hcore := G3021N.ratio_core (nearEnd m φ) (farEnd m φ) (muSeq φ m) (tauN φ m)
    (normalizedRoot n m φ) (gamma2 φ m) B M hB.le hM0 hτd hg2d hντ hgM (G3021N.near_le_far m φ) hω t ht
  have hn : ‖farEnd m φ - nearEnd m φ‖ = ‖gap φ m‖ := G3021N.norm_far_sub_near m φ
  rw [hn] at hcore
  exact hcore

end
end NlsGge.GKDefinitionDesign
