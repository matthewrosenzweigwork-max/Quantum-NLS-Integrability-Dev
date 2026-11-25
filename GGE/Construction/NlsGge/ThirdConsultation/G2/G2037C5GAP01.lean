import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2028
import NlsGge.ThirdConsultation.G2.G2037Host
import NlsGge.ThirdConsultation.G2.G2037Support1
import NlsGge.ThirdConsultation.G2.G2037Support2
import NlsGge.ThirdConsultation.G2.G2073Support1

                                                                                                                                                                                                      
                                                                                                      
                                                                                        
                                                                                   
                                                                                                        
                                                                                   
                                                                                                 
                                                                                     
                                                              
                                                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2037GapAux

/-- Real inequality for one ellipse quadrant: `((h+w)c-h)^2 + (w s)^2 ≤ w^2` when `h < (h+w)c`. -/
theorem g2037gap_real_ineq (h w c s : ℝ) (hh : 0 ≤ h) (hw : 0 < w) (hc : c ≤ 1)
    (hcs : c ^ 2 + s ^ 2 = 1) (hx : h < (h + w) * c) :
    ((h + w) * c - h) ^ 2 + (w * s) ^ 2 ≤ w ^ 2 := by
  have hA : 0 < (h + w) * c - h := by linarith
  have hB : (h + w) * c - h ≤ w * c := by nlinarith [mul_nonneg hh (sub_nonneg.2 hc)]
  have hsq : ((h + w) * c - h) ^ 2 ≤ (w * c) ^ 2 := by nlinarith
  have e1 : (w * s) ^ 2 = w ^ 2 - w ^ 2 * c ^ 2 := by
    have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
    rw [mul_pow, hs2]; ring
  have e2 : (w * c) ^ 2 = w ^ 2 * c ^ 2 := by ring
  linarith [hsq, e1, e2]

/-- Distance from `a` to the midpoint of `a` and `b`. -/
theorem g2037gap_dist_left_mid (a b : ℂ) : dist a ((a + b) / 2) = ‖b - a‖ / 2 := by
  rw [dist_eq_norm]
  have e : a - (a + b) / 2 = (a - b) / 2 := by ring
  rw [e, norm_div, norm_sub_rev]
  norm_num

/-- Distance from `b` to the midpoint of `a` and `b`. -/
theorem g2037gap_dist_right_mid (a b : ℂ) : dist b ((a + b) / 2) = ‖b - a‖ / 2 := by
  rw [dist_eq_norm]
  have e : b - (a + b) / 2 = (b - a) / 2 := by ring
  rw [e, norm_div]
  norm_num

end G2037GapAux

open G2037GapAux

/-- The disc centred at the midpoint of `[a,b]` with radius `‖b-a‖/2 + 2w`; its width is `w`. -/
def g2037gap_disc (a b : ℂ) (w : ℝ) (hw : 0 < w) : DiscWithSegment where
  center := (a + b) / 2
  radius := ‖b - a‖ / 2 + 2 * w
  radius_pos := by have := norm_nonneg (b - a); linarith
  a := a
  b := b
  contained := by
    have ha : a ∈ Metric.ball ((a + b) / 2) (‖b - a‖ / 2 + 2 * w) := by
      rw [Metric.mem_ball, g2037gap_dist_left_mid]; linarith
    have hb : b ∈ Metric.ball ((a + b) / 2) (‖b - a‖ / 2 + 2 * w) := by
      rw [Metric.mem_ball, g2037gap_dist_right_mid]; linarith
    exact (convex_ball _ _).segment_subset ha hb

theorem g2037gap_disc_width (a b : ℂ) (w : ℝ) (hw : 0 < w) :
    (g2037gap_disc a b w hw).width = w := by
  unfold DiscWithSegment.width
  show (‖b - a‖ / 2 + 2 * w - max (dist a ((a + b) / 2)) (dist b ((a + b) / 2))) / 2 = w
  rw [g2037gap_dist_left_mid, g2037gap_dist_right_mid, max_self]
  ring

/-- The gap ellipse stays within distance `D.width` of the segment (clamped parameter). -/
theorem g2037gap_ellipse_near (D : DiscWithSegment) (θ : ℝ) :
    ∃ t : ℝ, t ∈ Set.Icc (-D.halfLength) D.halfLength ∧
      dist (ellipseParam D θ) (D.midpoint + D.axis * (t : ℂ)) ≤ D.width := by
  obtain ⟨hw, -, hu1, -⟩ := disc_segment_coordinates D
  have hh0 : 0 ≤ D.halfLength := by unfold DiscWithSegment.halfLength; positivity
  have hc1 := Real.cos_le_one θ
  have hc2 := Real.neg_one_le_cos θ
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq θ; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = max (-D.halfLength)
      (min D.halfLength ((D.halfLength + D.width) * Real.cos θ)) := ⟨_, rfl⟩
  have htI : t ∈ Set.Icc (-D.halfLength) D.halfLength := by
    rw [ht]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  refine ⟨t, htI, ?_⟩
  have hdiff : ellipseParam D θ - (D.midpoint + D.axis * (t : ℂ)) =
      D.axis * ((((D.halfLength + D.width) * Real.cos θ - t : ℝ) : ℂ) +
        Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)) := by
    unfold ellipseParam
    push_cast
    ring
  have hsq : ∀ v : ℝ, ‖((v : ℝ) : ℂ) + Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)‖ ^ 2 =
      v ^ 2 + (D.width * Real.sin θ) ^ 2 := by
    intro v
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.add_im, Complex.mul_im]
    ring
  have hreal : ((D.halfLength + D.width) * Real.cos θ - t) ^ 2 +
      (D.width * Real.sin θ) ^ 2 ≤ D.width ^ 2 := by
    by_cases hxh : D.halfLength < (D.halfLength + D.width) * Real.cos θ
    · have hmax : (-D.halfLength) ≤ D.halfLength := by linarith
      have ht' : t = D.halfLength := by
        rw [ht, min_eq_left hxh.le, max_eq_right hmax]
      rw [ht']
      exact g2037gap_real_ineq D.halfLength D.width (Real.cos θ) (Real.sin θ) hh0 hw hc1 hcs hxh
    · by_cases hxl : (D.halfLength + D.width) * Real.cos θ < -D.halfLength
      · have hle : (D.halfLength + D.width) * Real.cos θ ≤ D.halfLength :=
          hxl.le.trans (by linarith)
        have ht' : t = -D.halfLength := by
          rw [ht, min_eq_right hle, max_eq_left hxl.le]
        rw [ht']
        have hx' : D.halfLength < (D.halfLength + D.width) * (-Real.cos θ) := by
          nlinarith
        have hi := g2037gap_real_ineq D.halfLength D.width (-Real.cos θ) (Real.sin θ) hh0 hw
          (by linarith) (by rw [neg_sq]; linarith) hx'
        have e2 : ((D.halfLength + D.width) * Real.cos θ - -D.halfLength) ^ 2 =
            ((D.halfLength + D.width) * (-Real.cos θ) - D.halfLength) ^ 2 := by ring
        rw [e2]
        exact hi
      · have hge : -D.halfLength ≤ (D.halfLength + D.width) * Real.cos θ := not_lt.1 hxl
        have hle : (D.halfLength + D.width) * Real.cos θ ≤ D.halfLength := not_lt.1 hxh
        have ht' : t = (D.halfLength + D.width) * Real.cos θ := by
          rw [ht, min_eq_right hle, max_eq_right hge]
        rw [ht', sub_self]
        have e : D.width ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) = D.width ^ 2 := by
          rw [Real.sin_sq_add_cos_sq θ, mul_one]
        nlinarith [mul_nonneg (sq_nonneg D.width) (sq_nonneg (Real.cos θ))]
  have hN := hsq ((D.halfLength + D.width) * Real.cos θ - t)
  rw [dist_eq_norm, hdiff, norm_mul, hu1, one_mul]
  have hNle : ‖((((D.halfLength + D.width) * Real.cos θ - t : ℝ)) : ℂ) +
      Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)‖ ^ 2 ≤ D.width ^ 2 := by
    rw [hN]; exact hreal
  nlinarith [norm_nonneg (((((D.halfLength + D.width) * Real.cos θ - t : ℝ)) : ℂ) +
      Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)), hNle, hw]

/-- The gap ellipse misses its own gap segment. -/
theorem g2037gap_ellipse_not_own (D : DiscWithSegment) (θ : ℝ) (hw : 0 < D.width) :
    ellipseParam D θ ∉ segment ℝ D.a D.b := by
  intro hseg
  obtain ⟨-, -, hu1, hsegeq⟩ := disc_segment_coordinates D
  rw [hsegeq] at hseg
  obtain ⟨s, hs, hsp⟩ := hseg
  have hax : D.axis ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu1; exact zero_ne_one hu1
  have hsp' : D.midpoint + D.axis * (s : ℂ) = ellipseParam D θ := hsp
  unfold ellipseParam at hsp'
  have h1 := add_left_cancel hsp'
  have h2 := mul_left_cancel₀ hax h1
  have hXim : ((((D.halfLength + D.width) * Real.cos θ : ℝ) : ℂ) +
      Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)).im = D.width * Real.sin θ := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, mul_zero, one_mul, zero_add, add_zero]
  have hXre : ((((D.halfLength + D.width) * Real.cos θ : ℝ) : ℂ) +
      Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)).re = (D.halfLength + D.width) * Real.cos θ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub, add_zero]
  have hsin : D.width * Real.sin θ = 0 := by
    rw [← hXim, ← h2, Complex.ofReal_im]
  have hsre : s = (D.halfLength + D.width) * Real.cos θ := by
    have := congrArg Complex.re h2
    rw [Complex.ofReal_re, hXre] at this
    exact this
  have hs0 : Real.sin θ = 0 := (mul_eq_zero.1 hsin).resolve_left hw.ne'
  have hcos2 : Real.cos θ ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hs0] at this
    nlinarith
  have hh0 : 0 ≤ D.halfLength := by linarith [hs.1, hs.2]
  have hsq : s ^ 2 ≤ D.halfLength ^ 2 := by nlinarith [hs.1, hs.2]
  have hs2 : s ^ 2 = (D.halfLength + D.width) ^ 2 := by
    rw [hsre, mul_pow, hcos2, mul_one]
  nlinarith [mul_nonneg hh0 hw.le, mul_pos hw hw]

/-- (ii) Separation: the tube of isolating disc `n` misses every other gap segment. -/
theorem g2037gap_tube_miss (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (φ : PotPair) (hspec : IsolatingSpectral38 φ C R)
    (n k : ℤ) (hkn : k ≠ n) (z : ℂ) (hz : dist z (C n) < R n + c⁻¹ / 2) :
    z ∉ gapSegment φ k :=
  g2073s1_tube_avoids C R c N hg φ hspec n k hkn z hz

/-- (i) Gap-cycle period: for every index `n` of an isolating family, the gap ellipse of the
explicit disc `g2037gap_disc` around `[lamMinus n, lamPlus n]` has zero period of `finiteGapDifferential`. -/
theorem g2037gap_cycle_period (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hCR : IsolatingFamily38 (realSlice u) C R) (n : ℤ) :
    ∃ D : DiscWithSegment, D.a = lamMinus (realSlice u) n ∧ D.b = lamPlus (realSlice u) n ∧
      curveIntegral (complexForm (finiteGapDifferential u S)) (gapCycle D) = 0 := by
  obtain ⟨c, N, hg, hspec⟩ := hCR
  have hc1 : (1 : ℝ) ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcpos : 0 < c⁻¹ / 2 := by
    have := inv_pos.2 hc0
    linarith
  obtain ⟨V, hVo, hφV, -, U, hUo, hKU, -, -, hder⟩ := G2_028 u n
  have hKc : IsCompact (gapSegment (realSlice u) n) := G2028Aux.isCompact_gapSegment _ _
  obtain ⟨ε, hε, hth⟩ := hKc.exists_thickening_subset_open hUo hKU
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = min (ε / 2) (c⁻¹ / 2) := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hwdef]; exact lt_min (by linarith) hcpos
  have hwε : w < ε := by
    have := min_le_left (ε / 2) (c⁻¹ / 2)
    rw [hwdef]; linarith
  have hwc : w ≤ c⁻¹ / 2 := by rw [hwdef]; exact min_le_right _ _
  set D : DiscWithSegment := g2037gap_disc (lamMinus (realSlice u) n) (lamPlus (realSlice u) n) w hw
    with hD
  have hDw : D.width = w := g2037gap_disc_width _ _ w hw
  refine ⟨D, rfl, rfl, ?_⟩
  -- the gap ellipse lies in U and in rootDomain38 (off every gap segment)
  have hray : ∀ θ : ℝ, ellipseParam D θ ∈ U ∧ (realSlice u, ellipseParam D θ) ∈ rootDomain38 := by
    intro θ
    obtain ⟨t, ht, hdist⟩ := g2037gap_ellipse_near D θ
    have hz0 : D.midpoint + D.axis * (t : ℂ) ∈ gapSegment (realSlice u) n := by
      have hmem : D.midpoint + D.axis * (t : ℂ) ∈ segment ℝ D.a D.b := by
        rw [(disc_segment_coordinates D).2.2.2]
        exact ⟨t, ht, rfl⟩
      exact hmem
    rw [hDw] at hdist
    have hdistε : dist (ellipseParam D θ) (D.midpoint + D.axis * (t : ℂ)) < ε := by linarith
    have hUθ : ellipseParam D θ ∈ U := hth (Metric.mem_thickening_iff.2 ⟨_, hz0, hdistε⟩)
    refine ⟨hUθ, realSlice_mem_gkW u, ?_⟩
    intro hmem
    simp only [gapSegments38, Set.mem_iUnion] at hmem
    obtain ⟨k, hk⟩ := hmem
    by_cases hkn : k = n
    · rw [hkn] at hk
      exact g2037gap_ellipse_not_own D θ (by rw [hDw]; exact hw) hk
    · have hz0' : dist (D.midpoint + D.axis * (t : ℂ)) (C n) < R n := by
        have := (hspec.1 n).1 hz0
        exact mem_ball.1 this
      have hdz : dist (ellipseParam D θ) (C n) < R n + c⁻¹ / 2 := by
        have h1 := dist_triangle (ellipseParam D θ) (D.midpoint + D.axis * (t : ℂ)) (C n)
        linarith
      exact g2037gap_tube_miss C R c N hg (realSlice u) hspec n k hkn _ hdz hk
  have hΩo : IsOpen {z : ℂ | (realSlice u, z) ∈ rootDomain38} :=
    isOpen_rootDomain38.preimage (continuous_const.prodMk continuous_id)
  have hrange : Set.range (gapCycle D) ⊆ U ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38} := by
    rintro _ ⟨t, rfl⟩
    exact hray _
  have hcont : ContinuousOn (finiteGapDifferential u S)
      (U ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38}) := by
    apply ContinuousOn.mono (g2037s1_fgd_analyticOn u S).continuousOn
    intro z hz hc
    rcases hz with ⟨-, hzΩ⟩
    have hz2 : z ∉ gapSegments38 (realSlice u) := by
      obtain ⟨-, h⟩ := hzΩ
      exact h
    unfold finiteGapCuts at hc
    obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.1 hc
    exact hz2 (Set.mem_iUnion.2 ⟨k, hk⟩)
  have hP : ∀ z ∈ U ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38},
      HasDerivAt (localLogDiscriminant n (realSlice u)) (finiteGapDifferential u S z) z := by
    intro z hz
    have hder' := (hder (realSlice u) hφV z hz.1 hz.2).2
    rw [g2037s2_deriv_eq_fgd u S hS z hz.2] at hder'
    exact hder'
  have hprim := primitive_curveIntegral (gapCycle D) (gapCycle_piecewise D)
    (U ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38}) (finiteGapDifferential u S)
    (localLogDiscriminant n (realSlice u)) (hUo.inter hΩo) hrange hcont hP
  rw [hprim, sub_self]

end
end NlsGge.GKDefinitionDesign
