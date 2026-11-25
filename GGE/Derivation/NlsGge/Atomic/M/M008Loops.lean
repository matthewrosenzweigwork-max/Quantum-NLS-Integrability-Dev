import Mathlib
import NlsGge.GK38.XiSqPeriod
import NlsGge.GK38.ActionRadialIntegrals
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.M.M008Host

/- M-008 SUPPORT S3 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Conjunct (3) of Pro round 6 section 10E
   `omega_gap_period_zero`: every `AdmissibleGapLoop` (C^1 on [0,1], closed, in the isolating disc minus its own gap segment)
   has an interval-integrable integrand and zero `contourIntegral (omega phi)`.
   Route: landed LIB-079 `gap_cycle_period` (any admissible loop in `DiscWithSegment.domain` has integral = winding number times
   the gap-cycle integral), landed `circleLoop`/`curveIntegral_circleLoop` (LIB-015) on a circle of radius r < R enclosing the own
   segment, landed `radial_unweighted_realization` (circle of radius r equals the isolating circle) and `a5FixedPeriod_zero38`
   (zero period of the isolating circle).  So the gap-cycle integral of `omega phi` vanishes for every phi in gkW, whence every
   admissible loop integral vanishes. -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

section Aux
open scoped unitInterval

theorem own_segment_subset_disc (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ discU φ n := by
  obtain ⟨c, N, hgeom, hspec⟩ := isolating_family38 φ hφ
  exact (hspec.1 n).1

/-- The isolating disc of the n-th gap with its own gap segment. -/
def gapDiscSeg (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) : DiscWithSegment where
  center := discC φ n
  radius := discR φ n
  radius_pos := isolating_radius_pos38 (isolating_family38 φ hφ) n
  a := lamMinus φ n
  b := lamPlus φ n
  contained := own_segment_subset_disc φ hφ n

theorem gapDiscSeg_domain (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    (gapDiscSeg φ hφ n).domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl

theorem gapDiscSeg_domain_subset (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    (gapDiscSeg φ hφ n).domain ⊆ actionCutDomain38 φ := by
  intro z hz
  rw [gapDiscSeg_domain] at hz
  intro hmem
  unfold gapSegments38 at hmem
  rw [mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  by_cases hmn : m = n
  · subst hmn
    exact hz.2 hm
  · exact Set.disjoint_left.1 ((isolating φ hφ).1 hmn) (own_segment_subset_disc φ hφ m hm) hz.1

theorem omega_differentiableOn_domain (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    DifferentiableOn ℂ (omega φ) (gapDiscSeg φ hφ n).domain :=
  (a5LogQuotient_analytic38 φ hφ).differentiableOn.mono (gapDiscSeg_domain_subset φ hφ n)

/-- The closed path of a function continuous on `[0,1]` with equal end values. -/
def loopPath (p : ℝ → ℂ) (hc : ContinuousOn p (Icc (0 : ℝ) 1)) (h : p 0 = p 1) : Path (p 0) (p 0) where
  toFun t := p (t : ℝ)
  continuous_toFun := hc.comp_continuous continuous_subtype_val (fun t => t.2)
  source' := by simp
  target' := by simp [h]

theorem loopPath_extend (p : ℝ → ℂ) (hc : ContinuousOn p (Icc (0 : ℝ) 1)) (h : p 0 = p 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (loopPath p hc h).extend t = p t := by
  have e : (loopPath p hc h).extend t = loopPath p hc h ⟨t, ht⟩ := Path.extend_extends' _ ⟨t, ht⟩
  rw [e]
  rfl

theorem loopPath_deriv_extend (p : ℝ → ℂ) (hc : ContinuousOn p (Icc (0 : ℝ) 1)) (h : p 0 = p 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : deriv (loopPath p hc h).extend t = deriv p t := by
  have hev : (loopPath p hc h).extend =ᶠ[𝓝 t] p := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact loopPath_extend p hc h (Ioo_subset_Icc_self hs)
  exact hev.deriv_eq

theorem curveIntegralFun_loopPath (f : ℂ → ℂ) (p : ℝ → ℂ) (hc : ContinuousOn p (Icc (0 : ℝ) 1))
    (h : p 0 = p 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    curveIntegralFun (complexForm f) (loopPath p hc h) x = f (p x) * deriv p x := by
  rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2),
    loopPath_extend p hc h (Ioo_subset_Icc_self hx), loopPath_deriv_extend p hc h hx]
  simp [complexForm]

theorem curveIntegral_loopPath (f : ℂ → ℂ) (p : ℝ → ℂ) (hc : ContinuousOn p (Icc (0 : ℝ) 1))
    (h : p 0 = p 1) :
    curveIntegral (complexForm f) (loopPath p hc h) = contourIntegral p f := by
  rw [curveIntegral_def]
  unfold contourIntegral
  apply intervalIntegral.integral_congr_ae
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact curveIntegralFun_loopPath f p hc h ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

theorem piecewiseC1_of_contDiffOn {a b : ℂ} (γ : Path a b) (G : ℝ → ℂ)
    (hG : ContDiffOn ℝ 1 G (Icc (0 : ℝ) 1)) (hγ : ∀ t : I, γ t = G t) : PiecewiseC1 γ := by
  refine ⟨singlePartition, fun i => ?_⟩
  have hsm : ContDiffOn ℝ 1 (fun u : ℝ =>
      G ((singlePartition.cut i.castSucc : I) + u * ((singlePartition.cut i.succ : I) -
        (singlePartition.cut i.castSucc : I)))) (Icc (0 : ℝ) 1) :=
    hG.comp (by fun_prop) (fun u hu => affMem _ _ hu)
  refine hsm.congr (fun u hu => ?_)
  rw [subpath_extend_eq γ _ _ u hu]
  have e : γ.extend ((singlePartition.cut i.castSucc : I) + u * ((singlePartition.cut i.succ : I) -
      (singlePartition.cut i.castSucc : I))) = γ ⟨_, affMem _ _ hu⟩ :=
    Path.extend_extends' _ ⟨_, affMem _ _ hu⟩
  rw [e, hγ]

end Aux

/-- The gap cycle of the isolating disc carries zero `omega` period, for every `phi` in `gkW`. -/
theorem gapCycle_omega_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    curveIntegral (complexForm (omega φ)) (gapCycle (gapDiscSeg φ hφ n)) = 0 := by
  set D := gapDiscSeg φ hφ n with hD
  have hf : DifferentiableOn ℂ (omega φ) D.domain := omega_differentiableOn_domain φ hφ n
  have hfam := isolating_family38 φ hφ
  have hRpos : 0 < discR φ n := isolating_radius_pos38 hfam n
  -- a circle of radius r < R around the center that encloses the own segment
  have ha : lamMinus φ n ∈ ball (discC φ n) (discR φ n) :=
    own_segment_subset_disc φ hφ n (left_mem_segment ℝ _ _)
  have hb : lamPlus φ n ∈ ball (discC φ n) (discR φ n) :=
    own_segment_subset_disc φ hφ n (right_mem_segment ℝ _ _)
  set m : ℝ := max (dist (lamMinus φ n) (discC φ n)) (dist (lamPlus φ n) (discC φ n)) with hm
  have hmR : m < discR φ n := max_lt (mem_ball.1 ha) (mem_ball.1 hb)
  have hm0 : 0 ≤ m := le_max_of_le_left dist_nonneg
  set r : ℝ := (m + discR φ n) / 2 with hr
  have hmr : m < r := by rw [hr]; linarith
  have hrR : r < discR φ n := by rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt hm0 hmr
  have hseg_r : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (discC φ n) r := by
    have hcb : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ closedBall (discC φ n) m :=
      (convex_closedBall (discC φ n) m).segment_subset
        (by rw [mem_closedBall]; exact le_max_left _ _)
        (by rw [mem_closedBall]; exact le_max_right _ _)
    intro z hz
    exact closedBall_subset_ball hmr (hcb hz)
  -- the circle loop is admissible in the domain
  have hsphere : sphere (discC φ n) r ⊆ D.domain := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show z ∈ ball (discC φ n) (discR φ n)
      rw [mem_ball, mem_sphere.1 hz]; exact hrR
    · intro hzs
      have := hseg_r hzs
      rw [mem_ball, mem_sphere.1 hz] at this
      exact lt_irrefl _ this
  have hpw : PiecewiseC1 (circleLoop (discC φ n) r) :=
    piecewiseC1_of_smooth (circleLoop (discC φ n) r)
      (fun t : ℝ => circleMap (discC φ n) r (2 * Real.pi * t))
      ((contDiff_circleMap _ _).comp (contDiff_const.mul contDiff_id))
      (fun t => (circleMap_eq_cos_sin _ _ _).symm)
  have hrange : range (circleLoop (discC φ n) r) ⊆ D.domain := by
    rintro _ ⟨t, rfl⟩
    apply hsphere
    rw [mem_sphere]
    show dist (discC φ n + (r : ℂ) *
        ((Real.cos (2 * Real.pi * (t : ℝ)) : ℂ) + Complex.I * (Real.sin (2 * Real.pi * (t : ℝ)) : ℂ)))
      (discC φ n) = r
    rw [← circleMap_eq_cos_sin, ← mem_sphere]
    exact circleMap_mem_sphere _ hr0.le _
  obtain ⟨_, _, _, hidx, hper⟩ := gap_cycle_period D (omega φ) hf (circleLoop (discC φ n) r) ⟨hpw, hrange⟩
  -- the circle loop has index one around the midpoint
  have hmid : D.midpoint ∈ ball (discC φ n) r := hseg_r (mid_mem_seg D)
  have hmid_ns : D.midpoint ∉ sphere (discC φ n) r := by
    intro hs
    rw [mem_ball, mem_sphere.1 hs] at hmid
    exact lt_irrefl _ hmid
  have hinv : ContinuousOn (fun z : ℂ => (z - D.midpoint)⁻¹) (sphere (discC φ n) r) := by
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz hz0
    have hz0' : z - D.midpoint = 0 := hz0
    have hzm : z = D.midpoint := sub_eq_zero.1 hz0'
    exact hmid_ns (by rwa [hzm] at hz)
  have hone : indexIntegral (circleLoop (discC φ n) r) D.midpoint = 1 := by
    unfold indexIntegral
    rw [curveIntegral_circleLoop _ _ _ hr0 hinv, circleIntegral.integral_sub_inv_of_mem_ball hmid]
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [inv_mul_cancel₀ h2pi]
  rw [hone] at hidx
  have hw : ((windingNumber (circleLoop (discC φ n) r) D.midpoint : ℤ) : ℂ) = 1 := hidx.symm
  -- the circle integral of omega vanishes
  have hcont : ContinuousOn (omega φ) (sphere (discC φ n) r) :=
    hf.continuousOn.mono hsphere
  have hcirc : curveIntegral (complexForm (omega φ)) (circleLoop (discC φ n) r) = 0 := by
    rw [curveIntegral_circleLoop _ _ _ hr0 hcont]
    have hrad := ActionRadial.radial_unweighted_realization φ hφ (discC φ) (discR φ) hfam n r hr0
      hrR.le hseg_r
    have h0 := (a5FixedPeriod_zero38 φ hφ (discC φ) (discR φ) hfam n).2
    exact hrad.2.2.symm.trans h0
  rw [hper, hw, one_mul] at hcirc
  exact hcirc

/-- Conjunct (3) of the section-10E head: admissible gap loops have zero `omega` period. -/
theorem omega_gap_loop_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (p : ℝ → ℂ)
    (hp : AdmissibleGapLoop φ n p) :
    IntervalIntegrable (fun t : ℝ => omega φ (p t) * deriv p t) volume 0 1 ∧
    contourIntegral p (omega φ) = 0 := by
  obtain ⟨hdiff, hclosed, hmem⟩ := hp
  have hc : ContinuousOn p (Icc (0 : ℝ) 1) := hdiff.continuousOn
  set D := gapDiscSeg φ hφ n with hD
  set γ := loopPath p hc hclosed with hγ
  have hadm : Admissible D.domain γ := by
    refine ⟨piecewiseC1_of_contDiffOn γ p hdiff (fun t => rfl), ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hmem (t : ℝ) t.2
  obtain ⟨hI, _, _, _, hper⟩ := gap_cycle_period D (omega φ) (omega_differentiableOn_domain φ hφ n) γ hadm
  refine ⟨?_, ?_⟩
  · have := hI.congr_uIoo (g := fun t : ℝ => omega φ (p t) * deriv p t) (fun x hx => by
      rw [Set.uIoo_of_le zero_le_one] at hx
      exact curveIntegralFun_loopPath (omega φ) p hc hclosed hx)
    exact this
  · rw [← curveIntegral_loopPath (omega φ) p hc hclosed, hper, gapCycle_omega_zero φ hφ n, mul_zero]

end
end NlsGge.ThirdConsultation.MContour
