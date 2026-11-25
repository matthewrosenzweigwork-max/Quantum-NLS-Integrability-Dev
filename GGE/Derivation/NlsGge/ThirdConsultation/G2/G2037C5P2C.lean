import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.ThirdConsultation.G2.G2037C5P2

/- G2-037 CONJUNCT (5) PACKET P2C (proof development, AUTHOR; not self-reviewed; SUPPORTING, not the head).
   Index one on the WHOLE own cut. For the gap disc D of cut k (chord [D.a, D.b] = gapSegment φ k):
   the gap ellipse avoids the chord (LIB079 gapCycle_range), the index is continuous off the ellipse
   (parametric integral with dominated convergence), integer-valued (indexIntegral_int), and the chord
   is connected, so the index is constant on the chord and equals its midpoint value 1
   (g2037p2_index_midpoint). No hypothesis beyond the endpoints of D. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open scoped unitInterval
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2037P2CAux

/-- The gap ellipse has a positive clearance from any point `z` off its range. -/
theorem clearance (D : DiscWithSegment) {z : ℂ} (hz : z ∉ range (gapCycle D)) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ ball z r, ∀ s : ℝ, r ≤ ‖ellipseParam D s - p‖ := by
  have hc : Continuous (fun w : ℂ => dist w z) := continuous_id.dist continuous_const
  obtain ⟨x, hxK, hmin⟩ := (isCompact_range (gapCycle D).continuous).exists_isMinOn
    (Set.range_nonempty _) hc.continuousOn
  have hxz : x ≠ z := fun h => hz (h ▸ hxK)
  have hm : 0 < dist x z := dist_pos.2 hxz
  refine ⟨dist x z / 2, by positivity, fun p hp s => ?_⟩
  have h1 : dist x z ≤ dist (ellipseParam D s) z :=
    isMinOn_iff.mp hmin _ (ellipse_mem_range D s)
  have h2 : dist p z < dist x z / 2 := mem_ball.1 hp
  have h3 := dist_triangle (ellipseParam D s) p z
  rw [← dist_eq_norm]
  linarith

/-- Parametric form of the index off the ellipse (angle lift `θ t = 2π t`, one cell). -/
theorem indexIntegral_eq_param (D : DiscWithSegment) {p : ℂ} (hp : p ∉ range (gapCycle D)) :
    indexIntegral (gapCycle D) p =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∫ s in (0 : ℝ)..(2 * Real.pi), (ellipseParam D s - p)⁻¹ * ellipseDeriv D s := by
  have hf : ContinuousOn (fun z : ℂ => (z - p)⁻¹) (range (gapCycle D)) := by
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    rintro _ ⟨t, rfl⟩
    exact sub_ne_zero.2 (fun h => hp ⟨t, h⟩)
  have hθ : ∀ i : Fin singlePartition.n,
      ContDiffOn ℝ 1 (fun x : ℝ => 2 * Real.pi * x)
        (Icc (singlePartition.cut i.castSucc : ℝ) (singlePartition.cut i.succ : ℝ)) :=
    fun _ => (by fun_prop : ContDiff ℝ 1 (fun x : ℝ => 2 * Real.pi * x)).contDiffOn
  have h := curveIntegral_of_angle_lift D (fun z => (z - p)⁻¹) hf (gapCycle D)
    (gapCycle_piecewise D) (fun x : ℝ => 2 * Real.pi * x) singlePartition hθ (fun _ => rfl)
  unfold indexIntegral
  rw [h]
  simp only [mul_zero, mul_one]

/-- Continuity of the parametric integral at a point off the ellipse (dominated convergence). -/
theorem continuousAt_param (D : DiscWithSegment) {z : ℂ} (hz : z ∉ range (gapCycle D)) :
    ContinuousAt
      (fun p : ℂ => ∫ s in (0 : ℝ)..(2 * Real.pi), (ellipseParam D s - p)⁻¹ * ellipseDeriv D s) z := by
  obtain ⟨r, hr, hcl⟩ := clearance D hz
  have hEc : Continuous (ellipseParam D) :=
    continuous_iff_continuousAt.2 fun s => (ellipseParam_hasDerivAt D s).continuousAt
  have hdc : Continuous (ellipseDeriv D) := by
    unfold ellipseDeriv
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).exists_bound_of_continuousOn
    hdc.continuousOn
  have hball : ∀ p ∈ ball z r, ∀ s : ℝ, ellipseParam D s - p ≠ 0 := by
    intro p hp s h
    have h1 := hcl p hp s
    rw [h, norm_zero] at h1
    linarith
  have hne : ∀ s : ℝ, ellipseParam D s - z ≠ 0 := by
    intro s h
    apply hz
    have h1 := ellipse_mem_range D s
    rwa [sub_eq_zero.1 h] at h1
  have hmeas : ∀ᶠ p in 𝓝 z,
      AEStronglyMeasurable (fun s : ℝ => (ellipseParam D s - p)⁻¹ * ellipseDeriv D s)
        (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with p hp
    exact (((hEc.sub continuous_const).inv₀ (hball p hp)).mul hdc).aestronglyMeasurable
  have hbd : ∀ᶠ p in 𝓝 z, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ‖(ellipseParam D s - p)⁻¹ * ellipseDeriv D s‖ ≤ M * r⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds z hr] with p hp
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] at hs
    have hsI : s ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hs.1.le, hs.2⟩
    have hd : ‖ellipseDeriv D s‖ ≤ M := hM s hsI
    have hinv : ‖ellipseParam D s - p‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr (hcl p hp s)
    rw [norm_mul, norm_inv]
    calc ‖ellipseParam D s - p‖⁻¹ * ‖ellipseDeriv D s‖ ≤ r⁻¹ * M :=
          mul_le_mul hinv hd (norm_nonneg _) (inv_nonneg.2 hr.le)
      _ = M * r⁻¹ := mul_comm _ _
  have hcont : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ContinuousAt (fun p : ℂ => (ellipseParam D s - p)⁻¹ * ellipseDeriv D s) z := by
    refine Filter.Eventually.of_forall (fun s _ => ?_)
    exact ((continuousAt_const.sub continuousAt_id).inv₀ (hne s)).mul continuousAt_const
  exact intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M * r⁻¹)
    hmeas hbd intervalIntegrable_const hcont

/-- The index of a gap cycle is continuous at every point off its range. -/
theorem indexIntegral_continuousAt (D : DiscWithSegment) {z : ℂ} (hz : z ∉ range (gapCycle D)) :
    ContinuousAt (fun p => indexIntegral (gapCycle D) p) z := by
  obtain ⟨r, hr, hcl⟩ := clearance D hz
  have hc := (continuousAt_param D hz).const_mul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  refine hc.congr ?_
  filter_upwards [Metric.ball_mem_nhds z hr] with p hp
  have hpn : p ∉ range (gapCycle D) := by
    rintro ⟨t, ht⟩
    have h1 := hcl p hp (2 * Real.pi * (t : ℝ))
    have h0 : ellipseParam D (2 * Real.pi * (t : ℝ)) = p := ht
    rw [h0, sub_self, norm_zero] at h1
    linarith
  exact (indexIntegral_eq_param D hpn).symm

/-- The index of a gap cycle is constant on the chord `segment ℝ D.a D.b`. -/
theorem index_const_on_chord (D : DiscWithSegment) {z : ℂ} (hz : z ∈ segment ℝ D.a D.b) :
    indexIntegral (gapCycle D) z = indexIntegral (gapCycle D) D.midpoint := by
  have hSc : segment ℝ D.a D.b ⊆ (range (gapCycle D))ᶜ := by
    intro w hw hr
    exact (gapCycle_range D hr).2 hw
  have hcont : ContinuousOn (fun p => indexIntegral (gapCycle D) p) (segment ℝ D.a D.b) :=
    fun w hw => (indexIntegral_continuousAt D (hSc hw)).continuousWithinAt
  have hint : MapsTo (fun p => indexIntegral (gapCycle D) p) (segment ℝ D.a D.b)
      (Set.range (Int.cast : ℤ → ℂ)) := by
    intro w hw
    exact ⟨_, (indexIntegral_int (gapCycle D) (gapCycle_piecewise D) (hSc hw)).2.symm⟩
  exact (convex_segment D.a D.b).isPreconnected.constant_of_mapsTo
    Complex.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hcont hint hz
    (mid_mem_seg D)

end G2037P2CAux

open G2037P2CAux

/-- P2-iii: the gap-cycle index equals one at every point of the own cut `gapSegment φ k`
(the chord of the gap disc `D`, whose endpoints are the gap endpoints of cut `k`). -/
theorem g2037p2c_index_one_on_cut {φ : PotPair} (k : ℤ) (D : DiscWithSegment)
    (ha : D.a = lamMinus φ k) (hb : D.b = lamPlus φ k) :
    ∀ z ∈ gapSegment φ k, indexIntegral (gapCycle D) z = 1 := by
  intro z hz
  have hseg : gapSegment φ k = segment ℝ D.a D.b := by
    unfold gapSegment
    rw [ha, hb]
  rw [hseg] at hz
  rw [index_const_on_chord D hz]
  exact g2037p2_index_midpoint D

end
end NlsGge.GKDefinitionDesign
