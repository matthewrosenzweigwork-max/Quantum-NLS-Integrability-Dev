import NlsGge.Spectral.ActualPhysicalHeightAmplitudeJointParameterBound36V6
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
noncomputable section

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The actual 00-channel full-line L¹ class varies continuously over the
physical endpoint/height rectangle; the source enters through its proved norm
primitive, not through pointwise continuity. -/
theorem actualPhysicalHeightAmplitude00Family36V7_continuous
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    Continuous (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀) := by
  rw [Metric.continuous_iff]
  intro p ε hε
  let C : ℝ := Real.exp (2 * Y₀)
  let M : ℝ := actualPhysicalSourceNormPrimitive35V2 u 1
  have hC : 0 < C := by dsimp [C]; exact Real.exp_pos _
  have hM : 0 ≤ M := by
    dsimp [M, actualPhysicalSourceNormPrimitive35V2]
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ => norm_nonneg _)
  have hGcont : Continuous
      (fun x : Set.Icc (0 : ℝ) 1 => actualPhysicalSourceNormPrimitive35V2 u x) :=
    (actualPhysicalSourceNormPrimitive35V2_continuousOn u).domRestrict
  have hGat0 : ContinuousAt
      (fun x : Set.Icc (0 : ℝ) 1 => actualPhysicalSourceNormPrimitive35V2 u x) p.1 := by
    exact hGcont.continuousAt
  have hGat := Metric.continuousAt_iff.mp hGat0
    (ε / (2 * C)) (div_pos hε (by positivity))
  obtain ⟨δG, hδG, hGsmall⟩ := hGat
  let δY : ℝ := ε / (4 * C * (M + 1))
  have hδY : 0 < δY := by
    dsimp [δY]
    positivity
  let δ : ℝ := min δG δY
  have hδ : 0 < δ := lt_min hδG hδY
  refine ⟨δ, hδ, ?_⟩
  intro q hdist
  have hdistG : dist q.1 p.1 < δG := by
    apply lt_of_le_of_lt ?_ (lt_of_lt_of_le hdist (min_le_left _ _))
    change dist q.1 p.1 ≤ max (dist q.1 p.1) (dist q.2 p.2)
    exact le_max_left _ _
  have hdistY : dist q.2 p.2 < δY := by
    apply lt_of_le_of_lt ?_ (lt_of_lt_of_le hdist (min_le_right _ _))
    change dist q.2 p.2 ≤ max (dist q.1 p.1) (dist q.2 p.2)
    exact le_max_right _ _
  have hGsmall' :
      |actualPhysicalSourceNormPrimitive35V2 u q.1 -
        actualPhysicalSourceNormPrimitive35V2 u p.1| < ε / (2 * C) := by
    simpa [Real.dist_eq] using hGsmall (x := q.1) hdistG
  have hYsmall : |((q.2 : ℝ) - (p.2 : ℝ))| < δY := by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hdistY
  have hYsmall' : |((p.2 : ℝ) - (q.2 : ℝ))| < δY := by
    simpa only [abs_sub_comm] using hYsmall
  have hbound := actualPhysicalHeightAmplitude00Family36V6_dist_bound
    u Y₀ hY₀ p q
  have hterm₁ : C *
      |actualPhysicalSourceNormPrimitive35V2 u p.1 -
        actualPhysicalSourceNormPrimitive35V2 u q.1| < ε / 2 := by
    have hsymm := abs_sub_comm
      (actualPhysicalSourceNormPrimitive35V2 u p.1)
      (actualPhysicalSourceNormPrimitive35V2 u q.1)
    calc
      _ = C * |actualPhysicalSourceNormPrimitive35V2 u q.1 -
            actualPhysicalSourceNormPrimitive35V2 u p.1| := by rw [hsymm]
      _ < C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hGsmall' hC
      _ = ε / 2 := by dsimp [C]; field_simp
  have hterm₂ :
      2 * C * |((p.2 : ℝ) - (q.2 : ℝ))| * M ≤ ε / 2 := by
    have hcoeff : 0 ≤ 2 * C * M := by positivity
    have hmul :
        2 * C * |((p.2 : ℝ) - (q.2 : ℝ))| * M ≤ 2 * C * δY * M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_of_lt hYsmall') (by positivity)) hM
    calc
      _ ≤ 2 * C * δY * M := hmul
      _ = (ε / 2) * (M / (M + 1)) := by
        dsimp [δY]
        field_simp
        <;> ring
      _ ≤ ε / 2 := by
        apply mul_le_of_le_one_right (by positivity : 0 ≤ ε / 2)
        exact (div_le_one (by linarith [hM])).2 (by linarith)
  calc
    dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ q)
        (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ p)
        ≤ C * |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| +
          2 * C * |((p.2 : ℝ) - (q.2 : ℝ))| * M := by
            simpa [C, M, dist_comm] using hbound
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hterm₁ hterm₂
    _ = ε := by ring

/-- Compactness of the actual 00-channel family follows from the physical
parameter rectangle and the preceding continuity result. -/
theorem actualPhysicalHeightAmplitude00Family36V7_isCompact_range
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    IsCompact (Set.range (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀)) :=
  isCompact_range (actualPhysicalHeightAmplitude00Family36V7_continuous u Y₀ hY₀)

/-- The actual 11-channel full-line L¹ class is continuous in the same physical
parameters, retaining the unstarred source and negative-height convention. -/
theorem actualPhysicalHeightAmplitude11Family36V7_continuous
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    Continuous (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀) := by
  rw [Metric.continuous_iff]
  intro p ε hε
  let C : ℝ := Real.exp (2 * Y₀)
  let M : ℝ := actualPhysicalSourceNormPrimitive35V2 u 1
  have hC : 0 < C := by dsimp [C]; exact Real.exp_pos _
  have hM : 0 ≤ M := by
    dsimp [M, actualPhysicalSourceNormPrimitive35V2]
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ => norm_nonneg _)
  have hGcont : Continuous
      (fun x : Set.Icc (0 : ℝ) 1 => actualPhysicalSourceNormPrimitive35V2 u x) :=
    (actualPhysicalSourceNormPrimitive35V2_continuousOn u).domRestrict
  have hGat0 : ContinuousAt
      (fun x : Set.Icc (0 : ℝ) 1 => actualPhysicalSourceNormPrimitive35V2 u x) p.1 := by
    exact hGcont.continuousAt
  have hGat := Metric.continuousAt_iff.mp hGat0
    (ε / (2 * C)) (div_pos hε (by positivity))
  obtain ⟨δG, hδG, hGsmall⟩ := hGat
  let δY : ℝ := ε / (4 * C * (M + 1))
  have hδY : 0 < δY := by
    dsimp [δY]
    positivity
  let δ : ℝ := min δG δY
  have hδ : 0 < δ := lt_min hδG hδY
  refine ⟨δ, hδ, ?_⟩
  intro q hdist
  have hdistG : dist q.1 p.1 < δG := by
    apply lt_of_le_of_lt ?_ (lt_of_lt_of_le hdist (min_le_left _ _))
    change dist q.1 p.1 ≤ max (dist q.1 p.1) (dist q.2 p.2)
    exact le_max_left _ _
  have hdistY : dist q.2 p.2 < δY := by
    apply lt_of_le_of_lt ?_ (lt_of_lt_of_le hdist (min_le_right _ _))
    change dist q.2 p.2 ≤ max (dist q.1 p.1) (dist q.2 p.2)
    exact le_max_right _ _
  have hGsmall' :
      |actualPhysicalSourceNormPrimitive35V2 u q.1 -
        actualPhysicalSourceNormPrimitive35V2 u p.1| < ε / (2 * C) := by
    simpa [Real.dist_eq] using hGsmall (x := q.1) hdistG
  have hYsmall : |((q.2 : ℝ) - (p.2 : ℝ))| < δY := by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hdistY
  have hYsmall' : |((p.2 : ℝ) - (q.2 : ℝ))| < δY := by
    simpa only [abs_sub_comm] using hYsmall
  have hbound := actualPhysicalHeightAmplitude11Family36V6_dist_bound
    u Y₀ hY₀ p q
  have hterm₁ : C *
      |actualPhysicalSourceNormPrimitive35V2 u p.1 -
        actualPhysicalSourceNormPrimitive35V2 u q.1| < ε / 2 := by
    have hsymm := abs_sub_comm
      (actualPhysicalSourceNormPrimitive35V2 u p.1)
      (actualPhysicalSourceNormPrimitive35V2 u q.1)
    calc
      _ = C * |actualPhysicalSourceNormPrimitive35V2 u q.1 -
            actualPhysicalSourceNormPrimitive35V2 u p.1| := by rw [hsymm]
      _ < C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hGsmall' hC
      _ = ε / 2 := by dsimp [C]; field_simp
  have hterm₂ :
      2 * C * |((p.2 : ℝ) - (q.2 : ℝ))| * M ≤ ε / 2 := by
    have hcoeff : 0 ≤ 2 * C * M := by positivity
    have hmul :
        2 * C * |((p.2 : ℝ) - (q.2 : ℝ))| * M ≤ 2 * C * δY * M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_of_lt hYsmall') (by positivity)) hM
    calc
      _ ≤ 2 * C * δY * M := hmul
      _ = (ε / 2) * (M / (M + 1)) := by
        dsimp [δY]
        field_simp
        <;> ring
      _ ≤ ε / 2 := by
        apply mul_le_of_le_one_right (by positivity : 0 ≤ ε / 2)
        exact (div_le_one (by linarith [hM])).2 (by linarith)
  calc
    dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ q)
        (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
        ≤ C * |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| +
          2 * C * |((p.2 : ℝ) - (q.2 : ℝ))| * M := by
            simpa [C, M, dist_comm] using hbound
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hterm₁ hterm₂
    _ = ε := by ring

theorem actualPhysicalHeightAmplitude11Family36V7_isCompact_range
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    IsCompact (Set.range (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀)) :=
  isCompact_range (actualPhysicalHeightAmplitude11Family36V7_continuous u Y₀ hY₀)

end NlsGge.SpectralFoundations
end
