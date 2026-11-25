import QuantumNLS.Q07CutNeighborhoodR15
import QuantumNLS.PhysicalL2BandGeometry

/-! The compact real-cut estimate on the actual physical L2 space. The
interval profile is a continuous linear image, with its canonical
representative identified almost everywhere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace QuantumNLS.SpatialTransfer.Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid QuantumNLS.SpatialTransfer.Mat2 := NormedAddGroup.toENormedAddMonoid
namespace QuantumNLS.Q07PhysicalProfilesR15
open Q07RealCutsR15

section FiniteMeasure
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def lowerExponent : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 1 μ where
  toFun f := ⟨f.val, Lp.antitone (by norm_num : (1 : ENNReal) ≤ 2) f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lowerExponent_bound (f : Lp ℂ 2 μ) :
    ‖lowerExponent μ f‖ ≤ (μ univ ^ (1 - (2:ℝ)⁻¹)).toReal * ‖f‖ := by
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := (f : X → ℂ)) (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable f)
  have hf : eLpNorm (f : X → ℂ) 2 μ * μ univ ^ (1 - (2:ℝ)⁻¹) ≠ ∞ := by
    apply ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hb' : eLpNorm (f : X → ℂ) 1 μ ≤
      eLpNorm (f : X → ℂ) 2 μ * μ univ ^ (1 - (2:ℝ)⁻¹) := by
    simpa only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one, one_div] using hb
  have h := ENNReal.toReal_mono hf hb' 
  change (eLpNorm (f : X → ℂ) 1 μ).toReal ≤ (μ univ ^ (1 - (2:ℝ)⁻¹)).toReal * ‖f‖
  simpa only [Lp.norm_def, ENNReal.toReal_mul, mul_comm] using h

def lowerExponentCLM : Lp ℂ 2 μ →L[ℂ] Lp ℂ 1 μ :=
  (lowerExponent μ).mkContinuous (μ univ ^ (1 - (2:ℝ)⁻¹)).toReal
    (lowerExponent_bound μ)
end FiniteMeasure

variable {L κ : ℝ} [Fact (0 < L)]
open PhysicalTensor (L2T)

def toProfile : L2T L →L[ℂ] Profile L :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => (x : AddCircle L))
    (by simpa using AddCircle.measurePreserving_mk L 0)).toContinuousLinearMap ∘L
      lowerExponentCLM (volume : Measure (AddCircle L))

theorem toProfile_ae (u : L2T L) :
    (fun x : ℝ => toProfile u x) =ᵐ[volume.restrict (Ioc 0 L)] L2SpatialTransfer.profile u := by
  exact Lp.coeFn_compMeasurePreserving
    (lowerExponentCLM (volume : Measure (AddCircle L)) u)
    (by simpa using AddCircle.measurePreserving_mk L 0)

theorem discriminant_eq (u : L2T L) (t : ℝ) :
    discriminant κ (toProfile u) t = PhysicalL2BandGeometry.d (κ := κ) u t := by
  have hae : (fun x : ℝ => toProfile u x) =ᵐ[volume.restrict (Icc 0 L)] L2SpatialTransfer.profile u := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact toProfile_ae u
  have hA : SpatialTransfer.balCoef κ (fun x => toProfile u x) (t:ℂ) =ᵐ[volume.restrict (Icc 0 L)]
      SpatialTransfer.balCoef κ (L2SpatialTransfer.profile u) (t:ℂ) := by
    filter_upwards [hae] with x hx
    simp only [SpatialTransfer.balCoef, SpatialTransfer.coef, hx]
  have hT := L1SpatialTransfer.transfer_eq_of_ae (Fact.out : 0 < L).le hA
    (x := L) ⟨(Fact.out : 0 < L).le, le_rfl⟩
  change (RootDiscriminantL1.discL1 L κ (fun x => toProfile u x) (t : ℂ)).re = _
  unfold RootDiscriminantL1.discL1 RootDiscriminantL1.TT
  rw [hT]
  rfl

/-- Uniform high-energy real discriminant error on any compact physical
L2 class, derived from the actual transfer. -/
theorem uniform_physical_real_asymptotic {K : Set (L2T L)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ u ∈ K,
      |PhysicalL2BandGeometry.d (κ := κ) u t - 2 * Real.cos (t*L/2)| < ε := by
  have hh := uniform_real_asymptotic (κ := κ) (Fact.out : 0 < L)
    (hK.image toProfile.continuous) hε
  filter_upwards [hh] with t ht u hu
  rw [← discriminant_eq u t]
  exact ht _ (mem_image_of_mem toProfile hu)

open PROP017UniformN (cutSeq)

/-- The actual physical real cuts, uniformly on a compact L2 profile class. -/
theorem uniform_physical_real_cuts {K : Set (L2T L)} (hK : IsCompact K) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K, ∀ a : ℝ,
      (a = cutSeq L l ∨ a = -cutSeq L l) →
      (∀ s : ℝ, |s| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) u (a+s)| < 3/2) ∧
        |PhysicalL2BandGeometry.d (κ := κ) u a| ≤ 1/2 := by
  obtain ⟨l0, hl0⟩ := uniform_real_cuts (κ := κ) (Fact.out : 0 < L)
    (hK.image toProfile.continuous)
  refine ⟨l0, fun l hl u hu a ha => ?_⟩
  simpa only [discriminant_eq] using hl0 l hl _ (mem_image_of_mem toProfile hu) a ha


/-- The accepted density theorem makes a real-cut interval a genuine gap
of the full-mass measure. Zero and nonunit profiles are included. -/
theorem measure_gap_of_real_cut (hκ : 0 < κ) (u : L2T L) {a : ℝ}
    (hs : ∀ s : ℝ, |s| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) u (a+s)| < 3/2) :
    FullMass.Mmeas κ u (Ioo (a-1/L) (a+1/L)) = 0 := by
  by_cases hu : u = 0
  · subst u
    rw [FullMass.Mmeas_zero]
    simp
  rw [← PhysicalL2Normalization.measure_eq_Mmeas hκ u,
    RootDensityIdentification.root_density hκ hu, withDensity_apply _ measurableSet_Ioo]
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0) ?_]
  · simp
  intro x hx
  have hxs : |x-a| < 1/L := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hd := hs (x-a) hxs
  rw [show a+(x-a) = x by ring] at hd
  have hh : RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x:ℂ)).re| = 0 := by
    unfold RootDensity.hfun
    split_ifs with hlt
    · change 2 < |PhysicalL2BandGeometry.d (κ := κ) u x| at hlt
      linarith
    · rfl
  simp [RootDensityIdentification.dens, hh]

/-- Uniform high real cuts and full-mass measure gaps on a compact physical
class. This packages the proved real-cut clauses without a unit-sphere
restriction; the strip and contour-Hessian clauses are not asserted. -/
theorem uniform_physical_measure_cuts (hκ : 0 < κ) {K : Set (L2T L)} (hK : IsCompact K) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K, ∀ a : ℝ,
      (a = cutSeq L l ∨ a = -cutSeq L l) →
      (∀ s : ℝ, |s| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) u (a+s)| < 3/2) ∧
      |PhysicalL2BandGeometry.d (κ := κ) u a| ≤ 1/2 ∧
      FullMass.Mmeas κ u (Ioo (a-1/L) (a+1/L)) = 0 := by
  obtain ⟨l0, hl0⟩ := uniform_physical_real_cuts (κ := κ) hK
  refine ⟨l0, fun l hl u hu a ha => ?_⟩
  obtain ⟨hs, ha0⟩ := hl0 l hl u hu a ha
  exact ⟨hs, ha0, measure_gap_of_real_cut hκ u hs⟩


/-- A fixed physical L2 neighborhood of the compact class has the same
uniform real-cut intervals. -/
theorem uniform_physical_cuts_near {K : Set (L2T L)} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K,
      ∀ v : L2T L, ‖v-u‖ < δ → ∀ a : ℝ,
      (a = cutSeq L l ∨ a = -cutSeq L l) →
      (∀ s : ℝ, |s| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) v (a+s)| < 3/2) ∧
        |PhysicalL2BandGeometry.d (κ := κ) v a| ≤ 1/2 := by
  obtain ⟨η, hη, l0, hl0⟩ := Q07CutNeighborhoodR15.uniform_real_cuts_near
    (κ := κ) (Fact.out : 0 < L) (hK.image toProfile.continuous)
  let C := ‖toProfile (L := L)‖
  have hC : 0 ≤ C := norm_nonneg _
  refine ⟨η/(C+1), by positivity, l0, ?_⟩
  intro l hl u hu v hv a ha
  have hnorm : ‖toProfile v - toProfile u‖ < η := by
    have h1 : ‖v-u‖*(C+1) < η := (lt_div_iff₀ (by positivity : 0 < C+1)).mp hv
    calc
      _ = ‖toProfile (v-u)‖ := by rw [map_sub]
      _ ≤ C*‖v-u‖ := toProfile.le_opNorm _
      _ ≤ ‖v-u‖*(C+1) := by nlinarith [norm_nonneg (v-u)]
      _ < η := h1
  simpa only [discriminant_eq] using
    hl0 l hl _ (mem_image_of_mem toProfile hu) (toProfile v) hnorm a ha

end QuantumNLS.Q07PhysicalProfilesR15
