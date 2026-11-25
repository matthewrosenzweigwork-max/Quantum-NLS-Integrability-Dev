import Mathlib
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.ActionGradientQuotient
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup1
import NlsGge.Atomic.G1.G1081Sup2

/- G1-081 S4 / L2 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/S4L2.lean.
   `singleGapField_local_complex_extension` (Pro round 14 Cluster 2 text, verbatim head): the complex-linear conjugate Riesz map
   rieszPairC (Sup1's rieszPair is its restrictScalars R), the C-analytic composite
   G phi = spectralDiscrimHamField38 phi (muSeq phi n) on the open set gkW, and the real-slice identity from Sup2/muSeq_eq_gkMu38. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.PoissonSpectral38
open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1081S4L2
noncomputable section

theorem star_smul_complex (c : ℂ) (f : PhysicalL2) : star (c • f) = (starRingEnd ℂ c) • star f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_smul c f, MeasureTheory.Lp.coeFn_star (c • f),
    MeasureTheory.Lp.coeFn_smul ((starRingEnd ℂ) c) (star f), MeasureTheory.Lp.coeFn_star f]
    with x h1 h2 h3 h4
  simp only [h2, h3, Pi.star_apply, h1, Pi.smul_apply, h4, smul_eq_mul, star_mul']
  rfl

/-- Complex-linear conjugate Riesz map `ℓ ↦ star (toDual⁻¹ ℓ)`. -/
def rieszStarCLC : (PhysicalL2 →L[ℂ] ℂ) →L[ℂ] PhysicalL2 :=
  LinearMap.mkContinuous
    { toFun := fun ℓ => starLp ((InnerProductSpace.toDual ℂ PhysicalL2).symm ℓ)
      map_add' := fun a b => by simp
      map_smul' := fun c ℓ => by
        simp only [RingHom.id_apply]
        rw [LinearIsometryEquiv.map_smulₛₗ]
        change star ((starRingEnd ℂ) c • (InnerProductSpace.toDual ℂ PhysicalL2).symm ℓ) =
          c • star ((InnerProductSpace.toDual ℂ PhysicalL2).symm ℓ)
        rw [star_smul_complex]; simp }
    1 (fun ℓ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometry.norm_map,
        LinearIsometryEquiv.norm_map, one_mul]
      exact le_rfl)

def rieszPairC : (PotPair →L[ℂ] ℂ) →L[ℂ] PotPair :=
  (rieszStarCLC.comp ((ContinuousLinearMap.compL ℂ PhysicalL2 PotPair ℂ).flip
      (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2))).prod
    (rieszStarCLC.comp ((ContinuousLinearMap.compL ℂ PhysicalL2 PotPair ℂ).flip
      (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)))

theorem rieszPairC_eq (ℓ : PotPair →L[ℂ] ℂ) :
    rieszPairC ℓ = NlsGge.Atomic.G1081Sup1.rieszPair ℓ := rfl

theorem gradDiscrimL2_eq_rieszPairC (φ : PotPair) (z : ℂ) :
    gradDiscrimL2 φ z = rieszPairC (gradDiscrimCLM φ z) := by
  rw [NlsGge.Atomic.G1081Sup1.gradDiscrimL2_eq_rieszPair]; rfl

theorem analyticOnNhd_gradDiscrimL2_complex :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2) univ := by
  have he : (fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2) =
      fun p : PotPair × ℂ => rieszPairC (gradDiscrimCLM p.1 p.2) := by
    funext p; exact gradDiscrimL2_eq_rieszPairC p.1 p.2
  rw [he]
  intro p hp
  exact (rieszPairC.analyticAt _).comp
    (NlsGge.GK38.ActionGradient.gradDiscrim_joint_analytic p hp)

/-- The complex extension of the single-gap field at the Dirichlet label `n`. -/
def gapFieldC (n : ℤ) (φ : PotPair) : PotPair :=
  spectralDiscrimHamField38 φ (muSeq φ n)

theorem analyticAt_gapFieldC (n : ℤ) {φ : PotPair} (hφ : φ ∈ gkW) :
    AnalyticAt ℂ (gapFieldC n) φ := by
  have h1 : AnalyticAt ℂ (fun ψ : PotPair => ((ψ, muSeq ψ n) : PotPair × ℂ)) φ :=
    analyticAt_id.prod (NlsGge.GK38.angleDirichlet_analytic_derivative38 φ hφ n).1
  have hg : AnalyticAt ℂ (fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2) (φ, muSeq φ n) :=
    analyticOnNhd_gradDiscrimL2_complex _ (mem_univ _)
  have h2 : AnalyticAt ℂ (fun ψ : PotPair => gradDiscrimL2 ψ (muSeq ψ n)) φ :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2)
      (f := fun ψ : PotPair => ((ψ, muSeq ψ n) : PotPair × ℂ)) hg h1
  have hfst : AnalyticAt ℂ (fun ψ : PotPair => (gradDiscrimL2 ψ (muSeq ψ n)).1) φ :=
    AnalyticAt.comp (g := ⇑(ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2))
      (f := fun ψ : PotPair => gradDiscrimL2 ψ (muSeq ψ n))
      ((ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2).analyticAt _) h2
  have hsnd : AnalyticAt ℂ (fun ψ : PotPair => (gradDiscrimL2 ψ (muSeq ψ n)).2) φ :=
    AnalyticAt.comp (g := ⇑(ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2))
      (f := fun ψ : PotPair => gradDiscrimL2 ψ (muSeq ψ n))
      ((ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2).analyticAt _) h2
  have hA : AnalyticAt ℂ (fun ψ : PotPair => (-Complex.I) • (gradDiscrimL2 ψ (muSeq ψ n)).2) φ :=
    AnalyticAt.comp (g := fun x : PhysicalL2 => (-Complex.I) • x)
      (f := fun ψ : PotPair => (gradDiscrimL2 ψ (muSeq ψ n)).2)
      (((-Complex.I) • ContinuousLinearMap.id ℂ PhysicalL2).analyticAt _) hsnd
  have hB : AnalyticAt ℂ (fun ψ : PotPair => Complex.I • (gradDiscrimL2 ψ (muSeq ψ n)).1) φ :=
    AnalyticAt.comp (g := fun x : PhysicalL2 => Complex.I • x)
      (f := fun ψ : PotPair => (gradDiscrimL2 ψ (muSeq ψ n)).1)
      ((Complex.I • ContinuousLinearMap.id ℂ PhysicalL2).analyticAt _) hfst
  exact hA.prod hB

theorem gapFieldC_realSlice (n : ℤ) (v : PhysicalL2) :
    gapFieldC n (realSlice v) = realSlice (singleGapField n v) := by
  unfold gapFieldC
  rw [NlsGge.GK38.muSeq_eq_gkMu38, NlsGge.Atomic.G1081Sup2.realSlice_singleGapField]

theorem singleGapField_local_complex_extension (n : ℤ) (u : PhysicalL2) :
  ∃ (r : ℝ) (G : PotPair → PotPair), 0 < r ∧
    AnalyticOnNhd ℂ G (Metric.ball (realSlice u) r) ∧
    ∀ v : PhysicalL2, realSlice v ∈ Metric.ball (realSlice u) r →
      G (realSlice v) = realSlice (singleGapField n v) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_gkW (realSlice u) (realSlice_mem_gkW u)
  exact ⟨r, gapFieldC n, hr, fun φ hφ => analyticAt_gapFieldC n (hsub hφ),
    fun v _ => gapFieldC_realSlice n v⟩

end
end NlsGge.Atomic.G1081S4L2
