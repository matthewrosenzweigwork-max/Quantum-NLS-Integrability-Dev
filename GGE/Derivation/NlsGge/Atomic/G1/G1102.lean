import Mathlib
import NlsGge.Atomic.G1.G1083Host
import NlsGge.Atomic.G1.G1083Sup2
import NlsGge.Atomic.G1.G1084
import NlsGge.Atomic.G1.G1100
import NlsGge.Atomic.G1.G1051
import NlsGge.Atomic.G1.G1082Sup6

/- G1-102 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1102.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from root/gpt6pro_followup11 STATEMENTS/G1.md section G1-102.
   Route: normingFactor = (discrim + antiDiscrim)/2 pointwise, so on isospectralSet u the signed norming (hence realKappa38 and the early
   coordinates) are functions of the signed Dirichlet datum; G1-100 (injectivity of normingDirichletMap) gives injectivity of the datum;
   continuous bijection compact -> T2 is a homeomorphism (G1-084 for continuity/surjectivity); each gap circle is the continuous image of R
   under t |-> datum along the flow (G1083Sup2 covering), the product of connected sets is connected. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem normingFactor_eq_half_sum (φ : PotPair) (z : ℂ) :
    normingFactor φ z = (discrim φ z + antiDiscrim φ z) / 2 := by
  obtain ⟨e1, e2, -⟩ := NlsGge.Atomic.G1051S3.entries φ z
  unfold normingFactor
  rw [e1, e2]; ring

theorem signedDirichletData_injOn (u : PhysicalL2) :
    InjOn signedDirichletData (isospectralSet u) := by
  intro v hv w hw hE
  have hg : ∀ n, gkMu v n = gkMu w n := fun n => congrArg Prod.fst (congrFun hE n)
  have hd : ∀ n, deltaMu v n = deltaMu w n := fun n => congrArg Prod.snd (congrFun hE n)
  have hΔv : discrim (realSlice v) = discrim (realSlice u) := funext (show isospectral u v from hv)
  have hΔw : discrim (realSlice w) = discrim (realSlice u) := funext (show isospectral u w from hw)
  have hnf : ∀ n, normingFactor (realSlice v) (gkMu v n : ℂ) = normingFactor (realSlice w) (gkMu w n : ℂ) := by
    intro n
    rw [normingFactor_eq_half_sum, normingFactor_eq_half_sum, antiDiscrim_eq_deltaMu38, antiDiscrim_eq_deltaMu38,
      hΔv, hΔw, hg n, hd n]
  have hE2 : earlyCoordinates v = earlyCoordinates w := by
    funext n
    have hnf' : normingFactor (realSlice v) (gkMu w n : ℂ) = normingFactor (realSlice w) (gkMu w n : ℂ) := by
      have h := hnf n
      rwa [hg n] at h
    simp only [earlyCoordinates, realKappa38, signedNorming38, hg n, hnf']
  have hN : normingDirichletMap v = normingDirichletMap w := by
    unfold normingDirichletMap
    rw [hE2]
  exact NlsGge.Atomic.G1100.G1_100 hN

theorem gapCircle_eq_range_flow (n : ℤ) (u : PhysicalL2) :
    gapCircle u n = range (fun t : ℝ => signedDirichletData (singleGapFlow n t u) n) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht⟩ := exists_flow_hit n u p hp
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    exact signedDirichletData_mem_gapCircle (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n t u) n

theorem isConnected_gapCircle (n : ℤ) (u : PhysicalL2) : IsConnected (gapCircle u n) := by
  rw [gapCircle_eq_range_flow n u]
  exact isConnected_range
    (((continuous_apply n).comp continuous_signedDirichletData).comp
      (NlsGge.Atomic.G1082Sup6.continuous_flow n u))

theorem gapCircleProduct_eq_pi (u : PhysicalL2) :
    gapCircleProduct u = Set.pi univ (fun n : ℤ => gapCircle u n) := by
  ext p; simp [gapCircleProduct]

theorem G1_102 (u : PhysicalL2) :
    (∃ e : {v : PhysicalL2 // v ∈ isospectralSet u} ≃ₜ
        {p : ℤ → ℝ × ℝ // p ∈ gapCircleProduct u},
      ∀ v, (e v).1 = signedDirichletData v.1) ∧
    IsConnected (isospectralSet u) := by
  have h84 := G1_084 u
  have hK : IsCompact (isospectralSet u) := (G1_080 u).1
  haveI : CompactSpace {v : PhysicalL2 // v ∈ isospectralSet u} := isCompact_iff_compactSpace.mp hK
  let f : {v : PhysicalL2 // v ∈ isospectralSet u} → {p : ℤ → ℝ × ℝ // p ∈ gapCircleProduct u} :=
    fun v => ⟨signedDirichletData v.1, fun n => signedDirichletData_mem_gapCircle v.2 n⟩
  have hfc : Continuous f :=
    Continuous.subtype_mk (continuous_signedDirichletData.comp continuous_subtype_val) _
  have hfi : Function.Injective f := fun v w h =>
    Subtype.ext (signedDirichletData_injOn u v.2 w.2 (congrArg Subtype.val h))
  have hfs : Function.Surjective f := fun p => by
    obtain ⟨v, hv, hvp⟩ := h84.2.2 p.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvp⟩
  let e : {v : PhysicalL2 // v ∈ isospectralSet u} ≃ₜ {p : ℤ → ℝ × ℝ // p ∈ gapCircleProduct u} :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩) hfc
  refine ⟨⟨e, fun v => rfl⟩, ?_⟩
  have hconn : IsConnected (gapCircleProduct u) := by
    rw [gapCircleProduct_eq_pi]
    exact isConnected_univ_pi.2 fun n => isConnected_gapCircle n u
  haveI : ConnectedSpace {p : ℤ → ℝ × ℝ // p ∈ gapCircleProduct u} := isConnected_iff_connectedSpace.1 hconn
  have hr : isospectralSet u = range (fun c : {p : ℤ → ℝ × ℝ // p ∈ gapCircleProduct u} => (e.symm c).1) := by
    ext v
    constructor
    · intro hv; exact ⟨e ⟨v, hv⟩, by simp⟩
    · rintro ⟨c, rfl⟩; exact (e.symm c).2
  rw [hr]
  exact isConnected_range (continuous_subtype_val.comp e.symm.continuous)

end
end NlsGge.GKDefinitionDesign
