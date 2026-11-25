import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Birkhoff.S01Translation38
import NlsGge.Birkhoff.F01Determinant38
import NlsGge.NLS38.SeqConv38
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace NlsGge.Atomic.Common

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

/-- Actual period-one physical L2 fields whose reflected Fourier sequence is finitely supported. -/
def physicalFourierPolynomialSubmodule38 : Submodule ℝ PhysicalL2 where
  carrier := {u | {n : ℤ | fourierSeq38 u n ≠ 0}.Finite}
  zero_mem' := by
    change {n : ℤ | fourierSeq38 (0 : PhysicalL2) n ≠ 0}.Finite
    simp [fourierSeq38_zero38]
  add_mem' := by
    intro u v hu hv
    apply (hu.union hv).subset
    intro n hn
    change fourierSeq38 (u + v) n ≠ 0 at hn
    rw [fourierSeq38_add38] at hn
    change n ∈ {k : ℤ | fourierSeq38 u k ≠ 0} ∪ {k : ℤ | fourierSeq38 v k ≠ 0}
    by_contra h
    simp only [Set.mem_union, not_or] at h
    simp only [Set.mem_ofPred_eq, not_not] at h
    rw [h.1, h.2] at hn
    exact hn (by simp)
  smul_mem' := by
    intro c u hu
    apply hu.subset
    intro n hn
    change fourierSeq38 ((c : ℂ) • u) n ≠ 0 at hn
    rw [fourierSeq38_smul38] at hn
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    rw [h] at hn
    simp at hn

/-- The r-indexed wrapper permits the norm to be induced from the corresponding h^r carrier. -/
structure PhysicalFourierPolynomial38 (r : ℝ) where
  toPhysicalSubmodule : physicalFourierPolynomialSubmodule38

/-- Forget the wrapper and retain the actual physical field. -/
abbrev physicalFourierPolynomialField38 {r : ℝ} (p : PhysicalFourierPolynomial38 r) : PhysicalL2 :=
  p.toPhysicalSubmodule.1

def physicalFourierPolynomial38EquivSubmodule (r : ℝ) :
    PhysicalFourierPolynomial38 r ≃ physicalFourierPolynomialSubmodule38 where
  toFun p := p.toPhysicalSubmodule
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv p := rfl

instance physicalFourierPolynomial38AddCommGroup (r : ℝ) : AddCommGroup (PhysicalFourierPolynomial38 r) :=
  (physicalFourierPolynomial38EquivSubmodule r).addCommGroup

def physicalFourierPolynomial38AddEquivSubmodule (r : ℝ) :
    PhysicalFourierPolynomial38 r ≃+ physicalFourierPolynomialSubmodule38 where
  toEquiv := physicalFourierPolynomial38EquivSubmodule r
  map_add' _ _ := rfl

instance physicalFourierPolynomial38Module (r : ℝ) : Module ℝ (PhysicalFourierPolynomial38 r) :=
  (physicalFourierPolynomial38AddEquivSubmodule r).module ℝ

def physicalFourierPolynomial38LinearEquivSubmodule (r : ℝ) :
    PhysicalFourierPolynomial38 r ≃ₗ[ℝ] physicalFourierPolynomialSubmodule38 where
  toFun p := p.toPhysicalSubmodule
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' c p := by
    apply Subtype.ext
    rfl

/-- The actual Fourier polynomial represented in the coherent real h^r carrier. -/
def physicalFourierPolynomialToCarrier38 (r : ℝ) :
    PhysicalFourierPolynomial38 r →ₗ[ℝ] SobolevCarrier38 r where
  toFun p := by
    have hp0 : (p.toPhysicalSubmodule : PhysicalL2) ∈ physicalFourierPolynomialSubmodule38 :=
      p.toPhysicalSubmodule.property
    have hp : {n : ℤ | fourierSeq38 (physicalFourierPolynomialField38 p) n ≠ 0}.Finite := by
      change {n : ℤ | fourierSeq38 (p.toPhysicalSubmodule : PhysicalL2) n ≠ 0}.Finite at hp0
      simpa [physicalFourierPolynomialField38] using hp0
    exact carrierMk38 r (fourierSeq38 (physicalFourierPolynomialField38 p))
      (finiteSupport_mem_seqSobolev38 r _ hp)
  map_add' p q := by
    apply carrierExt38
    funext n
    simp only [carrierCoe38_mk]
    have hpq := (physicalFourierPolynomial38LinearEquivSubmodule r).map_add p q
    have hpqf := congrArg (fun z : physicalFourierPolynomialSubmodule38 => (z : PhysicalL2)) hpq
    change fourierSeq38 ((p + q).toPhysicalSubmodule : PhysicalL2) n = _
    have hpq' : (p + q).toPhysicalSubmodule = p.toPhysicalSubmodule + q.toPhysicalSubmodule := by
      change (p + q).toPhysicalSubmodule = p.toPhysicalSubmodule + q.toPhysicalSubmodule at hpq
      exact hpq
    change fourierSeq38 ((p + q).toPhysicalSubmodule : PhysicalL2) n =
      fourierSeq38 (p.toPhysicalSubmodule : PhysicalL2) n +
        fourierSeq38 (q.toPhysicalSubmodule : PhysicalL2) n
    rw [hpq', Submodule.coe_add, fourierSeq38_add38]
  map_smul' c p := by
    apply carrierExt38
    funext n
    simp only [carrierCoe38_mk]
    have hsmul := (physicalFourierPolynomial38LinearEquivSubmodule r).map_smul c p
    have hsmulf := congrArg (fun z : physicalFourierPolynomialSubmodule38 => (z : PhysicalL2)) hsmul
    change fourierSeq38 ((c • p).toPhysicalSubmodule : PhysicalL2) n = _
    have hsmul' : (c • p).toPhysicalSubmodule = c • p.toPhysicalSubmodule := by
      change (c • p).toPhysicalSubmodule = c • p.toPhysicalSubmodule at hsmul
      exact hsmul
    change fourierSeq38 ((c • p).toPhysicalSubmodule : PhysicalL2) n =
      (c : ℂ) * fourierSeq38 (p.toPhysicalSubmodule : PhysicalL2) n
    rw [hsmul', Submodule.coe_smul]
    change fourierSeq38 ((c : ℂ) • (p.toPhysicalSubmodule : PhysicalL2)) n = _
    rw [fourierSeq38_smul38]

 theorem physicalFourierPolynomialToCarrier38_injective (r : ℝ) :
    Function.Injective (physicalFourierPolynomialToCarrier38 r) := by
  intro p q h
  have hseq : fourierSeq38 (physicalFourierPolynomialField38 p) =
      fourierSeq38 (physicalFourierPolynomialField38 q) := by
    funext n
    have h' := congrArg (carrierCoe38 r) h
    simpa [physicalFourierPolynomialToCarrier38] using congrFun h' n
  have hfield := fourierSeq38_injective hseq
  apply (physicalFourierPolynomial38EquivSubmodule r).injective
  exact Subtype.ext hfield

instance physicalFourierPolynomial38NormedAddCommGroup (r : ℝ) :
    NormedAddCommGroup (PhysicalFourierPolynomial38 r) :=
  NormedAddCommGroup.induced _ _ (physicalFourierPolynomialToCarrier38 r)
    (physicalFourierPolynomialToCarrier38_injective r)

instance physicalFourierPolynomial38NormedSpace (r : ℝ) :
    NormedSpace ℝ (PhysicalFourierPolynomial38 r) where
  norm_smul_le c p := by
    change ‖physicalFourierPolynomialToCarrier38 r (c • p)‖ ≤
      ‖c‖ * ‖physicalFourierPolynomialToCarrier38 r p‖
    rw [map_smul]
    exact norm_smul_le c (physicalFourierPolynomialToCarrier38 r p)

/-- The isometric Fourier map on finite physical Fourier polynomials. -/
def physicalFourierPolynomialIsometry38 (r : ℝ) :
    PhysicalFourierPolynomial38 r →ₗᵢ[ℝ] SobolevCarrier38 r where
  toLinearMap := physicalFourierPolynomialToCarrier38 r
  norm_map' _ := rfl

/-- Physical H^r is defined as the completion of actual finite period-one Fourier polynomials. -/
abbrev PhysicalSobolev38 (r : ℝ) := UniformSpace.Completion (PhysicalFourierPolynomial38 r)

private def polynomialOfProjection38 (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    PhysicalFourierPolynomial38 r := by
  let z : ℤ → ℂ := carrierCoe38 r (projC38 r N x)
  have hfinite : {n : ℤ | z n ≠ 0}.Finite := by
    apply (symmetricModes N).finite_toSet.subset
    intro n hn
    have hnz : carrierCoe38 r (projC38 r N x) n ≠ 0 := by simpa [z] using hn
    rw [carrierCoe38_projC38] at hnz
    by_contra hout
    by_cases hnmem : n ∈ symmetricModes N
    · exact hout hnmem
    · simp [hnmem] at hnz
  have hz0 : z ∈ seqSobolev38 0 := finiteSupport_mem_seqSobolev38 0 z hfinite
  let u : PhysicalL2 := physInv38 z hz0
  have hu : {n : ℤ | fourierSeq38 u n ≠ 0}.Finite := by
    rw [fourierSeq38_physInv38]
    exact hfinite
  exact ⟨⟨u, hu⟩⟩

theorem physicalFourierPolynomialToCarrier38_proj (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    physicalFourierPolynomialToCarrier38 r (polynomialOfProjection38 r N x) = projC38 r N x := by
  apply carrierExt38
  funext n
  change fourierSeq38 (physicalFourierPolynomialField38 (polynomialOfProjection38 r N x)) n =
    carrierCoe38 r (projC38 r N x) n
  have hcoeff : fourierSeq38 (physicalFourierPolynomialField38 (polynomialOfProjection38 r N x)) =
      fun n => carrierCoe38 r (projC38 r N x) n := by
    funext k
    unfold polynomialOfProjection38
    simp only [physicalFourierPolynomialField38, fourierSeq38_physInv38]
  rw [congrFun hcoeff n, carrierCoe38_projC38]

theorem physicalFourierPolynomialToCarrier38_denseRange (r : ℝ) :
    DenseRange (physicalFourierPolynomialIsometry38 r) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hevent : ∀ᶠ N : ℕ in atTop, projC38 r N x ∈ Metric.ball x ε :=
    (tendsto_projC38 r x) (Metric.ball_mem_nhds x hε)
  obtain ⟨N, hN⟩ := hevent.exists
  refine ⟨polynomialOfProjection38 r N x, ?_⟩
  simpa [physicalFourierPolynomialIsometry38,
    physicalFourierPolynomialToCarrier38_proj, dist_comm] using (Metric.mem_ball.mp hN)

/-- The completion Fourier transform into the actual coherent h^r carrier. -/
def physicalSobolevFourier38 (r : ℝ) :
    PhysicalSobolev38 r →ₗᵢ[ℝ] SobolevCarrier38 r :=
  (physicalFourierPolynomialIsometry38 r).fromCompletion

theorem physicalSobolevFourier38_coe (r : ℝ) (p : PhysicalFourierPolynomial38 r) :
    physicalSobolevFourier38 r p = physicalFourierPolynomialToCarrier38 r p :=
  LinearIsometry.fromCompletion_apply_coe (physicalFourierPolynomialIsometry38 r) p

theorem physicalSobolevFourier38_denseRange (r : ℝ) : DenseRange (physicalSobolevFourier38 r) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨p, hp⟩ := (Metric.denseRange_iff.mp
    (physicalFourierPolynomialToCarrier38_denseRange r)) x ε hε
  refine ⟨p, ?_⟩
  rw [physicalSobolevFourier38_coe]
  exact hp

theorem physicalSobolevFourier38_surjective (r : ℝ) :
    Function.Surjective (physicalSobolevFourier38 r) := by
  let f := physicalSobolevFourier38 r
  have hclosed : IsClosed (Set.range f) := f.isometry.isClosedEmbedding.isClosed_range
  have hdense : closure (Set.range f) = Set.univ :=
    denseRange_iff_closure_range.mp (physicalSobolevFourier38_denseRange r)
  have hrange : Set.range f = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense
  intro y
  have hy : y ∈ Set.range f := by rw [hrange]; simp
  exact Set.mem_range.mp hy

/-- Fourier realizes the completed physical H^r space as the coherent sequence h^r Hilbert space. -/
def physicalSobolevFourierEquiv38 (r : ℝ) :
    PhysicalSobolev38 r ≃ₗᵢ[ℝ] SobolevCarrier38 r :=
  LinearIsometryEquiv.ofSurjective (physicalSobolevFourier38 r)
    (physicalSobolevFourier38_surjective r)

theorem physicalSobolevFourierEquiv38_coe (r : ℝ) (p : PhysicalFourierPolynomial38 r) :
    physicalSobolevFourierEquiv38 r p = physicalFourierPolynomialToCarrier38 r p :=
  physicalSobolevFourier38_coe r p

theorem physicalSobolevFourierEquiv38_polynomialCoeff (r : ℝ)
    (p : PhysicalFourierPolynomial38 r) (n : ℤ) :
    carrierCoe38 r (physicalSobolevFourierEquiv38 r p) n =
      fourierSeq38 (physicalFourierPolynomialField38 p) n := by
  rw [physicalSobolevFourierEquiv38_coe, physicalFourierPolynomialToCarrier38]
  rfl

end NlsGge.Atomic.Common
