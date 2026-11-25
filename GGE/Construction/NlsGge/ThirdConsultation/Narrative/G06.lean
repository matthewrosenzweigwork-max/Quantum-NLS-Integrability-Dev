import NlsGge.Ramer.General.RamerGeneral
import NlsGge.Birkhoff.S01Equivariance38
import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.Measure.CountableSupport
import Mathlib.Analysis.Normed.Operator.Extend
import NlsGge.Analysis.RegularizedDeterminant.Det2Transport
import Mathlib.MeasureTheory.Constructions.Polish.Basic

                                                          
                                                                       
                                                                     
                                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology InnerProductSpace
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Measure NlsGge.Ramer
open NlsGge.Sobolev38
open NlsGge.Analysis.RegularizedDeterminant

namespace NlsGge.ThirdConsultation.Narrative

/-- The positive rates of the specified complex product Gaussian. -/
structure SourceGaussianRates where
  q : ℤ → ℝ
  q_pos : ∀ n, 0 < q n

namespace SourceGaussianRates

/-- A rate-only provider for the existing CM/head API. Its E is never used as
    the source E. The auxiliary diagonal form cancels out of H and every head. -/
def cmProvider (r : SourceGaussianRates) : NlsGge.Ramer.General.RamerSetting where
  q := r.q
  q_pos := r.q_pos
  M n := NlsGge.Ramer.General.ModeForm.iso
    (r.q n * japaneseBracket n ^ (-2 : ℝ))
    (mul_pos (r.q_pos n) (Real.rpow_pos_of_pos (japaneseBracket_pos n) _))
  hs := by
    refine (summable_japaneseBracket_rpow_neg 2 (by norm_num)).congr fun n => ?_
    rw [NlsGge.Ramer.General.ModeForm.iso_tr]
    simp only [Real.rpow_eq_pow]
    field_simp [(r.q_pos n).ne'] <;> ring

/-- The actual source Cameron--Martin space, with weight 2q. -/
abbrev H (r : SourceGaussianRates) := r.cmProvider.H

theorem cm_hasSum (r : SourceGaussianRates) (h : r.H) :
    HasSum (fun n : ℤ => 2 * r.q n * ‖r.cmProvider.hcoord h n‖ ^ 2) (‖h‖ ^ 2) :=
  weightedHilbert_hasSum r.cmProvider.cmWeight h

/-- The finite real value of the source CM quadratic energy; cm_hasSum already
    proves finiteness of its nonnegative series on this carrier. -/
def quadraticEnergy (r : SourceGaussianRates) (h : r.H) : ℝ :=
  ∑' n : ℤ, r.q n * ‖r.cmProvider.hcoord h n‖ ^ 2

theorem quadraticEnergy_eq_half_norm_sq (r : SourceGaussianRates) (h : r.H) :
    r.quadraticEnergy h = ‖h‖ ^ 2 / 2 := by
  have hs : HasSum (fun n : ℤ => r.q n * ‖r.cmProvider.hcoord h n‖ ^ 2)
      ((1 / 2 : ℝ) * ‖h‖ ^ 2) :=
    ((r.cm_hasSum h).mul_left (1 / 2 : ℝ)).congr_fun (fun n => by ring)
  exact hs.tsum_eq.trans (by ring)

end SourceGaussianRates

section Setting

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]

/-- The literal standing setting of v2:546-551. E is arbitrary: only symmetric
    cutoffs must be orthogonal. In particular, n and -n may be coupled.
    No divergence, density, conjugacy or approximation conclusion is a field. -/
structure SourceShellGaussianSetting where
  rates : SourceGaussianRates
  toH1 : E →L[ℝ] SobolevCarrier38 1
  toH1_injective : Function.Injective toH1
  gamma : Measure E
  probability : IsProbabilityMeasure gamma
  coordinate_law : gamma.map (fun x : E => carrierCoe38 1 (toH1 x)) =
    countableComplexGaussian rates.q
  full_support : ∀ U : Set E, IsOpen U → U.Nonempty → gamma U ≠ 0
  inclHS : HilbertSchmidt rates.H E
  incl_coordinates : ∀ (h : rates.H) (n : ℤ),
    carrierCoe38 1 (toH1 (HilbertSchmidt.toCLM inclHS h)) n = rates.cmProvider.hcoord h n
  projE : ℕ → E →L[ℝ] E
  proj_coordinates : ∀ (N : ℕ) (x : E) (n : ℤ),
    carrierCoe38 1 (toH1 (projE N x)) n =
      if n ∈ symmetricModes N then carrierCoe38 1 (toH1 x) n else 0
  proj_orthogonal : ∀ (N : ℕ) (x y : E),
    inner ℝ (projE N y) (x - projE N x) = 0
  proj_strong : ∀ x : E, Tendsto (fun N : ℕ => projE N x) atTop (𝓝 x)

end Setting

namespace SourceShellGaussianSetting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable (S : SourceShellGaussianSetting E)

abbrev H := S.rates.H

/-- Coordinates are supplied by the genuine continuous E to h1 inclusion. -/
def coord (x : E) : ℤ → ℂ := carrierCoe38 1 (S.toH1 x)

theorem coord_injective : Function.Injective S.coord := by
  intro x y h
  apply S.toH1_injective
  exact (carrierCoe38_injective 1) h

theorem measurable_coord : Measurable S.coord := by
  refine measurable_pi_iff.2 fun n => ?_
  exact ((coordC38 1 n).continuous.comp S.toH1.continuous).measurable

/-- The inclusion is the actual bounded operator underlying the given HS map. -/
def incl : S.H →L[ℝ] E := HilbertSchmidt.toCLM S.inclHS

theorem incl_injective : Function.Injective S.incl := by
  intro h k hhk
  change S.inclHS.toCLM h = S.inclHS.toCLM k at hhk
  apply S.rates.cmProvider.hcoord_ext
  intro n
  rw [← S.incl_coordinates h n, ← S.incl_coordinates k n, hhk]

theorem incl_isHilbertSchmidt : IsHilbertSchmidt S.incl :=
  HilbertSchmidt.membership S.inclHS

theorem projE_idempotent (N : ℕ) (x : E) : S.projE N (S.projE N x) = S.projE N x := by
  apply S.coord_injective
  funext n
  change carrierCoe38 1 (S.toH1 _) n = carrierCoe38 1 (S.toH1 _) n
  rw [S.proj_coordinates, S.proj_coordinates]
  split_ifs <;> rfl

theorem projE_norm_le (N : ℕ) (x : E) : ‖S.projE N x‖ ≤ ‖x‖ := by
  have h := norm_add_sq_real (S.projE N x) (x - S.projE N x)
  rw [show S.projE N x + (x - S.projE N x) = x by abel,
    S.proj_orthogonal N x x] at h
  nlinarith [sq_nonneg ‖x - S.projE N x‖, norm_nonneg x, norm_nonneg (S.projE N x)]

/-- The same literal symmetric cutoff on the factor-two CM space. -/
def projH (N : ℕ) : S.H →L[ℝ] S.H := S.rates.cmProvider.headProj N

theorem projH_orthogonal (N : ℕ) (h k : S.H) :
    inner ℝ (S.projH N k) (h - S.projH N h) = 0 :=
  weightedRealProjection_range_residual S.rates.cmProvider.cmWeight (symmetricModes N) h k

theorem projH_strong (h : S.H) : Tendsto (fun N : ℕ => S.projH N h) atTop (𝓝 h) :=
  weightedProjection_tendsto S.rates.cmProvider.cmWeight h

theorem projE_incl (N : ℕ) (h : S.H) : S.projE N (S.incl h) = S.incl (S.projH N h) := by
  apply S.coord_injective
  funext n
  calc S.coord (S.projE N (S.incl h)) n
      = (if n ∈ symmetricModes N then S.coord (S.incl h) n else 0) :=
        S.proj_coordinates N (S.incl h) n
    _ = (if n ∈ symmetricModes N then S.rates.cmProvider.hcoord h n else 0) :=
        congrArg (fun z : ℂ => if n ∈ symmetricModes N then z else 0) (S.incl_coordinates h n)
    _ = S.rates.cmProvider.hcoord (S.projH N h) n :=
        (S.rates.cmProvider.hcoord_headProj N h n).symm
    _ = S.coord (S.incl (S.projH N h)) n := (S.incl_coordinates (S.projH N h) n).symm

/-- The CM derivative is an actual Hilbert--Schmidt composition, never a norm proxy. -/
def hDerivative (K : E → S.H) (x : E) : HilbertSchmidt S.H S.H :=
  HilbertSchmidt.postcompose (fderiv ℝ K x) S.inclHS

theorem hDerivative_toCLM (K : E → S.H) (x : E) :
    (S.hDerivative K x).toCLM = (fderiv ℝ K x).comp S.incl := rfl

theorem hDerivative_norm_le (K : E → S.H) (x : E) :
    ‖S.hDerivative K x‖ ≤ ‖fderiv ℝ K x‖ * ‖S.inclHS‖ :=
  HilbertSchmidt.norm_postcompose_le _ _

theorem hDerivative_sub_norm_le (K : E → S.H) (x y : E) :
    ‖S.hDerivative K x - S.hDerivative K y‖ ≤
      ‖fderiv ℝ K x - fderiv ℝ K y‖ * ‖S.inclHS‖ := by
  have he : S.hDerivative K x - S.hDerivative K y =
      HilbertSchmidt.postcompose (fderiv ℝ K x - fderiv ℝ K y) S.inclHS := by
    apply HilbertSchmidt.ext
    intro h
    rfl
  rw [he]
  exact HilbertSchmidt.norm_postcompose_le _ _

theorem continuous_hDerivative (K : E → S.H) (hK : ContDiff ℝ 1 K) :
    Continuous (S.hDerivative K) := by
  have hDc : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun y => ‖fderiv ℝ K y - fderiv ℝ K x‖) (𝓝 x) (𝓝 0) := by
    have ht := (hDc.tendsto x).sub_const (fderiv ℝ K x)
    simpa using ht.norm
  have h1 := h0.mul_const ‖S.inclHS‖
  rw [zero_mul] at h1
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => S.hDerivative_sub_norm_le K y x) h1

theorem continuous_det2_hDerivative (K : E → S.H) (hK : ContDiff ℝ 1 K) :
    Continuous (fun x => det2 (S.hDerivative K x)) :=
  continuous_det2.comp (S.continuous_hDerivative K hK)

/-- The finite head and its weighted inner product depend only on the specified q. -/
abbrev Head (N : ℕ) := S.rates.cmProvider.head N

def headPt (N : ℕ) (x : E) : S.Head N := S.rates.cmProvider.headPt N (S.coord x)

theorem measurable_headPt (N : ℕ) : Measurable (S.headPt N) :=
  (S.rates.cmProvider.measurable_headPt N).comp S.measurable_coord

theorem head_lift_eq_projE (N : ℕ) (x : E) :
    S.incl (S.headPt N x : S.H) = S.projE N x := by
  apply S.coord_injective
  funext n
  calc S.coord (S.incl (S.headPt N x : S.H)) n
      = S.rates.cmProvider.hcoord (S.headPt N x : S.H) n :=
        S.incl_coordinates (S.headPt N x : S.H) n
    _ = (if n ∈ symmetricModes N then S.coord x n else 0) :=
        S.rates.cmProvider.hcoord_headPt N (S.coord x) n
    _ = S.coord (S.projE N x) n := (S.proj_coordinates N x n).symm

theorem incl_denseRange : DenseRange S.incl := by
  intro x
  refine mem_closure_of_tendsto (S.proj_strong x) (Eventually.of_forall fun N => ?_)
  exact ⟨(S.headPt N x : S.H), S.head_lift_eq_projE N x⟩

/-- The full source E law has the correct standard-Gaussian finite CM heads. -/
theorem headPt_map (N : ℕ) : S.gamma.map (S.headPt N) = finiteStdGaussian (S.Head N) := by
  change S.gamma.map (S.rates.cmProvider.headPt N ∘ S.coord) = _
  rw [← Measure.map_map (S.rates.cmProvider.measurable_headPt N) S.measurable_coord]
  rw [show S.gamma.map S.coord = S.rates.cmProvider.γ from S.coordinate_law]
  exact S.rates.cmProvider.headPt_map N

/-- Cylindrical fields and finite Gaussian divergences on the source E itself. -/
def cylField (N : ℕ) (g : S.Head N → S.Head N) (x : E) : S.H := g (S.headPt N x)

def cylDiv (N : ℕ) (g : S.Head N → S.Head N) (x : E) : ℝ :=
  finiteGaussianDivergence g (S.headPt N x)

/-- The Gaussian L2-closed graph of smooth cylindrical divergences. This is a
    literal graph-closure predicate, not an assumed divergence theorem. -/
def SourceClosedDivergence (F : E → S.H) (η : E → ℝ) : Prop :=
  MemLp η 2 S.gamma ∧
  ∃ (N : ℕ → ℕ) (g : ∀ k, S.Head (N k) → S.Head (N k)) (C : ℕ → ℝ) (p : ℕ → ℕ),
    (∀ k, ContDiff ℝ 2 (g k)) ∧
    (∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k) ∧
    (∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k) ∧
    Tendsto (fun k => eLpNorm (fun x => ‖S.cylField (N k) (g k) x - F x‖) 2 S.gamma)
      atTop (𝓝 0) ∧
    Tendsto (fun k => eLpNorm (fun x => S.cylDiv (N k) (g k) x - η x) 2 S.gamma)
      atTop (𝓝 0)

/-- The source's local existence and compatibility with every closed-divergence
    representative agreeing on a ball; cf. v2:572-587 and ramer_general's clauses. -/
def SourceLocalDivergence (K : E → S.H) (d : E → ℝ) : Prop :=
  (∀ x₀ : E, ∃ r > 0, ∃ (G : E → S.H) (η : E → ℝ),
    Set.EqOn G K (Metric.ball x₀ r) ∧ S.SourceClosedDivergence G η) ∧
  (∀ (x₀ : E) (r : ℝ) (G : E → S.H) (η : E → ℝ),
    Set.EqOn G K (Metric.ball x₀ r) → S.SourceClosedDivergence G η →
    ∀ᵐ x ∂S.gamma, x ∈ Metric.ball x₀ r → d x = η x)

/-- The actual finite map P_N T on P_N E, expressed in the CM head coordinates. -/
def headMap (T : E → E) (N : ℕ) (v : S.Head N) : S.Head N :=
  S.headPt N (T (S.incl (v : S.H)))

/-- v2:560-564, with real determinant and exact finite CM energy difference. -/
def cylindricalJacobian (T : E ≃ₜ E) (N : ℕ) (x : E) : ℝ :=
  finiteRamerDensity (S.headMap T N) (S.headPt N x)

theorem cylindricalJacobian_eq (T : E ≃ₜ E) (N : ℕ) (x : E) :
    S.cylindricalJacobian T N x =
      |(fderiv ℝ (S.headMap T N) (S.headPt N x)).det| *
        Real.exp (-S.rates.quadraticEnergy (S.headMap T N (S.headPt N x) : S.H) +
          S.rates.quadraticEnergy (S.headPt N x : S.H)) := by
  unfold cylindricalJacobian finiteRamerDensity
  rw [S.rates.quadraticEnergy_eq_half_norm_sq, S.rates.quadraticEnergy_eq_half_norm_sq]
  simp only [Submodule.norm_coe]
  congr 1
  congr 1
  ring

theorem cylindricalJacobian_nonneg (T : E ≃ₜ E) (N : ℕ) (x : E) :
    0 ≤ S.cylindricalJacobian T N x := finiteRamerDensity_nonneg _ _

/-- The actual inverse of the CM derivative, in the coupled source E. -/
theorem exists_inverse_hDerivative (T : E ≃ₜ E) (K Kinv : E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTi : ∀ y, T.symm y = y + S.incl (Kinv y))
    (hK : Differentiable ℝ K) (hKi : Differentiable ℝ Kinv) (x : E) :
    ∃ L : S.H ≃L[ℝ] S.H,
      (∀ h : S.H, L h = h + (S.hDerivative K x).toCLM h) ∧
      (∀ h : S.H, L.symm h = h + (S.hDerivative Kinv (T x)).toCLM h) := by
  obtain ⟨L, hL, hLi⟩ := NlsGge.Ramer.exists_inverse_id_add_HDeriv S.incl
    S.incl_injective T K Kinv hT hTi hK hKi x
  refine ⟨L, ?_, ?_⟩
  · intro h
    have he := congrArg (fun A : S.H →L[ℝ] S.H => A h) (S.hDerivative_toCLM K x)
    exact (congrArg (fun A : S.H →L[ℝ] S.H => A h) hL).trans
      (congrArg (fun v => h + v) he.symm)
  · intro h
    have he := congrArg (fun A : S.H →L[ℝ] S.H => A h) (S.hDerivative_toCLM Kinv (T x))
    exact (congrArg (fun A : S.H →L[ℝ] S.H => A h) hLi).trans
      (congrArg (fun v => h + v) he.symm)

/-- The literal source Jacobian expression, once a local divergence is supplied. -/
def ramerJacobian (K : E → S.H) (d : E → ℝ) (x : E) : ℝ :=
  |det2 (S.hDerivative K x)| * Real.exp (-d x - ‖K x‖ ^ 2 / 2)

/-- Pointwise positivity needs no assumed divergence or density identity. -/
theorem ramerJacobian_pos (T : E ≃ₜ E) (K Kinv : E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTi : ∀ y, T.symm y = y + S.incl (Kinv y))
    (hK : Differentiable ℝ K) (hKi : Differentiable ℝ Kinv)
    (d : E → ℝ) (x : E) : 0 < S.ramerJacobian K d x := by
  unfold ramerJacobian
  refine mul_pos (abs_pos.2 ?_) (Real.exp_pos _)
  obtain ⟨L, hL, hLi⟩ := S.exists_inverse_hDerivative T K Kinv hT hTi hK hKi x
  apply det2_ne_zero_of_isUnit
  have hLp : ∀ h, L h = h + (S.hDerivative K x).toCLM h := hL
  have hLip : ∀ h, L.symm h = h + (S.hDerivative Kinv (T x)).toCLM h := hLi
  refine ⟨⟨1 + (S.hDerivative K x).toCLM,
    1 + (S.hDerivative Kinv (T x)).toCLM, ?_, ?_⟩, rfl⟩
  · ext h
    have he := L.apply_symm_apply h
    rw [hLip, hLp] at he
    simpa [add_comm] using he
  · ext h
    have he := L.symm_apply_apply h
    rw [hLp, hLip] at he
    simpa [add_comm] using he

/-- Actual source E images of the normalized coordinate CM basis. -/
def cmColumn (p : ℤ × Fin 2) : E :=
  S.incl (weightedRealHilbertBasis S.rates.cmProvider.cmWeight p)

theorem cmColumn_ne_zero (p : ℤ × Fin 2) : S.cmColumn p ≠ 0 := by
  intro hz
  have he : weightedRealHilbertBasis S.rates.cmProvider.cmWeight p = 0 :=
    S.incl_injective (by simpa only [cmColumn, map_zero] using hz)
  have hn := (weightedRealHilbertBasis S.rates.cmProvider.cmWeight).orthonormal.norm_eq_one p
  rw [he, norm_zero] at hn
  norm_num at hn

def modeColumnEnergy (n : ℤ) : ℝ := ‖S.cmColumn (n, 0)‖ ^ 2 + ‖S.cmColumn (n, 1)‖ ^ 2

theorem modeColumnEnergy_pos (n : ℤ) : 0 < S.modeColumnEnergy n := by
  have h0 : 0 < ‖S.cmColumn (n, 0)‖ := norm_pos_iff.2 (S.cmColumn_ne_zero (n, 0))
  exact add_pos_of_pos_of_nonneg (pow_pos h0 2) (sq_nonneg _)

theorem summable_modeColumnEnergy : Summable S.modeColumnEnergy := by
  have hs := (S.inclHS.hasSum_basis_sq
    (weightedRealHilbertBasis S.rates.cmProvider.cmWeight)).summable
  have hnn : ∀ p : ℤ × Fin 2,
      0 ≤ ‖S.inclHS.toCLM (weightedRealHilbertBasis S.rates.cmProvider.cmWeight p)‖ ^ 2 :=
    fun _ => sq_nonneg _
  have hg := (summable_prod_of_nonneg hnn).mp hs
  refine hg.2.congr fun n => ?_
  simp only [tsum_fintype, Fin.sum_univ_two]
  rfl

/-- A diagonal envelope weight obtained from actual source HS columns.
    The factor four allows both real components and both members of a shell. -/
def envelopeWeight (n : ℤ) : ℝ := 4 * (2 * S.rates.q n) * S.modeColumnEnergy n

theorem envelopeWeight_pos (n : ℤ) : 0 < S.envelopeWeight n := by
  exact mul_pos (mul_pos (by norm_num) (mul_pos (by norm_num) (S.rates.q_pos n)))
    (S.modeColumnEnergy_pos n)

/-- The actual diagonal product-Gaussian space proposed for the envelope route.
    This definition assumes no comparison or Gaussian-transfer theorem. -/
def diagonalEnvelope : NlsGge.Ramer.General.RamerSetting where
  q := S.rates.q
  q_pos := S.rates.q_pos
  M n := NlsGge.Ramer.General.ModeForm.iso (S.envelopeWeight n) (S.envelopeWeight_pos n)
  hs := by
    refine (S.summable_modeColumnEnergy.mul_left 8).congr fun n => ?_
    rw [NlsGge.Ramer.General.ModeForm.iso_tr]
    dsimp only [envelopeWeight]
    field_simp [(S.rates.q_pos n).ne'] <;> ring

theorem diagonalEnvelope_rates (n : ℤ) : S.diagonalEnvelope.q n = S.rates.q n := rfl


/- Both CM carriers and heads are determined by the same q. The explicit
   isometries below record this; source E is not identified with envelope E. -/

/-- The explicit identity isometry of the two factor-two CM spaces. -/
abbrev envelopeCMEquiv : S.H ≃ₗᵢ[ℝ] S.diagonalEnvelope.H where
  toFun h := h
  invFun h := h
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The corresponding identity isometry on every literal symmetric CM head. -/
abbrev envelopeHeadEquiv (N : ℕ) : S.Head N ≃ₗᵢ[ℝ] S.diagonalEnvelope.head N where
  toFun h := h
  invFun h := h
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

theorem map_coord : S.gamma.map S.coord = countableComplexGaussian S.rates.q :=
  S.coordinate_law

theorem envelopeCMEquiv_hcoord (h : S.H) (n : ℤ) :
    S.diagonalEnvelope.hcoord (S.envelopeCMEquiv h) n = S.rates.cmProvider.hcoord h n := rfl

theorem envelopeHeadEquiv_coe (N : ℕ) (v : S.Head N) :
    (S.envelopeHeadEquiv N v : S.diagonalEnvelope.H) = S.envelopeCMEquiv (v : S.H) := rfl

include S in
/-- Source separability follows from the actual dense CM inclusion; it is not
    an added premise of the source setting. -/
theorem source_separableSpace : TopologicalSpace.SeparableSpace E :=
  S.incl_denseRange.separableSpace S.incl.continuous

theorem continuous_coord : Continuous S.coord := by
  refine continuous_pi fun n => ?_
  exact (coordC38 1 n).continuous.comp S.toH1.continuous

/-- The source coordinates determine Borel measures, including measures
    obtained later by a Gaussian transfer. -/
theorem measurableEmbedding_coord : MeasurableEmbedding S.coord := by
  letI : TopologicalSpace.SeparableSpace E := S.source_separableSpace
  letI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  exact S.continuous_coord.measurableEmbedding S.coord_injective

theorem measure_eq_of_coordinate_law (μ : Measure E)
    (hμ : μ.map S.coord = countableComplexGaussian S.rates.q) : μ = S.gamma := by
  apply S.measurableEmbedding_coord.map_injective
  exact hμ.trans S.map_coord.symm

/-- The cutoff action on a genuine CM basis column. -/
theorem projE_cmColumn (N : ℕ) (p : ℤ × Fin 2) :
    S.projE N (S.cmColumn p) =
      if p.1 ∈ symmetricModes N then S.cmColumn p else 0 := by
  classical
  have hh : S.projH N (weightedRealHilbertBasis S.rates.cmProvider.cmWeight p) =
      if p.1 ∈ symmetricModes N then
        weightedRealHilbertBasis S.rates.cmProvider.cmWeight p else 0 := by
    apply S.rates.cmProvider.hcoord_ext
    intro n
    change S.rates.cmProvider.hcoord
      (S.rates.cmProvider.headProj N (weightedRealHilbertBasis S.rates.cmProvider.cmWeight p)) n = _
    rw [S.rates.cmProvider.hcoord_headProj]
    by_cases hp : p.1 ∈ symmetricModes N
    · simp only [if_pos hp]
      rw [S.rates.cmProvider.hcoord_basis]
      by_cases hn : n = p.1
      · subst n; simp only [if_pos hp]
      · simp only [if_neg hn, zero_div, ite_self]
    · simp only [if_neg hp]
      rw [S.rates.cmProvider.hcoord_basis]
      change (if n ∈ symmetricModes N then
        (if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
          (Real.sqrt (S.rates.cmProvider.cmWeight n) : ℂ) else 0) = 0
      by_cases hn : n = p.1
      · subst n; simp only [if_neg hp]
      · simp only [if_neg hn, zero_div, ite_self]
  calc
    S.projE N (S.cmColumn p) = S.incl
        (S.projH N (weightedRealHilbertBasis S.rates.cmProvider.cmWeight p)) :=
      S.projE_incl N _
    _ = if p.1 ∈ symmetricModes N then S.cmColumn p else 0 := by
      rw [hh]
      split_ifs <;> simp only [cmColumn, map_zero]

/-- Distinct symmetric shells are orthogonal in source E. Within a shell,
    including the pair n,-n, no orthogonality is asserted. -/
theorem cmColumn_inner_eq_zero (p q : ℤ × Fin 2)
    (hpq : p.1.natAbs ≠ q.1.natAbs) : inner ℝ (S.cmColumn p) (S.cmColumn q) = 0 := by
  have hsmall (p q : ℤ × Fin 2) (hlt : p.1.natAbs < q.1.natAbs) :
      inner ℝ (S.cmColumn p) (S.cmColumn q) = 0 := by
    have hp : p.1 ∈ symmetricModes p.1.natAbs := by
      simp only [symmetricModes, Finset.mem_Icc]
      omega
    have hq : q.1 ∉ symmetricModes p.1.natAbs := by
      simp only [symmetricModes, Finset.mem_Icc]
      omega
    have ho := S.proj_orthogonal p.1.natAbs (S.cmColumn q) (S.cmColumn p)
    rw [S.projE_cmColumn, S.projE_cmColumn, if_pos hp, if_neg hq, sub_zero] at ho
    exact ho
  rcases lt_or_gt_of_ne hpq with h | h
  · exact hsmall p q h
  · rw [real_inner_comm]
    exact hsmall q p h

/-- A finite collection of real CM basis indices has at most four indices in
    any symmetric shell (and only two in the zero shell). -/
theorem shell_fiber_card_le_four (s : Finset (ℤ × Fin 2)) (p : ℤ × Fin 2) :
    (s.filter fun q => q.1.natAbs = p.1.natAbs).card ≤ 4 := by
  classical
  have hsub : (s.filter fun q => q.1.natAbs = p.1.natAbs) ⊆
      ({p.1, -p.1} : Finset ℤ).product (Finset.univ : Finset (Fin 2)) := by
    intro q hq
    have he := (Finset.mem_filter.mp hq).2
    rcases Int.natAbs_eq_natAbs_iff.mp he with h | h
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_insert.mpr (Or.inl h), Finset.mem_univ _⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)), Finset.mem_univ _⟩
  calc
    _ ≤ (({p.1, -p.1} : Finset ℤ).product (Finset.univ : Finset (Fin 2))).card :=
      Finset.card_le_card hsub
    _ = ({p.1, -p.1} : Finset ℤ).card * 2 := by simp
    _ ≤ 2 * 2 := Nat.mul_le_mul_right 2 (Finset.card_le_two (a := p.1) (b := -p.1))
    _ = 4 := rfl

/-- The finite Gram estimate needed by the envelope construction. It uses
    orthogonality only between shells, and the exact bound of four real columns. -/
theorem norm_sum_cmColumn_sq_le (s : Finset (ℤ × Fin 2)) (a : (ℤ × Fin 2) → ℝ) :
    ‖∑ p ∈ s, a p • S.cmColumn p‖ ^ 2 ≤
      4 * ∑ p ∈ s, (a p) ^ 2 * ‖S.cmColumn p‖ ^ 2 := by
  classical
  let v : (ℤ × Fin 2) → E := fun p => a p • S.cmColumn p
  let r : (ℤ × Fin 2) → ℝ := fun p => ‖v p‖ ^ 2
  have hrow (p : ℤ × Fin 2) :
      (∑ q ∈ s, if q.1.natAbs = p.1.natAbs then r p else 0) ≤ 4 * r p := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast shell_fiber_card_le_four s p
  have hA : (∑ p ∈ s, ∑ q ∈ s,
      if p.1.natAbs = q.1.natAbs then r p else 0) ≤ 4 * ∑ p ∈ s, r p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    simpa only [eq_comm] using hrow p
  have hB : (∑ p ∈ s, ∑ q ∈ s,
      if p.1.natAbs = q.1.natAbs then r q else 0) ≤ 4 * ∑ p ∈ s, r p := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => hrow q
  have hGram : 2 * ‖∑ p ∈ s, v p‖ ^ 2 ≤
      (∑ p ∈ s, ∑ q ∈ s, if p.1.natAbs = q.1.natAbs then r p else 0) +
      (∑ p ∈ s, ∑ q ∈ s, if p.1.natAbs = q.1.natAbs then r q else 0) := by
    have he : 2 * ‖∑ p ∈ s, v p‖ ^ 2 =
        ∑ p ∈ s, ∑ q ∈ s, 2 * inner ℝ (v p) (v q) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [sum_inner, inner_sum, Finset.mul_sum]
      exact Finset.sum_comm
    rw [he, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q hq => ?_
    by_cases heq : p.1.natAbs = q.1.natAbs
    · simp only [if_pos heq]
      have hn := norm_sub_sq_real (v p) (v q)
      dsimp only [r]
      nlinarith [sq_nonneg ‖v p - v q‖]
    · have hz : inner ℝ (v p) (v q) = 0 := by
        dsimp only [v]
        rw [real_inner_smul_left, inner_smul_right, S.cmColumn_inner_eq_zero p q heq]
        simp
      simp only [if_neg heq, hz, mul_zero, zero_add, le_refl]
  have hfin : ‖∑ p ∈ s, v p‖ ^ 2 ≤ 4 * ∑ p ∈ s, r p := by
    nlinarith [hA, hB, hGram]
  simpa only [v, r, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hfin

/-- A real CM coefficient, in the already fixed source CM basis. -/
def cmCoefficient (h : S.H) (p : ℤ × Fin 2) : ℝ :=
  inner ℝ (weightedRealHilbertBasis S.rates.cmProvider.cmWeight p) h

theorem cmCoefficient_sq_le (h : S.H) (p : ℤ × Fin 2) :
    (S.cmCoefficient h p) ^ 2 ≤
      S.rates.cmProvider.cmWeight p.1 * ‖S.rates.cmProvider.hcoord h p.1‖ ^ 2 := by
  have he : S.cmCoefficient h p = inner ℝ (Complex.orthonormalBasisOneI p.2)
      (weightedIsometry S.rates.cmProvider.cmWeight
        (show WeightedHilbert S.rates.cmProvider.cmWeight from h) p.1) := by
    unfold cmCoefficient
    rw [weightedRealHilbertBasis_apply, weightedRealBasisVector_inner]
  rw [he]
  have hn := norm_inner_le_norm (𝕜 := ℝ) (Complex.orthonormalBasisOneI p.2)
    (weightedIsometry S.rates.cmProvider.cmWeight
      (show WeightedHilbert S.rates.cmProvider.cmWeight from h) p.1)
  rw [Complex.orthonormalBasisOneI.orthonormal.norm_eq_one, one_mul] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ = ‖inner ℝ (Complex.orthonormalBasisOneI p.2)
        (weightedIsometry S.rates.cmProvider.cmWeight
          (show WeightedHilbert S.rates.cmProvider.cmWeight from h) p.1)‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    _ ≤ _ := hsq
    _ = _ := by
      rw [weightedIsometry_apply]
      simp only [weightedCoordinates, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (S.rates.cmProvider.cmWeight_pos p.1).le]
      rfl

/-- The summable envelope energy of a CM element, before using its real sum. -/
theorem envelope_energy_hasSum (h : S.H) :
    HasSum (fun n => S.rates.cmProvider.cmWeight n *
      ‖S.rates.cmProvider.hcoord h n‖ ^ 2 * S.modeColumnEnergy n)
      (‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖ ^ 2 / 4) := by
  have ht := (S.diagonalEnvelope.E_norm_sq_hasSum (S.diagonalEnvelope.incl (S.envelopeCMEquiv h))).mul_left (1 / 4 : ℝ)
  have hv : (1 / 4 : ℝ) * ‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖ ^ 2 =
      ‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖ ^ 2 / 4 := by ring
  rw [hv] at ht
  refine ht.congr_fun (fun n => ?_)
  have he : (S.diagonalEnvelope.M n).form
      (S.diagonalEnvelope.coord n (S.diagonalEnvelope.incl (S.envelopeCMEquiv h)))
      (S.diagonalEnvelope.coord n (S.diagonalEnvelope.incl (S.envelopeCMEquiv h))) =
      S.envelopeWeight n * ‖S.rates.cmProvider.hcoord h n‖ ^ 2 :=
    (congrArg (fun z : ℂ => (S.diagonalEnvelope.M n).form z z)
      ((S.diagonalEnvelope.coord_incl (S.envelopeCMEquiv h) n).trans
        (S.envelopeCMEquiv_hcoord h n))).trans
      (NlsGge.Ramer.General.ModeForm.iso_form _ _ _)
  calc
    _ = (1 / 4 : ℝ) * (S.envelopeWeight n * ‖S.rates.cmProvider.hcoord h n‖ ^ 2) := by
      dsimp only [envelopeWeight, NlsGge.Ramer.General.RamerSetting.cmWeight,
        SourceGaussianRates.cmProvider]
      ring
    _ = _ := congrArg (fun a : ℝ => (1 / 4 : ℝ) * a) he.symm

/-- The diagonal envelope dominates source E on the whole CM space. The proof
    uses finite real basis sums and then the actual CM-basis expansion. -/
theorem incl_norm_le_diagonalEnvelope (h : S.H) : ‖S.incl h‖ ≤ ‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖ := by
  classical
  let g : (ℤ × Fin 2) → ℝ := fun p => S.rates.cmProvider.cmWeight p.1 *
    ‖S.rates.cmProvider.hcoord h p.1‖ ^ 2 * ‖S.cmColumn p‖ ^ 2
  have hg_nonneg : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg (mul_nonneg (S.rates.cmProvider.cmWeight_pos p.1).le (sq_nonneg _))
      (sq_nonneg _)
  have hg_fiber (n : ℤ) : Summable (fun j : Fin 2 => g (n, j)) :=
    (hasSum_fintype (fun j : Fin 2 => g (n, j))).summable
  have hg_fiber_eq (n : ℤ) : (∑' j : Fin 2, g (n, j)) =
      S.rates.cmProvider.cmWeight n * ‖S.rates.cmProvider.hcoord h n‖ ^ 2 *
        S.modeColumnEnergy n := by
    simp only [tsum_fintype, Fin.sum_univ_two, g, modeColumnEnergy]
    ring
  have hg : Summable g := (summable_prod_of_nonneg hg_nonneg).mpr
    ⟨hg_fiber, (S.envelope_energy_hasSum h).summable.congr (fun n => (hg_fiber_eq n).symm)⟩
  have hg_sum : (∑' p, g p) = ‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖ ^ 2 / 4 := by
    rw [hg.tsum_prod' hg_fiber]
    simp_rw [hg_fiber_eq]
    exact (S.envelope_energy_hasSum h).tsum_eq
  have hfinite (s : Finset (ℤ × Fin 2)) :
      ‖∑ p ∈ s, S.cmCoefficient h p • S.cmColumn p‖ ^ 2 ≤ ‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖ ^ 2 := by
    calc
      _ ≤ 4 * ∑ p ∈ s, (S.cmCoefficient h p) ^ 2 * ‖S.cmColumn p‖ ^ 2 :=
        S.norm_sum_cmColumn_sq_le s (S.cmCoefficient h)
      _ ≤ 4 * ∑ p ∈ s, g p := by
        gcongr with p hp
        exact mul_le_mul_of_nonneg_right (S.cmCoefficient_sq_le h p) (sq_nonneg _)
      _ ≤ 4 * ∑' p, g p := mul_le_mul_of_nonneg_left
        (hg.sum_le_tsum s (fun p hp => hg_nonneg p)) (by norm_num)
      _ = _ := by rw [hg_sum]; ring
  have hb : HasSum (fun p => S.cmCoefficient h p • S.cmColumn p) (S.incl h) := by
    have ht := ((weightedRealHilbertBasis S.rates.cmProvider.cmWeight).hasSum_repr h).mapL S.incl
    refine ht.congr_fun (fun p => ?_)
    simp only [cmColumn, cmCoefficient, HilbertBasis.repr_apply_apply]
    exact (S.incl.map_smul _ _).symm
  have ht : Tendsto (fun s : Finset (ℤ × Fin 2) =>
      ‖∑ p ∈ s, S.cmCoefficient h p • S.cmColumn p‖ ^ 2) atTop (𝓝 (‖S.incl h‖ ^ 2)) :=
    (show Tendsto (fun s : Finset (ℤ × Fin 2) =>
      ∑ p ∈ s, S.cmCoefficient h p • S.cmColumn p) atTop (𝓝 (S.incl h)) from hb).norm.pow 2
  exact le_of_sq_le_sq (le_of_tendsto ht (Eventually.of_forall hfinite)) (norm_nonneg _)

/-- The genuine bounded comparison map, defined only after its norm estimate
    has been proved. It is the identity on sequence coordinates. -/
def envelopeCMInclusion : S.H →L[ℝ] S.diagonalEnvelope.E :=
  S.diagonalEnvelope.incl.comp S.envelopeCMEquiv.toLinearIsometry.toContinuousLinearMap

theorem envelopeCMInclusion_denseRange : DenseRange S.envelopeCMInclusion := by
  have he : Set.range S.envelopeCMInclusion = Set.range S.diagonalEnvelope.incl := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨S.envelopeCMEquiv h, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨S.envelopeCMEquiv.symm h, ?_⟩
      exact congrArg S.diagonalEnvelope.incl (S.envelopeCMEquiv.apply_symm_apply h)
  intro x
  change x ∈ closure (Set.range S.envelopeCMInclusion)
  rw [he]
  exact S.diagonalEnvelope.incl_denseRange x

def envelopeToSource : S.diagonalEnvelope.E →L[ℝ] E :=
  S.incl.toLinearMap.extendOfNorm S.envelopeCMInclusion.toLinearMap

theorem envelopeToSource_incl (h : S.H) :
    S.envelopeToSource (S.diagonalEnvelope.incl (S.envelopeCMEquiv h)) = S.incl h := by
  have hb : ∃ C : ℝ, ∀ h : S.H,
      ‖S.incl.toLinearMap h‖ ≤ C * ‖S.envelopeCMInclusion.toLinearMap h‖ := by
    refine ⟨1, fun h => ?_⟩
    change ‖S.incl h‖ ≤ 1 * ‖S.diagonalEnvelope.incl (S.envelopeCMEquiv h)‖
    exact (S.incl_norm_le_diagonalEnvelope h).trans_eq (one_mul _).symm
  exact LinearMap.extendOfNorm_eq (f := S.incl.toLinearMap) (e := S.envelopeCMInclusion.toLinearMap)
    S.envelopeCMInclusion_denseRange hb h

theorem envelopeToSource_incl_symm (h : S.diagonalEnvelope.H) :
    S.envelopeToSource (S.diagonalEnvelope.incl h) = S.incl (S.envelopeCMEquiv.symm h) := by
  have he := S.envelopeToSource_incl (S.envelopeCMEquiv.symm h)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using he

theorem envelopeToSource_headToE (N : ℕ) (v : S.Head N) :
    S.envelopeToSource (S.diagonalEnvelope.headToE N (S.envelopeHeadEquiv N v)) =
      S.incl (v : S.H) := S.envelopeToSource_incl (v : S.H)

theorem envelopeToSource_coord (x : S.diagonalEnvelope.E) (n : ℤ) :
    S.coord (S.envelopeToSource x) n = S.diagonalEnvelope.coord n x := by
  refine isClosed_property S.diagonalEnvelope.incl_denseRange
    (p := fun y => S.coord (S.envelopeToSource y) n = S.diagonalEnvelope.coord n y) ?_ ?_ x
  · exact isClosed_eq (((continuous_apply n).comp S.continuous_coord).comp
      S.envelopeToSource.continuous) (S.diagonalEnvelope.coord n).continuous
  · intro h
    calc
      S.coord (S.envelopeToSource (S.diagonalEnvelope.incl h)) n =
          S.coord (S.incl (S.envelopeCMEquiv.symm h)) n :=
        congrArg (fun y => S.coord y n) (S.envelopeToSource_incl_symm h)
      _ = S.rates.cmProvider.hcoord (S.envelopeCMEquiv.symm h) n := S.incl_coordinates _ n
      _ = S.diagonalEnvelope.hcoord h n := by
        have hc := S.envelopeCMEquiv_hcoord (S.envelopeCMEquiv.symm h) n
        simpa only [LinearIsometryEquiv.apply_symm_apply] using hc.symm
      _ = S.diagonalEnvelope.coord n (S.diagonalEnvelope.incl h) :=
        (S.diagonalEnvelope.coord_incl h n).symm

theorem envelopeToSource_injective : Function.Injective S.envelopeToSource := by
  intro x y hxy
  apply S.diagonalEnvelope.E_ext
  intro n
  calc
    S.diagonalEnvelope.coord n x = S.coord (S.envelopeToSource x) n :=
      (S.envelopeToSource_coord x n).symm
    _ = S.coord (S.envelopeToSource y) n := congrArg (fun z => S.coord z n) hxy
    _ = S.diagonalEnvelope.coord n y := S.envelopeToSource_coord y n

/-- The comparison carries the actual envelope Gaussian to the given source
    law, proved by Borel-coordinate measure uniqueness. -/
theorem envelopeToSource_map : S.diagonalEnvelope.γE.map S.envelopeToSource = S.gamma := by
  apply S.measure_eq_of_coordinate_law
  rw [Measure.map_map S.measurable_coord S.envelopeToSource.continuous.measurable]
  have he : (S.coord ∘ S.envelopeToSource) = S.diagonalEnvelope.coordE := by
    funext x n
    exact S.envelopeToSource_coord x n
  rw [he]
  exact S.diagonalEnvelope.measurePreserving_coordE.map_eq

theorem envelopeToSource_projE (N : ℕ) (x : S.diagonalEnvelope.E) :
    S.envelopeToSource (S.diagonalEnvelope.projE N x) = S.projE N (S.envelopeToSource x) := by
  apply S.coord_injective
  funext n
  calc
    S.coord (S.envelopeToSource (S.diagonalEnvelope.projE N x)) n =
        S.diagonalEnvelope.coord n (S.diagonalEnvelope.projE N x) := S.envelopeToSource_coord _ n
    _ = (if n ∈ symmetricModes N then S.diagonalEnvelope.coord n x else 0) :=
      S.diagonalEnvelope.coord_projE N x n
    _ = (if n ∈ symmetricModes N then S.coord (S.envelopeToSource x) n else 0) :=
      congrArg (fun z : ℂ => if n ∈ symmetricModes N then z else 0)
        (S.envelopeToSource_coord x n).symm
    _ = S.coord (S.projE N (S.envelopeToSource x)) n := (S.proj_coordinates N _ n).symm

/-- A source CM field transported to the envelope CM carrier. -/
def envelopeField (F : E → S.H) (x : S.diagonalEnvelope.E) : S.diagonalEnvelope.H :=
  S.envelopeCMEquiv (F (S.envelopeToSource x))

theorem contDiff_envelopeField (F : E → S.H) (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (S.envelopeField F) :=
  S.envelopeCMEquiv.toContinuousLinearEquiv.contDiff.comp (hF.comp S.envelopeToSource.contDiff)

theorem fderiv_envelopeField (F : E → S.H) (hF : Differentiable ℝ F) (x : S.diagonalEnvelope.E) :
    fderiv ℝ (S.envelopeField F) x = S.envelopeCMEquiv.toLinearIsometry.toContinuousLinearMap.comp
      ((fderiv ℝ F (S.envelopeToSource x)).comp S.envelopeToSource) :=
  (S.envelopeCMEquiv.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp x
    ((hF _).hasFDerivAt.comp x S.envelopeToSource.hasFDerivAt)).fderiv

theorem norm_envelopeCMEquivCLM_le_one :
    ‖S.envelopeCMEquiv.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le S.envelopeCMEquiv.toLinearIsometry

theorem norm_fderiv_envelopeField_le (F : E → S.H) (hF : Differentiable ℝ F)
    (x : S.diagonalEnvelope.E) : ‖fderiv ℝ (S.envelopeField F) x‖ ≤
      ‖fderiv ℝ F (S.envelopeToSource x)‖ * ‖S.envelopeToSource‖ := by
  refine (congrArg norm (S.fderiv_envelopeField F hF x)).le.trans ?_
  calc
    _ ≤ ‖S.envelopeCMEquiv.toLinearIsometry.toContinuousLinearMap‖ *
        ‖(fderiv ℝ F (S.envelopeToSource x)).comp S.envelopeToSource‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖(fderiv ℝ F (S.envelopeToSource x)).comp S.envelopeToSource‖ :=
      mul_le_mul_of_nonneg_right S.norm_envelopeCMEquivCLM_le_one (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact ContinuousLinearMap.opNorm_comp_le _ _

/-- A measurable source realization of the fixed product Gaussian. -/
def realization (z : ℤ → ℂ) : E := S.envelopeToSource (S.diagonalEnvelope.R z)

theorem measurable_realization : Measurable S.realization :=
  S.envelopeToSource.continuous.measurable.comp S.diagonalEnvelope.measurable_R

theorem coord_realization_ae : ∀ᵐ z ∂(countableComplexGaussian S.rates.q),
    S.coord (S.realization z) = z := by
  filter_upwards [S.diagonalEnvelope.coordE_R_ae] with z hz
  funext n
  exact (S.envelopeToSource_coord _ n).trans (congrFun hz n)

/-- All sets, rather than just measurable sets, transfer through the almost
    everywhere inverse realization. -/
theorem measure_realization_preimage (A : Set E) :
    S.gamma A = countableComplexGaussian S.rates.q (S.realization ⁻¹' A) := by
  have he : countableComplexGaussian S.rates.q (S.coord '' A) = S.gamma A := by
    rw [← S.map_coord, S.measurableEmbedding_coord.map_apply,
      S.coord_injective.preimage_image]
  rw [← he]
  apply measure_congr
  filter_upwards [S.coord_realization_ae] with z hz
  apply propext
  constructor
  · rintro ⟨x, hx, hzx⟩
    have hEq : S.realization z = x := S.coord_injective (hz.trans hzx.symm)
    simpa only [Set.mem_preimage, hEq] using hx
  · intro hzA
    exact ⟨S.realization z, hzA, hz⟩

theorem ae_realization_iff (p : E → Prop) :
    (∀ᵐ x ∂S.gamma, p x) ↔
      ∀ᵐ z ∂(countableComplexGaussian S.rates.q), p (S.realization z) := by
  simp only [ae_iff]
  rw [S.measure_realization_preimage]
  rfl

theorem realization_coord_ae : ∀ᵐ x ∂S.gamma, S.realization (S.coord x) = x := by
  apply (S.ae_realization_iff _).2
  filter_upwards [S.coord_realization_ae] with z hz
  exact congrArg S.realization hz

/-- Gaussian L2 norms transfer even for an arbitrary graph-limit candidate. -/
theorem eLpNorm_realization (f : E → ℝ) : eLpNorm f 2 S.gamma =
    eLpNorm (fun z => f (S.realization z)) 2 (countableComplexGaussian S.rates.q) := by
  have he := S.measurableEmbedding_coord.eLpNorm_map_measure
    (g := fun z => f (S.realization z)) (p := 2) (μ := S.gamma)
  rw [S.map_coord] at he
  refine (eLpNorm_congr_ae ?_).trans he.symm
  filter_upwards [S.realization_coord_ae] with x hx
  exact congrArg f hx.symm

theorem memLp_realization_iff (f : E → ℝ) : MemLp f 2 S.gamma ↔
    MemLp (fun z => f (S.realization z)) 2 (countableComplexGaussian S.rates.q) := by
  have he := S.measurableEmbedding_coord.memLp_map_measure_iff
    (g := fun z => f (S.realization z)) (p := 2) (μ := S.gamma)
  rw [S.map_coord] at he
  refine Iff.trans ?_ he.symm
  apply memLp_congr_ae
  filter_upwards [S.realization_coord_ae] with x hx
  exact congrArg f hx.symm

theorem headPt_realization_ae (N : ℕ) :
    ∀ᵐ z ∂(countableComplexGaussian S.rates.q),
      S.envelopeHeadEquiv N (S.headPt N (S.realization z)) = S.diagonalEnvelope.headPt N z := by
  filter_upwards [S.coord_realization_ae] with z hz
  change S.envelopeHeadEquiv N (S.rates.cmProvider.headPt N (S.coord (S.realization z))) = _
  rw [hz]
  rfl

/-- The native profile is the conjugate by the actual finite-head isometry. -/
def envelopeProfile (N : ℕ) (g : S.Head N → S.Head N) :
    S.diagonalEnvelope.head N → S.diagonalEnvelope.head N :=
  fun v => S.envelopeHeadEquiv N (g ((S.envelopeHeadEquiv N).symm v))

def sourceProfile (N : ℕ) (g : S.diagonalEnvelope.head N → S.diagonalEnvelope.head N) :
    S.Head N → S.Head N := fun v => (S.envelopeHeadEquiv N).symm (g (S.envelopeHeadEquiv N v))

@[simp] theorem envelopeProfile_sourceProfile (N : ℕ)
    (g : S.diagonalEnvelope.head N → S.diagonalEnvelope.head N) :
    S.envelopeProfile N (S.sourceProfile N g) = g := by
  funext v
  simp only [envelopeProfile, sourceProfile, LinearIsometryEquiv.apply_symm_apply]

theorem contDiff_envelopeProfile (N : ℕ) (g : S.Head N → S.Head N) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (S.envelopeProfile N g) :=
  (S.envelopeHeadEquiv N).toContinuousLinearEquiv.contDiff.comp
    (hg.comp (S.envelopeHeadEquiv N).symm.toContinuousLinearEquiv.contDiff)

theorem contDiff_sourceProfile (N : ℕ)
    (g : S.diagonalEnvelope.head N → S.diagonalEnvelope.head N) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (S.sourceProfile N g) :=
  (S.envelopeHeadEquiv N).symm.toContinuousLinearEquiv.contDiff.comp
    (hg.comp (S.envelopeHeadEquiv N).toContinuousLinearEquiv.contDiff)

/-- The fixed isometries have identity coordinate formulas, so these exact
    derivative/finite-formula identities reduce definitionally. -/
theorem norm_fderiv_envelopeProfile (N : ℕ) (g : S.Head N → S.Head N)
    (v : S.diagonalEnvelope.head N) : ‖fderiv ℝ (S.envelopeProfile N g) v‖ =
      ‖fderiv ℝ g ((S.envelopeHeadEquiv N).symm v)‖ := rfl

theorem norm_fderiv_sourceProfile (N : ℕ)
    (g : S.diagonalEnvelope.head N → S.diagonalEnvelope.head N) (v : S.Head N) :
    ‖fderiv ℝ (S.sourceProfile N g) v‖ = ‖fderiv ℝ g (S.envelopeHeadEquiv N v)‖ := rfl

theorem envelopeProfile_finiteDiv (N : ℕ) (g : S.Head N → S.Head N)
    (v : S.diagonalEnvelope.head N) : finiteGaussianDivergence (S.envelopeProfile N g) v =
      finiteGaussianDivergence g ((S.envelopeHeadEquiv N).symm v) := rfl

theorem envelopeProfile_finiteRamerDensity (N : ℕ) (g : S.Head N → S.Head N) (v : S.Head N) :
    finiteRamerDensity (S.envelopeProfile N g) (S.envelopeHeadEquiv N v) = finiteRamerDensity g v := rfl

/-- Every graph approximant, including its CM value, is explicitly transported. -/
theorem sourceClosedDivergence_iff_raw (F : E → S.H) (η : E → ℝ) :
    S.SourceClosedDivergence F η ↔ S.diagonalEnvelope.IsClosedDiv
      (fun z => S.envelopeCMEquiv (F (S.realization z))) (fun z => η (S.realization z)) := by
  have hf (N : ℕ) (g : S.Head N → S.Head N) :
      ∀ᵐ z ∂(countableComplexGaussian S.rates.q),
        S.diagonalEnvelope.cylField N (S.envelopeProfile N g) z =
          S.envelopeCMEquiv (S.cylField N g (S.realization z)) ∧
        S.diagonalEnvelope.cylDiv N (S.envelopeProfile N g) z = S.cylDiv N g (S.realization z) := by
    filter_upwards [S.headPt_realization_ae N] with z hz
    have hret : (S.envelopeHeadEquiv N).symm (S.diagonalEnvelope.headPt N z) =
        S.headPt N (S.realization z) :=
      (congrArg (S.envelopeHeadEquiv N).symm hz).symm.trans
        ((S.envelopeHeadEquiv N).symm_apply_apply _)
    constructor
    · calc
        _ = (S.envelopeHeadEquiv N (g ((S.envelopeHeadEquiv N).symm
            (S.diagonalEnvelope.headPt N z))) : S.diagonalEnvelope.H) := rfl
        _ = (S.envelopeHeadEquiv N (g (S.headPt N (S.realization z))) : S.diagonalEnvelope.H) :=
          congrArg (fun v : S.Head N => (S.envelopeHeadEquiv N (g v) : S.diagonalEnvelope.H)) hret
        _ = _ := S.envelopeHeadEquiv_coe N _
    · exact (S.envelopeProfile_finiteDiv N g _).trans (congrArg (finiteGaussianDivergence g) hret)
  have heF (N : ℕ) (g : S.Head N → S.Head N) :
      eLpNorm (fun x => ‖S.cylField N g x - F x‖) 2 S.gamma =
      eLpNorm (fun z => ‖S.diagonalEnvelope.cylField N (S.envelopeProfile N g) z -
        S.envelopeCMEquiv (F (S.realization z))‖) 2 S.diagonalEnvelope.γ := by
    rw [S.eLpNorm_realization]
    apply eLpNorm_congr_ae
    filter_upwards [hf N g] with z hz
    calc
      _ = ‖S.envelopeCMEquiv (S.cylField N g (S.realization z) - F (S.realization z))‖ :=
        (S.envelopeCMEquiv.norm_map _).symm
      _ = ‖S.envelopeCMEquiv (S.cylField N g (S.realization z)) -
          S.envelopeCMEquiv (F (S.realization z))‖ := congrArg norm (S.envelopeCMEquiv.map_sub _ _)
      _ = _ := congrArg (fun v : S.diagonalEnvelope.H => ‖v - S.envelopeCMEquiv (F (S.realization z))‖)
        hz.1.symm
  have heD (N : ℕ) (g : S.Head N → S.Head N) :
      eLpNorm (fun x => S.cylDiv N g x - η x) 2 S.gamma =
      eLpNorm (fun z => S.diagonalEnvelope.cylDiv N (S.envelopeProfile N g) z - η (S.realization z))
        2 S.diagonalEnvelope.γ := by
    rw [S.eLpNorm_realization]
    apply eLpNorm_congr_ae
    filter_upwards [hf N g] with z hz
    exact congrArg (fun t : ℝ => t - η (S.realization z)) hz.2.symm
  constructor
  · rintro ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hD⟩
    refine ⟨(S.memLp_realization_iff η).1 hη, N, fun k => S.envelopeProfile (N k) (g k), C, p,
      (fun k => S.contDiff_envelopeProfile (N k) (g k) (hg k)), ?_, ?_, ?_, ?_⟩
    · intro k v
      calc
        _ = ‖g k ((S.envelopeHeadEquiv (N k)).symm v)‖ := (S.envelopeHeadEquiv (N k)).norm_map _
        _ ≤ C k * (1 + ‖(S.envelopeHeadEquiv (N k)).symm v‖) ^ p k := hgg k _
        _ = _ := congrArg (fun t : ℝ => C k * (1 + t) ^ p k)
          ((S.envelopeHeadEquiv (N k)).symm.norm_map v)
    · intro k v
      calc
        _ = ‖fderiv ℝ (g k) ((S.envelopeHeadEquiv (N k)).symm v)‖ :=
          S.norm_fderiv_envelopeProfile (N k) (g k) v
        _ ≤ C k * (1 + ‖(S.envelopeHeadEquiv (N k)).symm v‖) ^ p k := hDg k _
        _ = _ := congrArg (fun t : ℝ => C k * (1 + t) ^ p k)
          ((S.envelopeHeadEquiv (N k)).symm.norm_map v)
    · exact hF.congr (fun k => heF (N k) (g k))
    · exact hD.congr (fun k => heD (N k) (g k))
  · rintro ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hD⟩
    refine ⟨(S.memLp_realization_iff η).2 hη, N, fun k => S.sourceProfile (N k) (g k), C, p,
      (fun k => S.contDiff_sourceProfile (N k) (g k) (hg k)), ?_, ?_, ?_, ?_⟩
    · intro k v
      calc
        _ = ‖g k (S.envelopeHeadEquiv (N k) v)‖ := (S.envelopeHeadEquiv (N k)).symm.norm_map _
        _ ≤ C k * (1 + ‖S.envelopeHeadEquiv (N k) v‖) ^ p k := hgg k _
        _ = _ := congrArg (fun t : ℝ => C k * (1 + t) ^ p k) ((S.envelopeHeadEquiv (N k)).norm_map v)
    · intro k v
      calc
        _ = ‖fderiv ℝ (g k) (S.envelopeHeadEquiv (N k) v)‖ := S.norm_fderiv_sourceProfile (N k) (g k) v
        _ ≤ C k * (1 + ‖S.envelopeHeadEquiv (N k) v‖) ^ p k := hDg k _
        _ = _ := congrArg (fun t : ℝ => C k * (1 + t) ^ p k) ((S.envelopeHeadEquiv (N k)).norm_map v)
    · refine hF.congr (fun k => ?_)
      have h₁ := heF (N k) (S.sourceProfile (N k) (g k))
      have h₂ := congrArg (fun gg : S.diagonalEnvelope.head (N k) → S.diagonalEnvelope.head (N k) =>
        eLpNorm (fun z => ‖S.diagonalEnvelope.cylField (N k) gg z -
          S.envelopeCMEquiv (F (S.realization z))‖) 2 S.diagonalEnvelope.γ)
        (S.envelopeProfile_sourceProfile (N k) (g k))
      exact (h₁.trans h₂).symm
    · refine hD.congr (fun k => ?_)
      have h₁ := heD (N k) (S.sourceProfile (N k) (g k))
      have h₂ := congrArg (fun gg : S.diagonalEnvelope.head (N k) → S.diagonalEnvelope.head (N k) =>
        eLpNorm (fun z => S.diagonalEnvelope.cylDiv (N k) gg z - η (S.realization z))
          2 S.diagonalEnvelope.γ) (S.envelopeProfile_sourceProfile (N k) (g k))
      exact (h₁.trans h₂).symm

theorem sourceClosedDivergence_of_raw (F : E → S.H) (η : (ℤ → ℂ) → ℝ)
    (h : S.diagonalEnvelope.IsClosedDiv (fun z => S.envelopeCMEquiv (F (S.realization z))) η) :
    S.SourceClosedDivergence F (fun x => η (S.coord x)) := by
  apply (S.sourceClosedDivergence_iff_raw _ _).2
  apply h.congr_ae
  filter_upwards [S.coord_realization_ae] with z hz
  exact congrArg η hz.symm

/-- Source-local graph existence is obtained with a bump in the original
    source E norm, followed by the proved Gaussian graph transport. -/
theorem exists_source_local_closedDivergence (K : E → S.H) (hK : ContDiff ℝ 2 K) (x₀ : E) :
    ∃ r > 0, ∃ (G : E → S.H) (η : E → ℝ),
      Set.EqOn G K (Metric.ball x₀ r) ∧ S.SourceClosedDivergence G η := by
  obtain ⟨r, hr, hKb, hDb⟩ := NlsGge.Ramer.Gen.exists_local_radius_bounds K hK x₀
  obtain ⟨ρ, hρd, hρ0, hρ1, hρin, hρout, Mρ, hMρ⟩ :=
    NlsGge.Ramer.Gen.exists_bump_generic x₀ hr
  obtain ⟨B, hGd, hGB, hDGB, hEq⟩ := NlsGge.Ramer.Gen.bumped_field_generic K hK x₀ hr
    _ _ hKb hDb ρ hρd hρ0 hρ1 hρin hρout Mρ hMρ
  let G : E → S.H := fun x => ρ x • K x
  let Gp : S.diagonalEnvelope.E → S.diagonalEnvelope.H := S.envelopeField G
  have hGp : ContDiff ℝ 2 Gp := S.contDiff_envelopeField G hGd
  let Bp : ℝ := max B (B * ‖S.envelopeToSource‖)
  have hv : ∀ x, ‖Gp x‖ ≤ Bp := fun x =>
    (S.envelopeCMEquiv.norm_map _).le.trans ((hGB _).trans (le_max_left _ _))
  have hDv : ∀ x, ‖fderiv ℝ Gp x‖ ≤ Bp := by
    intro x
    have hGdiff : Differentiable ℝ G := hGd.differentiable (by norm_num)
    exact (S.norm_fderiv_envelopeField_le G hGdiff x).trans
      ((mul_le_mul_of_nonneg_right (hDGB _) (norm_nonneg _)).trans (le_max_right _ _))
  obtain ⟨η, hη, hlim, -⟩ := S.diagonalEnvelope.divergence_identification_bounded Gp hGp Bp hv hDv
  have hraw := S.diagonalEnvelope.isClosedDiv_of_tendsto_truncField Gp hGp Bp hv hDv η hη hlim
  exact ⟨r, hr, G, fun x => η (S.coord x), hEq,
    S.sourceClosedDivergence_of_raw G η hraw⟩

/-- Compatibility of the landed local divergence on an arbitrary open subset
    of the envelope; source balls pull back to precisely such sets. -/
theorem envelope_divergence_compatible_open
    (K : S.diagonalEnvelope.E → S.diagonalEnvelope.H) (hK : ContDiff ℝ 2 K) (δ : (ℤ → ℂ) → ℝ)
    (hδ : ∀ (x₀ : S.diagonalEnvelope.E) (r : ℝ) (G : S.diagonalEnvelope.E → S.diagonalEnvelope.H)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
        S.diagonalEnvelope.IsClosedDiv (fun z => G (S.diagonalEnvelope.R z)) η →
        ∀ᵐ z ∂S.diagonalEnvelope.γ, S.diagonalEnvelope.R z ∈ Metric.ball x₀ r → δ z = η z)
    (O : Set S.diagonalEnvelope.E) (hO : IsOpen O)
    (G : S.diagonalEnvelope.E → S.diagonalEnvelope.H) (η : (ℤ → ℂ) → ℝ)
    (hEq : Set.EqOn G K O)
    (hG : S.diagonalEnvelope.IsClosedDiv (fun z => G (S.diagonalEnvelope.R z)) η) :
    ∀ᵐ z ∂S.diagonalEnvelope.γ, S.diagonalEnvelope.R z ∈ O → δ z = η z := by
  classical
  have hloc := S.diagonalEnvelope.exists_local_closedDiv K hK
  choose r hr G₀ η₀ hEq₀ hCD₀ hm₀ hlim₀ using hloc
  obtain ⟨A, hAc, hAcov⟩ := S.diagonalEnvelope.exists_countable_cover_balls r hr
  have ha : ∀ x ∈ A, ∀ᵐ z ∂S.diagonalEnvelope.γ,
      S.diagonalEnvelope.R z ∈ O ∩ Metric.ball x (r x) → δ z = η z := by
    intro x hx
    have hlocal := NlsGge.Ramer.General.RamerSetting.IsClosedDiv.ae_eq_of_eqOn
      (hO.inter Metric.isOpen_ball)
      (G := G₀ x) (G' := G)
      (fun y hy => (hEq₀ x hy.2).trans (hEq hy.1).symm) (hCD₀ x) hG
    filter_upwards [hδ x (r x) (G₀ x) (η₀ x) (hEq₀ x) (hCD₀ x), hlocal] with z hz₁ hz₂ hz
    exact (hz₁ hz.2).trans (hz₂ hz)
  filter_upwards [(ae_ball_iff hAc).2 ha] with z hz hzO
  obtain ⟨x, hx, hzx⟩ := hAcov (S.diagonalEnvelope.R z)
  exact hz x hx ⟨hzO, hzx⟩

theorem measurableEmbedding_envelopeToSource : MeasurableEmbedding S.envelopeToSource :=
  S.envelopeToSource.continuous.measurableEmbedding S.envelopeToSource_injective

/-- Density pushforward along the proved injective Gaussian comparison map. -/
theorem map_source_withDensity (f : E → ℝ≥0∞) :
    (S.diagonalEnvelope.γE.withDensity (fun x => f (S.envelopeToSource x))).map S.envelopeToSource =
      S.gamma.withDensity f := by
  rw [← S.envelopeToSource_map]
  ext A hA
  rw [Measure.map_apply S.envelopeToSource.continuous.measurable hA,
    withDensity_apply _ (S.envelopeToSource.continuous.measurable hA), withDensity_apply _ hA,
    ← lintegral_indicator (S.envelopeToSource.continuous.measurable hA),
    ← lintegral_indicator hA, S.measurableEmbedding_envelopeToSource.lintegral_map]
  rfl

theorem coord_add (x y : E) (n : ℤ) : S.coord (x + y) n = S.coord x n + S.coord y n := by
  change (coordC38 1 n) (S.toH1 (x + y)) =
    (coordC38 1 n) (S.toH1 x) + (coordC38 1 n) (S.toH1 y)
  rw [map_add, map_add]

theorem headMap_eq_truncField (T : E ≃ₜ E) (K : E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x)) (N : ℕ) (v : S.Head N) :
    S.envelopeHeadEquiv N (S.headMap T N v) = S.envelopeHeadEquiv N v +
      S.diagonalEnvelope.truncField (S.envelopeField K) N (S.envelopeHeadEquiv N v) := by
  apply Subtype.ext
  apply S.diagonalEnvelope.hcoord_ext
  intro n
  have hcoe (w : S.Head N) :
      S.diagonalEnvelope.hcoord (S.envelopeHeadEquiv N w : S.diagonalEnvelope.H) n =
        S.rates.cmProvider.hcoord (w : S.H) n :=
    (congrArg (fun h : S.diagonalEnvelope.H => S.diagonalEnvelope.hcoord h n)
      (S.envelopeHeadEquiv_coe N w)).trans (S.envelopeCMEquiv_hcoord (w : S.H) n)
  have hp : S.coord (T (S.incl (v : S.H))) n =
      S.rates.cmProvider.hcoord (v : S.H) n + S.rates.cmProvider.hcoord (K (S.incl (v : S.H))) n := by
    calc
      S.coord (T (S.incl (v : S.H))) n =
          S.coord (S.incl (v : S.H) + S.incl (K (S.incl (v : S.H)))) n :=
        congrArg (fun x => S.coord x n) (hT _)
      _ = S.coord (S.incl (v : S.H)) n + S.coord (S.incl (K (S.incl (v : S.H)))) n := S.coord_add _ _ n
      _ = _ := congrArg₂ (· + ·) (S.incl_coordinates _ n) (S.incl_coordinates _ n)
  have ht : S.diagonalEnvelope.hcoord
      (S.diagonalEnvelope.truncField (S.envelopeField K) N (S.envelopeHeadEquiv N v) :
        S.diagonalEnvelope.H) n =
      if n ∈ symmetricModes N then S.rates.cmProvider.hcoord (K (S.incl (v : S.H))) n else 0 := by
    calc
      _ = (if n ∈ symmetricModes N then S.diagonalEnvelope.hcoord
          (S.envelopeField K (S.diagonalEnvelope.headToE N (S.envelopeHeadEquiv N v))) n else 0) :=
        S.diagonalEnvelope.hcoord_cmTrunc N _ n
      _ = (if n ∈ symmetricModes N then S.rates.cmProvider.hcoord
          (K (S.envelopeToSource (S.diagonalEnvelope.headToE N (S.envelopeHeadEquiv N v)))) n else 0) :=
        congrArg (fun z : ℂ => if n ∈ symmetricModes N then z else 0) (S.envelopeCMEquiv_hcoord _ n)
      _ = _ := congrArg (fun x : E =>
        if n ∈ symmetricModes N then S.rates.cmProvider.hcoord (K x) n else 0)
        (S.envelopeToSource_headToE N v)
  calc
    S.diagonalEnvelope.hcoord (S.envelopeHeadEquiv N (S.headMap T N v) : S.diagonalEnvelope.H) n =
        S.rates.cmProvider.hcoord (S.headMap T N v : S.H) n := hcoe _
    _ = (if n ∈ symmetricModes N then S.coord (T (S.incl (v : S.H))) n else 0) :=
      S.rates.cmProvider.hcoord_headPt N _ n
    _ = (if n ∈ symmetricModes N then S.rates.cmProvider.hcoord (v : S.H) n +
        S.rates.cmProvider.hcoord (K (S.incl (v : S.H))) n else 0) :=
      congrArg (fun z : ℂ => if n ∈ symmetricModes N then z else 0) hp
    _ = S.rates.cmProvider.hcoord (v : S.H) n +
        (if n ∈ symmetricModes N then S.rates.cmProvider.hcoord (K (S.incl (v : S.H))) n else 0) := by
      by_cases hn : n ∈ symmetricModes N
      · simp only [if_pos hn]
      · simp only [if_neg hn, v.2 n hn, zero_add]
    _ = S.diagonalEnvelope.hcoord (S.envelopeHeadEquiv N v : S.diagonalEnvelope.H) n +
        S.diagonalEnvelope.hcoord (S.diagonalEnvelope.truncField (S.envelopeField K) N
          (S.envelopeHeadEquiv N v) : S.diagonalEnvelope.H) n :=
      congrArg₂ (· + ·) (hcoe v).symm ht.symm
    _ = _ := (S.diagonalEnvelope.hcoord_add _ _ n).symm

/-- The nonlinear homeomorphism lifts to the stronger diagonal space because
    both displacements take values in the unchanged CM space. -/
def liftedHomeomorph (T : E ≃ₜ E) (K Kinv : E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTi : ∀ x, T.symm x = x + S.incl (Kinv x))
    (hK : Continuous K) (hKi : Continuous Kinv) :
    S.diagonalEnvelope.E ≃ₜ S.diagonalEnvelope.E where
  toFun x := x + S.diagonalEnvelope.incl (S.envelopeCMEquiv (K (S.envelopeToSource x)))
  invFun x := x + S.diagonalEnvelope.incl (S.envelopeCMEquiv (Kinv (S.envelopeToSource x)))
  left_inv x := by
    apply S.envelopeToSource_injective
    have hf (y : S.diagonalEnvelope.E) :
        S.envelopeToSource (y + S.diagonalEnvelope.incl (S.envelopeCMEquiv (K (S.envelopeToSource y)))) =
          T (S.envelopeToSource y) := by
      rw [map_add, S.envelopeToSource_incl]
      exact (hT _).symm
    have hi (y : S.diagonalEnvelope.E) :
        S.envelopeToSource (y + S.diagonalEnvelope.incl (S.envelopeCMEquiv (Kinv (S.envelopeToSource y)))) =
          T.symm (S.envelopeToSource y) := by
      rw [map_add, S.envelopeToSource_incl]
      exact (hTi _).symm
    calc
      _ = T.symm (S.envelopeToSource (x + S.diagonalEnvelope.incl (S.envelopeCMEquiv (K (S.envelopeToSource x))))) := hi _
      _ = T.symm (T (S.envelopeToSource x)) := congrArg T.symm (hf x)
      _ = S.envelopeToSource x := T.symm_apply_apply _
  right_inv x := by
    apply S.envelopeToSource_injective
    have hf (y : S.diagonalEnvelope.E) :
        S.envelopeToSource (y + S.diagonalEnvelope.incl (S.envelopeCMEquiv (K (S.envelopeToSource y)))) =
          T (S.envelopeToSource y) := by
      rw [map_add, S.envelopeToSource_incl]
      exact (hT _).symm
    have hi (y : S.diagonalEnvelope.E) :
        S.envelopeToSource (y + S.diagonalEnvelope.incl (S.envelopeCMEquiv (Kinv (S.envelopeToSource y)))) =
          T.symm (S.envelopeToSource y) := by
      rw [map_add, S.envelopeToSource_incl]
      exact (hTi _).symm
    calc
      _ = T (S.envelopeToSource (x + S.diagonalEnvelope.incl (S.envelopeCMEquiv (Kinv (S.envelopeToSource x))))) := hf _
      _ = T (T.symm (S.envelopeToSource x)) := congrArg T (hi x)
      _ = S.envelopeToSource x := T.apply_symm_apply _
  continuous_toFun := continuous_id.add (S.diagonalEnvelope.incl.continuous.comp
    (S.envelopeCMEquiv.continuous.comp (hK.comp S.envelopeToSource.continuous)))
  continuous_invFun := continuous_id.add (S.diagonalEnvelope.incl.continuous.comp
    (S.envelopeCMEquiv.continuous.comp (hKi.comp S.envelopeToSource.continuous)))

theorem liftedHomeomorph_symm_commutes (T : E ≃ₜ E) (K Kinv : E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTi : ∀ x, T.symm x = x + S.incl (Kinv x))
    (hK : Continuous K) (hKi : Continuous Kinv) (x : S.diagonalEnvelope.E) :
    S.envelopeToSource ((S.liftedHomeomorph T K Kinv hT hTi hK hKi).symm x) =
      T.symm (S.envelopeToSource x) := by
  change S.envelopeToSource (x + S.diagonalEnvelope.incl (S.envelopeCMEquiv (Kinv (S.envelopeToSource x)))) = _
  rw [map_add, S.envelopeToSource_incl]
  exact (hTi _).symm

/-- The exact HS conjugacy under the explicit CM isometry. -/
theorem hsDerivH_envelope (K : E → S.H) (hK : Differentiable ℝ K)
    (x : S.diagonalEnvelope.E) :
    S.diagonalEnvelope.hsDerivH (S.envelopeField K) x =
      HilbertSchmidt.transport (S.hDerivative K (S.envelopeToSource x))
        S.envelopeCMEquiv S.envelopeCMEquiv := by
  apply HilbertSchmidt.ext
  intro h
  have hc := S.fderiv_envelopeField K hK x
  have he₁ := congrArg (fun A : S.diagonalEnvelope.H →L[ℝ] S.diagonalEnvelope.H => A h)
    (S.diagonalEnvelope.hsDerivH_toCLM (S.envelopeField K) x)
  have he₂ := congrArg (fun A : S.diagonalEnvelope.E →L[ℝ] S.diagonalEnvelope.H =>
    A (S.diagonalEnvelope.incl h)) hc
  have he₃ := congrArg (fun y : E => S.envelopeCMEquiv (fderiv ℝ K (S.envelopeToSource x) y))
    (S.envelopeToSource_incl_symm h)
  have he₄ := congrArg (fun A : S.H →L[ℝ] S.H =>
    S.envelopeCMEquiv (A (S.envelopeCMEquiv.symm h)))
    (S.hDerivative_toCLM K (S.envelopeToSource x))
  have he₅ := congrArg (fun A : S.diagonalEnvelope.H →L[ℝ] S.diagonalEnvelope.H => A h)
    (HilbertSchmidt.toCLM_transport (S.hDerivative K (S.envelopeToSource x))
      S.envelopeCMEquiv S.envelopeCMEquiv)
  exact he₁.trans (he₂.trans (he₃.trans (he₄.symm.trans he₅.symm)))

end SourceShellGaussianSetting

open SourceShellGaussianSetting


/-- The full v2:545-566 Ramer theorem for the source space with coupled
    symmetric shells. The same d and J satisfy every conclusion. -/
theorem grouped_ramer_shell_general
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] (S : SourceShellGaussianSetting E)
    (T : E ≃ₜ E) (K Kinv : E → S.H)
    (hK : AnalyticOnNhd ℝ K Set.univ) (hKi : AnalyticOnNhd ℝ Kinv Set.univ)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTi : ∀ x, T.symm x = x + S.incl (Kinv x)) :
    ∃ d : E → ℝ, S.SourceLocalDivergence K d ∧
      let J := fun x => |det2 (S.hDerivative K x)| * Real.exp (-d x - ‖K x‖ ^ 2 / 2)
      S.gamma.map T.symm = S.gamma.withDensity (fun x => ENNReal.ofReal (J x)) ∧
      (∀ᵐ x ∂S.gamma, 0 < J x) ∧ Integrable J S.gamma ∧
      (∫ x, J x ∂S.gamma) = 1 ∧
      TendstoInMeasure S.gamma (S.cylindricalJacobian T) atTop J := by
  have hK2 : ContDiff ℝ 2 K := hK.contDiff
  have hKi2 : ContDiff ℝ 2 Kinv := hKi.contDiff
  have hKd : Differentiable ℝ K := hK2.differentiable (by norm_num)
  let Kp : S.diagonalEnvelope.E → S.diagonalEnvelope.H := S.envelopeField K
  let Kip : S.diagonalEnvelope.E → S.diagonalEnvelope.H := S.envelopeField Kinv
  have hKp : ContDiff ℝ 2 Kp := S.contDiff_envelopeField K hK2
  have hKip : ContDiff ℝ 2 Kip := S.contDiff_envelopeField Kinv hKi2
  let Tp := S.liftedHomeomorph T K Kinv hT hTi hK2.continuous hKi2.continuous
  obtain ⟨δ, hδ₂, hδ₃, hmap, hpos, hint, hmass, hconv⟩ :=
    S.diagonalEnvelope.ramer_general Tp Kp Kip (fun x => rfl) (fun x => rfl) hKp hKip
  let d : E → ℝ := fun x => δ (S.coord x)
  let J : E → ℝ := fun x => |det2 (S.hDerivative K x)| * Real.exp (-d x - ‖K x‖ ^ 2 / 2)
  let Jp : S.diagonalEnvelope.E → ℝ := fun x =>
    |det2 (S.diagonalEnvelope.hsDerivH Kp x)| *
      Real.exp (-δ (S.diagonalEnvelope.coordE x) - ‖Kp x‖ ^ 2 / 2)
  have hJ (x : S.diagonalEnvelope.E) : Jp x = J (S.envelopeToSource x) := by
    have hc : S.coord (S.envelopeToSource x) = S.diagonalEnvelope.coordE x :=
      funext fun n => S.envelopeToSource_coord x n
    have hd : |det2 (S.diagonalEnvelope.hsDerivH Kp x)| =
        |det2 (S.hDerivative K (S.envelopeToSource x))| :=
      (congrArg (fun A : HilbertSchmidt S.diagonalEnvelope.H S.diagonalEnvelope.H => |det2 A|)
        (S.hsDerivH_envelope K hKd x)).trans
        (congrArg abs (det2_transport (S.hDerivative K (S.envelopeToSource x)) S.envelopeCMEquiv))
    have hn : ‖Kp x‖ = ‖K (S.envelopeToSource x)‖ := S.envelopeCMEquiv.norm_map _
    have he : Real.exp (-δ (S.diagonalEnvelope.coordE x) - ‖Kp x‖ ^ 2 / 2) =
        Real.exp (-δ (S.coord (S.envelopeToSource x)) - ‖K (S.envelopeToSource x)‖ ^ 2 / 2) :=
      congrArg₂ (fun (z : ℤ → ℂ) (a : ℝ) => Real.exp (-δ z - a ^ 2 / 2)) hc.symm hn
    exact congrArg₂ (· * ·) hd he
  have hLocal : S.SourceLocalDivergence K d := by
    constructor
    · exact S.exists_source_local_closedDivergence K hK2
    · intro x₀ r G η hEq hCD
      apply (S.ae_realization_iff _).2
      have hraw := (S.sourceClosedDivergence_iff_raw G η).1 hCD
      have hop : IsOpen (S.envelopeToSource ⁻¹' Metric.ball x₀ r) :=
        Metric.isOpen_ball.preimage S.envelopeToSource.continuous
      have heq : Set.EqOn (S.envelopeField G) Kp
          (S.envelopeToSource ⁻¹' Metric.ball x₀ r) :=
        fun x hx => congrArg S.envelopeCMEquiv (hEq hx)
      have hh := S.envelope_divergence_compatible_open Kp hKp δ hδ₃ _ hop
        (S.envelopeField G) (fun z => η (S.realization z)) heq hraw
      filter_upwards [hh, S.coord_realization_ae] with z hz hzc hzb
      change δ (S.coord (S.realization z)) = η (S.realization z)
      rw [hzc]
      exact hz hzb
  have hInt : Integrable J S.gamma := by
    rw [← S.envelopeToSource_map]
    apply S.measurableEmbedding_envelopeToSource.integrable_map_iff.2
    exact hint.congr (Eventually.of_forall hJ)
  have hMap : S.gamma.map T.symm = S.gamma.withDensity (fun x => ENNReal.ofReal (J x)) := by
    have hh := congrArg (fun μ : Measure S.diagonalEnvelope.E => μ.map S.envelopeToSource) hmap
    have hcomm : S.envelopeToSource ∘ Tp.symm = T.symm ∘ S.envelopeToSource := by
      funext x
      exact S.liftedHomeomorph_symm_commutes T K Kinv hT hTi hK2.continuous hKi2.continuous x
    have hD : S.diagonalEnvelope.γE.withDensity (fun x => ENNReal.ofReal (Jp x)) =
        S.diagonalEnvelope.γE.withDensity (fun x => ENNReal.ofReal (J (S.envelopeToSource x))) := by
      congr 1
      funext x
      exact congrArg ENNReal.ofReal (hJ x)
    change (S.diagonalEnvelope.γE.map Tp.symm).map S.envelopeToSource =
      (S.diagonalEnvelope.γE.withDensity (fun x => ENNReal.ofReal (Jp x))).map S.envelopeToSource at hh
    rw [Measure.map_map S.envelopeToSource.continuous.measurable Tp.symm.continuous.measurable,
      hcomm, ← Measure.map_map T.symm.continuous.measurable S.envelopeToSource.continuous.measurable,
      S.envelopeToSource_map, hD] at hh
    exact hh.trans (S.map_source_withDensity (fun x => ENNReal.ofReal (J x)))
  refine ⟨d, hLocal, hMap, ?_, hInt, ?_, ?_⟩
  · exact Eventually.of_forall (fun x => S.ramerJacobian_pos T K Kinv hT hTi hKd
      (hKi2.differentiable (by norm_num)) d x)
  · calc
      (∫ x, J x ∂S.gamma) = ∫ x, J (S.envelopeToSource x) ∂S.diagonalEnvelope.γE := by
        rw [← S.envelopeToSource_map]
        exact S.measurableEmbedding_envelopeToSource.integral_map _
      _ = ∫ x, Jp x ∂S.diagonalEnvelope.γE := integral_congr_ae (Eventually.of_forall fun x => (hJ x).symm)
      _ = 1 := hmass
  · have hF (N : ℕ) : S.envelopeProfile N (S.headMap T N) =
        fun v => v + S.diagonalEnvelope.truncField Kp N v := by
      funext v
      have he := S.headMap_eq_truncField T K hT N ((S.envelopeHeadEquiv N).symm v)
      exact he.trans (congrArg (fun w : S.diagonalEnvelope.head N =>
        w + S.diagonalEnvelope.truncField Kp N w) ((S.envelopeHeadEquiv N).apply_symm_apply v))
    intro ε hε
    refine (hconv ε hε).congr (fun N => ?_)
    calc
      _ = countableComplexGaussian S.rates.q
          {z | ε ≤ edist (S.cylindricalJacobian T N (S.realization z)) (J (S.realization z))} := by
        apply measure_congr
        filter_upwards [S.headPt_realization_ae N] with z hz
        have hJac : finiteRamerDensity (fun v => v + S.diagonalEnvelope.truncField Kp N v)
            (S.diagonalEnvelope.headPt N z) = S.cylindricalJacobian T N (S.realization z) :=
          (congrArg (fun g : S.diagonalEnvelope.head N → S.diagonalEnvelope.head N =>
            finiteRamerDensity g (S.diagonalEnvelope.headPt N z)) (hF N).symm).trans
            ((congrArg (finiteRamerDensity (S.envelopeProfile N (S.headMap T N))) hz.symm).trans
              (S.envelopeProfile_finiteRamerDensity N (S.headMap T N) (S.headPt N (S.realization z))))
        exact congrArg₂ (fun a b : ℝ => ε ≤ edist a b) hJac (hJ (S.diagonalEnvelope.R z))
      _ = S.gamma {x | ε ≤ edist (S.cylindricalJacobian T N x) (J x)} :=
        (S.measure_realization_preimage {x | ε ≤ edist (S.cylindricalJacobian T N x) (J x)}).symm

end NlsGge.ThirdConsultation.Narrative
