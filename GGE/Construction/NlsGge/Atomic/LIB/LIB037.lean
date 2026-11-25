import NlsGge.Atomic.LIB.LIB036
import NlsGge.Atomic.LIB.LIB032
import Mathlib.Analysis.Normed.Lp.lpHolder


/-!
# LIB-037: the actual free resolvent on the imaginary axis

The bounded diagonal multiplier in the genuine free Fourier basis is transferred
to SourcePairL2. Its pairing against every vector in the actual operator domain
places its image in the adjoint domain; the proved selfadjoint realization then
gives genuine H1 membership and the action. Both inverse equations use the
source sign convention (iR - A)⁻¹.

The diagonal and weighted diagonal bounds give value norm at most ‖f‖/R and
weak derivative norm at most ‖f‖. The proved squared Sobolev inequality yields
the canonical Euclidean representative bound sqrt(3)/sqrt(R), uniformly over
all four boundary conditions. Its continuous-map-valued realization records
the interval L∞ estimate on the same actual L2 image.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace NlsGge.Atomic.LIB037
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB026 NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB036

def axisDenominator (R a : ℝ) : ℂ := Complex.I * (R : ℂ) - (a : ℂ)
lemma axisDenominator_norm_sq (R a : ℝ) : ‖axisDenominator R a‖ ^ 2 = R ^ 2 + a ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [axisDenominator, Complex.mul_re, Complex.mul_im, pow_two]
  ring
lemma axisDenominator_norm_lower {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    R ≤ ‖axisDenominator R a‖ := by
  have hs := axisDenominator_norm_sq R a
  have hn := norm_nonneg (axisDenominator R a)
  nlinarith [sq_nonneg a]
lemma axisDenominator_ne_zero {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    axisDenominator R a ≠ 0 := by
  intro hz
  have h := axisDenominator_norm_lower hR a
  rw [hz, norm_zero] at h
  linarith
lemma axisInverse_bound {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    ‖(axisDenominator R a)⁻¹‖ ≤ R⁻¹ := by
  rw [norm_inv]
  exact (inv_le_inv₀
    (lt_of_lt_of_le (by linarith : (0 : ℝ) < R) (axisDenominator_norm_lower hR a))
    (by linarith)).mpr (axisDenominator_norm_lower hR a)
lemma axisWeightedInverse_bound {R : ℝ} (hR : 1 ≤ R) (a : ℝ) :
    ‖(a : ℂ) * (axisDenominator R a)⁻¹‖ ≤ 1 := by
  have hn := norm_nonneg (axisDenominator R a)
  have hsq := axisDenominator_norm_sq R a
  have hab : |a| ≤ ‖axisDenominator R a‖ := by nlinarith [sq_abs a, sq_nonneg R]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv]
  exact (mul_inv_le_iff₀ (lt_of_lt_of_le (by linarith : (0 : ℝ) < R)
    (axisDenominator_norm_lower hR a))).mpr (by simpa using hab)

def freeEigenvalueReal (bc : ZSBoundaryCondition) (i : FreeIndex bc) : ℝ :=
  (freeFrequency bc i : ℝ) * Real.pi
lemma freeEigenvalue_eq_real (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    freeEigenvalue bc i = (freeEigenvalueReal bc i : ℂ) := by
  simp [freeEigenvalue, freeEigenvalueReal]
lemma star_freeEigenvalue (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    star (freeEigenvalue bc i) = freeEigenvalue bc i := by
  rw [freeEigenvalue_eq_real]
  exact Complex.conj_ofReal _

def axisCoefficient (bc : ZSBoundaryCondition) (R : ℝ) (i : FreeIndex bc) : ℂ :=
  (axisDenominator R (freeEigenvalueReal bc i))⁻¹
abbrev FreeSquare (bc : ZSBoundaryCondition) := lp (fun _ : FreeIndex bc => ℂ) 2

def freeDiagonal (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    FreeSquare bc →L[ℂ] FreeSquare bc :=
  lp.mapCLM 2 (fun i => axisCoefficient bc R i • ContinuousLinearMap.id ℂ ℂ)
    (inv_nonneg.mpr (by linarith) : 0 ≤ R⁻¹) (fun i => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, axisCoefficient] using
        axisInverse_bound hR (freeEigenvalueReal bc i))
def freeWeightedDiagonal (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    FreeSquare bc →L[ℂ] FreeSquare bc :=
  lp.mapCLM 2 (fun i => (freeEigenvalue bc i * axisCoefficient bc R i) •
    ContinuousLinearMap.id ℂ ℂ) zero_le_one (fun i => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, axisCoefficient,
        freeEigenvalue_eq_real] using axisWeightedInverse_bound hR (freeEigenvalueReal bc i))
lemma freeDiagonal_norm_le (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    ‖freeDiagonal bc R hR‖ ≤ R⁻¹ := lp.norm_mapCLM_le 2 _ _ _
lemma freeWeightedDiagonal_norm_le (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    ‖freeWeightedDiagonal bc R hR‖ ≤ 1 := lp.norm_mapCLM_le 2 _ _ _

def freeZSResolvent (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (freeZSBasis bc).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((freeDiagonal bc R hR).comp (freeZSBasis bc).repr.toContinuousLinearEquiv.toContinuousLinearMap)
def freeZSActionImage (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (freeZSBasis bc).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((freeWeightedDiagonal bc R hR).comp (freeZSBasis bc).repr.toContinuousLinearEquiv.toContinuousLinearMap)
lemma freeZSResolvent_repr (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) (i : FreeIndex bc) :
    (freeZSBasis bc).repr (freeZSResolvent bc R hR f) i =
      axisCoefficient bc R i * (freeZSBasis bc).repr f i := by
  change (freeZSBasis bc).repr ((freeZSBasis bc).repr.symm
    (freeDiagonal bc R hR ((freeZSBasis bc).repr f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl
lemma freeZSActionImage_repr (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) (i : FreeIndex bc) :
    (freeZSBasis bc).repr (freeZSActionImage bc R hR f) i =
      (freeEigenvalue bc i * axisCoefficient bc R i) * (freeZSBasis bc).repr f i := by
  change (freeZSBasis bc).repr ((freeZSBasis bc).repr.symm
    (freeWeightedDiagonal bc R hR ((freeZSBasis bc).repr f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl
lemma freeZSResolvent_norm_apply (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : ‖freeZSResolvent bc R hR f‖ ≤ R⁻¹ * ‖f‖ := by
  change ‖(freeZSBasis bc).repr.symm (freeDiagonal bc R hR ((freeZSBasis bc).repr f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := (freeDiagonal bc R hR).le_of_opNorm_le
    (freeDiagonal_norm_le bc R hR) ((freeZSBasis bc).repr f)
  simpa only [LinearIsometryEquiv.norm_map] using h

lemma freeZSActionImage_norm_apply (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : ‖freeZSActionImage bc R hR f‖ ≤ ‖f‖ := by
  change ‖(freeZSBasis bc).repr.symm (freeWeightedDiagonal bc R hR ((freeZSBasis bc).repr f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := (freeWeightedDiagonal bc R hR).le_of_opNorm_le
    (freeWeightedDiagonal_norm_le bc R hR) ((freeZSBasis bc).repr f)
  simpa only [one_mul, LinearIsometryEquiv.norm_map] using h
lemma freeZSResolvent_norm_le (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    ‖freeZSResolvent bc R hR‖ ≤ 1 / R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one (by linarith))
  intro f
  simpa only [one_div] using freeZSResolvent_norm_apply bc R hR f

lemma zeroPotential_realType : IsRealType (0 : SourcePairL2) := by
  unfold IsRealType
  change (0 : SourceIntervalL2) = star (0 : SourceIntervalL2)
  apply Lp.ext
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)),
    Lp.coeFn_star (0 : SourceIntervalL2)] with x hz hs
  rw [hs]
  change (0 : SourceIntervalL2) x = star ((0 : SourceIntervalL2) x)
  rw [hz]
  exact (star_zero ℂ).symm

lemma free_action_repr (bc : ZSBoundaryCondition)
    (u : (zsRealization 0 bc).domain) (i : FreeIndex bc) :
    (freeZSBasis bc).repr (zsRealization 0 bc u) i =
      freeEigenvalue bc i * (freeZSBasis bc).repr (u : SourcePairL2) i := by
  rw [HilbertBasis.repr_apply_apply]
  have hs := zsRealization_formalAdjoint zeroPotential_realType bc
    ⟨freeZSBasis bc i, freeZSBasis_mem_domain bc i⟩ u
  rw [free_zs_eigenvector, inner_smul_left] at hs
  simp only [starRingEnd_apply, star_freeEigenvalue] at hs
  rw [← hs, HilbertBasis.repr_apply_apply]

lemma freeZSResolvent_domain_pairing (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) (u : (zsRealization 0 bc).domain) :
    inner ℂ (zsRealization 0 bc u) (freeZSResolvent bc R hR f) =
      inner ℂ (u : SourcePairL2) (freeZSActionImage bc R hR f) := by
  rw [← (freeZSBasis bc).repr.inner_map_map, ← (freeZSBasis bc).repr.inner_map_map]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [free_action_repr, freeZSResolvent_repr, freeZSActionImage_repr]
  simp only [RCLike.inner_apply, map_mul, starRingEnd_apply, star_freeEigenvalue]
  ring

lemma freeZSResolvent_adjoint_pairing (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) (u : (zsRealization 0 bc).domain) :
    inner ℂ (freeZSActionImage bc R hR f) (u : SourcePairL2) =
      inner ℂ (freeZSResolvent bc R hR f) (zsRealization 0 bc u) := by
  have h := congrArg (starRingEnd ℂ) (freeZSResolvent_domain_pairing bc R hR f u).symm
  simpa only [inner_conj_symm] using h

lemma freeZSResolvent_mem_adjoint (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : freeZSResolvent bc R hR f ∈ (zsRealization 0 bc).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨freeZSActionImage bc R hR f, freeZSResolvent_adjoint_pairing bc R hR f⟩

lemma free_operator_adjoint_eq (bc : ZSBoundaryCondition) :
    (zsRealization 0 bc).adjoint = zsRealization 0 bc :=
  LinearPMap.isSelfAdjoint_def.mp
    (zs_real_selfAdjoint zeroPotential_realType bc)

/-- Membership is derived from the full actual-domain pairing and proved maximality. -/
lemma freeZSResolvent_mem_domain (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : freeZSResolvent bc R hR f ∈ (zsRealization 0 bc).domain := by
  have h := freeZSResolvent_mem_adjoint bc R hR f
  rwa [free_operator_adjoint_eq] at h

set_option backward.isDefEq.respectTransparency false in
lemma freeZSResolvent_action (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) :
    zsRealization 0 bc ⟨freeZSResolvent bc R hR f, freeZSResolvent_mem_domain bc R hR f⟩ =
      freeZSActionImage bc R hR f := by
  have h := (zsRealization 0 bc).adjoint_apply_eq (zsRealization_dense 0 bc)
    (⟨freeZSResolvent bc R hR f, freeZSResolvent_mem_adjoint bc R hR f⟩)
    (freeZSResolvent_adjoint_pairing bc R hR f)
  obtain ⟨hdom, happly⟩ := LinearPMap.dExt_iff.mp (free_operator_adjoint_eq bc)
  have he := happly
    (x := ⟨freeZSResolvent bc R hR f, freeZSResolvent_mem_adjoint bc R hR f⟩)
    (y := ⟨freeZSResolvent bc R hR f, freeZSResolvent_mem_domain bc R hR f⟩) rfl
  exact he.symm.trans h

lemma freeZSActionImage_eq (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) :
    freeZSActionImage bc R hR f = (Complex.I * (R : ℂ)) • freeZSResolvent bc R hR f - f := by
  apply (freeZSBasis bc).repr.injective
  apply lp.ext
  funext i
  simp only [map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, freeZSActionImage_repr, freeZSResolvent_repr]
  have hd := axisDenominator_ne_zero hR (freeEigenvalueReal bc i)
  rw [freeEigenvalue_eq_real]
  dsimp only [axisCoefficient]
  rw [show Complex.I * (R : ℂ) =
    axisDenominator R (freeEigenvalueReal bc i) + (freeEigenvalueReal bc i : ℂ) by
    dsimp only [axisDenominator]; ring]
  field_simp [hd]
  ring

/-- The actual right inverse, with its derived source-domain membership. -/
theorem freeZSResolvent_right_inverse (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) :
    (Complex.I * (R : ℂ)) • freeZSResolvent bc R hR f -
      zsRealization 0 bc ⟨freeZSResolvent bc R hR f, freeZSResolvent_mem_domain bc R hR f⟩ = f := by
  rw [freeZSResolvent_action, freeZSActionImage_eq]
  abel

/-- The actual left inverse is proved for every vector in the full source domain. -/
theorem freeZSResolvent_left_inverse (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (u : (zsRealization 0 bc).domain) :
    freeZSResolvent bc R hR ((Complex.I * (R : ℂ)) • (u : SourcePairL2) - zsRealization 0 bc u) = u := by
  apply (freeZSBasis bc).repr.injective
  apply lp.ext
  funext i
  rw [freeZSResolvent_repr]
  simp only [map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, free_action_repr]
  have hd := axisDenominator_ne_zero hR (freeEigenvalueReal bc i)
  rw [freeEigenvalue_eq_real]
  change (axisDenominator R (freeEigenvalueReal bc i))⁻¹ *
    ((Complex.I * (R : ℂ)) * (freeZSBasis bc).repr (u : SourcePairL2) i -
      (freeEigenvalueReal bc i : ℂ) * (freeZSBasis bc).repr (u : SourcePairL2) i) = _
  rw [← sub_mul]
  change (axisDenominator R (freeEigenvalueReal bc i))⁻¹ *
    (axisDenominator R (freeEigenvalueReal bc i) * (freeZSBasis bc).repr (u : SourcePairL2) i) = _
  rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

def freeZSResolventH1 (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : H1Pair :=
  domainLift ⟨freeZSResolvent bc R hR f, freeZSResolvent_mem_domain bc R hR f⟩
lemma freeZSResolventH1_value (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : h1PairValue (freeZSResolventH1 bc R hR f) = freeZSResolvent bc R hR f :=
  domainLift_value _
lemma freeZSResolventH1_boundary (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : HasZSBoundaryCondition bc (freeZSResolventH1 bc R hR f) :=
  domainLift_boundary _
lemma freeZSResolventH1_action (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : zsApply 0 (freeZSResolventH1 bc R hR f) = freeZSActionImage bc R hR f :=
  freeZSResolvent_action bc R hR f
lemma freeZSResolventH1_derivative_norm (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : ‖pairDerivative (freeZSResolventH1 bc R hR f)‖ ≤ ‖f‖ := by
  have h := NlsGge.Atomic.LIB032.derivative_norm_le_action_add_potential
    0 (freeZSResolventH1 bc R hR f)
  simpa only [norm_zero, zero_mul, add_zero, freeZSResolventH1_action] using
    h.trans (by simpa only [norm_zero, zero_mul, add_zero, freeZSResolventH1_action] using
      freeZSActionImage_norm_apply bc R hR f)

lemma freeZSResolventH1_add (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f g : SourcePairL2) : freeZSResolventH1 bc R hR (f + g) =
      h1PairAdd (freeZSResolventH1 bc R hR f) (freeZSResolventH1 bc R hR g) := by
  apply h1PairValue_injective
  rw [h1PairValue_add, freeZSResolventH1_value, freeZSResolventH1_value,
    freeZSResolventH1_value, map_add]
lemma freeZSResolventH1_smul (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (c : ℂ) (f : SourcePairL2) : freeZSResolventH1 bc R hR (c • f) =
      h1PairSmul c (freeZSResolventH1 bc R hR f) := by
  apply h1PairValue_injective
  rw [h1PairValue_smul, freeZSResolventH1_value, freeZSResolventH1_value, map_smul]
lemma pairRepresentative_add (f g : H1Pair) :
    pairRepresentative (h1PairAdd f g) = pairRepresentative f + pairRepresentative g := by
  apply ContinuousMap.ext
  intro x
  apply PiLp.ext
  intro b
  change representative (h1Add (f b) (g b)) x =
    representative (f b) x + representative (g b) x
  rw [representative_h1Add]
  rfl
lemma pairRepresentative_smul (c : ℂ) (f : H1Pair) :
    pairRepresentative (h1PairSmul c f) = c • pairRepresentative f := by
  apply ContinuousMap.ext
  intro x
  apply PiLp.ext
  intro b
  change representative (h1Smul c (f b)) x = c * representative (f b) x
  rw [representative_h1Smul]
  rfl

/-- The actual squared Sobolev inequality gives the uniform R^(-1/2) rate. -/
theorem freeZSResolvent_representative_bound (bc : ZSBoundaryCondition)
    (R : ℝ) (hR : 1 ≤ R) (f : SourcePairL2) :
    ‖pairRepresentative (freeZSResolventH1 bc R hR f)‖ ≤
      (Real.sqrt 3 / Real.sqrt R) * ‖f‖ := by
  have hRp : 0 < R := by linarith
  have hi : 0 ≤ R⁻¹ := inv_nonneg.mpr hRp.le
  have hi1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRp).mpr hR
  have hi2 : (R⁻¹) ^ 2 ≤ R⁻¹ := by nlinarith
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  have hs := pairRepresentative_norm_sq_le (freeZSResolventH1 bc R hR f) x
  have hv : ‖h1PairValue (freeZSResolventH1 bc R hR f)‖ ≤ R⁻¹ * ‖f‖ := by
    rw [freeZSResolventH1_value]
    exact freeZSResolvent_norm_apply bc R hR f
  have hd := freeZSResolventH1_derivative_norm bc R hR f
  have hv2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hi (norm_nonneg f))).mpr hv
  have hprod := mul_le_mul hv hd (norm_nonneg _)
    (mul_nonneg hi (norm_nonneg f))
  have hsmall := mul_le_mul_of_nonneg_right hi2 (sq_nonneg ‖f‖)
  have hb : ‖pairRepresentative (freeZSResolventH1 bc R hR f) x‖ ^ 2 ≤
      (3 / R) * ‖f‖ ^ 2 := by
    simp only [div_eq_mul_inv] at ⊢
    nlinarith only [hs, hv2, hprod, hsmall]
  have he : ((Real.sqrt 3 / Real.sqrt R) * ‖f‖) ^ 2 = (3 / R) * ‖f‖ ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hRp.le]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hb.trans_eq he.symm)

def freeZSResolventToSupLinear (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    SourcePairL2 →ₗ[ℂ] C(Icc (0 : ℝ) 1, PointPair) where
  toFun f := pairRepresentative (freeZSResolventH1 bc R hR f)
  map_add' f g := by rw [freeZSResolventH1_add, pairRepresentative_add]
  map_smul' c f := by rw [freeZSResolventH1_smul, pairRepresentative_smul]; rfl

/-- Canonical continuous realization of the actual L2 resolvent image. -/
def freeZSResolventToSup (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    SourcePairL2 →L[ℂ] C(Icc (0 : ℝ) 1, PointPair) :=
  (freeZSResolventToSupLinear bc R hR).mkContinuous (Real.sqrt 3 / Real.sqrt R)
    (freeZSResolvent_representative_bound bc R hR)

/-- The constant sqrt(3) is independent of the boundary condition and input. -/
theorem free_zs_resolvent_sup_bound (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    ‖freeZSResolventToSup bc R hR‖ ≤ Real.sqrt 3 / Real.sqrt R :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem free_zs_resolvent_H1_image (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : ∃ g : H1Pair, HasZSBoundaryCondition bc g ∧
      h1PairValue g = freeZSResolvent bc R hR f ∧
      pairRepresentative g = freeZSResolventToSup bc R hR f :=
  ⟨freeZSResolventH1 bc R hR f, freeZSResolventH1_boundary bc R hR f,
    freeZSResolventH1_value bc R hR f, rfl⟩

end NlsGge.Atomic.LIB037
