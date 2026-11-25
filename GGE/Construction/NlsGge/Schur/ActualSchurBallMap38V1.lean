import NlsGge.Schur.ActualSchurOwnModeWirtinger38V1
import NlsGge.Schur.ActualSchurCanonicalAndGapLocal38V1

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace ENNReal
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

local notation "H1" => WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-!
# The finite map `Ψ_{M,N}` of F:prop:ball and its derivative bounds (S-Ψ1, F05.02-.04)

Source: `paper/v2.tex` lines 1224-1312 (F:eq:Psi, F:eq:HSJac, F:eq:traceJac).
The plane `FourierPlane N = Fin (2N+1) → ℂ` embeds into the complex H¹ carrier; `Ψ` is the
identity on modes `|n| ≤ M` and the radius-free Schur coordinate `q_n(u, ū)` on the other
modes.  `B = DΨ - I` is a real-linear map of the plane whose matrix is given over the finite real
index type `Fin (2N+1) × Fin 2` (real / imaginary parts), in the plain real basis and in the
H¹-orthonormal real basis (conjugation by `diag ⟨n_i⟩`; trace and determinant are unchanged,
operator norm is not).
-/

/-- The plane embedding. -/
def planeH1Embedding38 (N : ℕ) : FourierPlane N →L[ℂ] H1 :=
  ∑ i : Fin (2 * N + 1),
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i).smulRight
      (actualH1ModeVector38 (modeIndex N i))

theorem planeH1Embedding38_apply (N : ℕ) (z : FourierPlane N) (k : ℤ) :
    (planeH1Embedding38 N z : ℤ → ℂ) k = ∑ i : Fin (2 * N + 1), if k = modeIndex N i then z i else 0 := by
  unfold planeH1Embedding38
  simp
  let coeAdd : H1 →+ (ℤ → ℂ) := ⟨⟨fun x => (x : ℤ → ℂ), rfl⟩, fun _ _ => rfl⟩
  have h := map_sum coeAdd (fun i : Fin (2 * N + 1) => z i • actualH1ModeVector38 (modeIndex N i)) Finset.univ
  change (((∑ i, z i • actualH1ModeVector38 (modeIndex N i) : H1)) : ℤ → ℂ) k = _
  rw [show ((∑ i, z i • actualH1ModeVector38 (modeIndex N i) : H1) : ℤ → ℂ) = ∑ i, ((z i • actualH1ModeVector38 (modeIndex N i) : H1) : ℤ → ℂ) from h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change z i * (actualH1ModeVector38 (modeIndex N i) : ℤ → ℂ) k = _
  rw [actualH1ModeVector38_apply]
  split_ifs <;> simp

theorem sobolevModeWeight_one38 (n : ℤ) : sobolevModeWeight (1 : ℝ) n = 1 + (n : ℝ) ^ 2 :=
  japaneseBracket_h1_weight n

theorem planeH1Embedding38_modeIndex (N : ℕ) (z : FourierPlane N) (j : Fin (2 * N + 1)) :
    (planeH1Embedding38 N z : ℤ → ℂ) (modeIndex N j) = z j := by
  rw [planeH1Embedding38_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (modeIndex_injective N h).symm
  · simp

theorem planeH1Embedding38_off (N : ℕ) (z : FourierPlane N) (k : ℤ)
    (hk : ∀ i, k ≠ modeIndex N i) : (planeH1Embedding38 N z : ℤ → ℂ) k = 0 := by
  rw [planeH1Embedding38_apply]
  exact Finset.sum_eq_zero fun i _ => if_neg (hk i)

/-- The H¹ norm of the plane embedding: `Σ ⟨n_i⟩² |z_i|²`. -/
theorem planeH1Embedding38_norm_sq (N : ℕ) (z : FourierPlane N) :
    ‖planeH1Embedding38 N z‖ ^ 2 =
      ∑ i : Fin (2 * N + 1), (1 + (modeIndex N i : ℝ) ^ 2) * ‖z i‖ ^ 2 := by
  rw [weightedHilbert_norm_sq]
  rw [tsum_eq_sum (s := Finset.univ.image (modeIndex N))]
  · rw [Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [planeH1Embedding38_modeIndex, sobolevModeWeight_one38]
  · intro k hk
    have : ∀ i, k ≠ modeIndex N i := fun i h => hk (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h.symm⟩)
    rw [planeH1Embedding38_off N z k this]
    simp

/-- H¹ norm on the plane. -/
def planeH1Norm38 (N : ℕ) (z : FourierPlane N) : ℝ := ‖planeH1Embedding38 N z‖

/-- The physical field of a plane point. -/
def planeField38 (N : ℕ) (z : FourierPlane N) : PhysicalL2 :=
  physicalH1ComplexCarrierToL2Actual22 (planeH1Embedding38 N z)

theorem planeH1Embedding38_single (N : ℕ) (i : Fin (2 * N + 1)) :
    planeH1Embedding38 N (Pi.single i 1) = actualH1ModeVector38 (modeIndex N i) := by
  apply Subtype.ext
  funext k
  rw [planeH1Embedding38_apply, actualH1ModeVector38_apply]
  by_cases hk : k = modeIndex N i
  · subst hk
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (modeIndex_injective N h).symm
    · simp
  · rw [if_neg hk]
    exact Finset.sum_eq_zero fun j _ => by
      by_cases h : k = modeIndex N j
      · rw [if_pos h]
        have : j ≠ i := fun hji => hk (hji ▸ h)
        simp [this]
      · rw [if_neg h]

/-- The real-linear embedding of the plane into the H¹ carrier. -/
def planeH1EmbeddingR38 (N : ℕ) : FourierPlane N →L[ℝ] H1 :=
  (planeH1Embedding38 N).restrictScalars ℝ

theorem planeH1EmbeddingR38_apply (N : ℕ) (z : FourierPlane N) :
    planeH1EmbeddingR38 N z = planeH1Embedding38 N z := rfl

/-- The map `Ψ_{M,N}` of F:eq:Psi: identity on the low modes `|n| ≤ M`, `q_n` on the high ones. -/
def actualSchurBallMap38 (N M : ℕ) (z : FourierPlane N) : FourierPlane N := fun i =>
  if (modeIndex N i).natAbs ≤ M then z i
  else actualSchurQnCanonical38 (modeIndex N i)
    (planeH1Embedding38 N z, actualH1Conj38 (planeH1Embedding38 N z))

theorem actualSchurBallMap38_low (N M : ℕ) (z : FourierPlane N) (i : Fin (2 * N + 1))
    (h : (modeIndex N i).natAbs ≤ M) : actualSchurBallMap38 N M z i = z i := by
  simp [actualSchurBallMap38, h]

theorem actualSchurBallMap38_high (N M : ℕ) (z : FourierPlane N) (i : Fin (2 * N + 1))
    (h : ¬ (modeIndex N i).natAbs ≤ M) :
    actualSchurBallMap38 N M z i = actualSchurQnCanonical38 (modeIndex N i)
      (planeH1Embedding38 N z, actualH1Conj38 (planeH1Embedding38 N z)) := by
  simp [actualSchurBallMap38, h]

theorem natAbs_gt_abs38 (M : ℕ) (n : ℤ) (h : ¬ n.natAbs ≤ M) : (M : ℝ) + 1 ≤ |(n : ℝ)| := by
  have h1 : M + 1 ≤ n.natAbs := by omega
  have h2 : ((M + 1 : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast h1
  have h3 : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  push_cast at h2
  linarith

/-- Off the diagonal identity: for high `i` and `‖embed z‖ ≤ 4R`, `Ψ_i(z) - z_i` is the
real-type remainder at radius `4R`. -/
theorem actualSchurBallMap38_high_sub (N M : ℕ) (R : ℝ) (hR : 1 ≤ R) (i : Fin (2 * N + 1))
    (hi : ¬ (modeIndex N i).natAbs ≤ M)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ ≤ 4 * R) :
    actualSchurBallMap38 N M z i - z i =
      actualSchurQnRealRemainder38 (4 * R) (modeIndex N i) (planeH1Embedding38 N z) := by
  have h4R : 1 ≤ 4 * R := by linarith
  have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |((modeIndex N i : ℤ) : ℝ)| := by
    have := natAbs_gt_abs38 M _ hi
    linarith
  have hc := actualSchurQnCanonical38_eq (4 * R) h4R (modeIndex N i) hthr
    (planeH1Embedding38 N z, actualH1Conj38 (planeH1Embedding38 N z)) hz
    (by rw [actualH1Conj38_norm]; exact hz)
  have hz' := planeH1Embedding38_modeIndex N z i
  rw [actualSchurBallMap38_high N M z i hi, hc]
  unfold actualSchurQnRealRemainder38
  rw [hz']

theorem planeH1Embedding38_continuous (N : ℕ) : Continuous (planeH1Embedding38 N) :=
  (planeH1Embedding38 N).continuous

/-- Componentwise derivative of `Ψ`. -/
def actualSchurBallMapRowDeriv38 (N M : ℕ) (R : ℝ) (z : FourierPlane N)
    (i : Fin (2 * N + 1)) : FourierPlane N →L[ℝ] ℂ :=
  if (modeIndex N i).natAbs ≤ M then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i
  else
    (fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) (modeIndex N i))
        (planeH1Embedding38 N z)).comp (planeH1EmbeddingR38 N) +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i

theorem actualSchurBallMap38_hasFDerivAt (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) :
    HasFDerivAt (actualSchurBallMap38 N M)
      (ContinuousLinearMap.pi (actualSchurBallMapRowDeriv38 N M R z)) z := by
  have h4R : 1 ≤ 4 * R := by linarith
  have hRpos : 0 < R := by linarith
  change HasFDerivAt (fun z' i => actualSchurBallMap38 N M z' i) _ z
  rw [hasFDerivAt_pi]
  intro i
  by_cases hi : (modeIndex N i).natAbs ≤ M
  · have hlow : (fun z' : FourierPlane N => actualSchurBallMap38 N M z' i) =
        fun z' => z' i := funext fun z' => actualSchurBallMap38_low N M z' i hi
    rw [hlow]
    simp only [actualSchurBallMapRowDeriv38, hi, if_true]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i).hasFDerivAt
  · have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤
        |((modeIndex N i : ℤ) : ℝ)| := by
      have := natAbs_gt_abs38 M _ hi
      linarith
    have hRem := actualSchurQnRealRemainder38_differentiableAt (4 * R) h4R (modeIndex N i) hthr
      (planeH1Embedding38 N z) (by linarith)
    have hc := HasFDerivAt.comp (g := actualSchurQnRealRemainder38 (4 * R) (modeIndex N i))
      (f := fun z' : FourierPlane N => planeH1EmbeddingR38 N z') z
      (by exact hRem.hasFDerivAt) (planeH1EmbeddingR38 N).hasFDerivAt
    have hp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * N + 1) => ℂ) i).hasFDerivAt
      (x := z)
    have hsum := hc.add hp
    have hev : (fun z' : FourierPlane N => actualSchurBallMap38 N M z' i) =ᶠ[nhds z]
        (actualSchurQnRealRemainder38 (4 * R) (modeIndex N i) ∘
          (fun z' : FourierPlane N => planeH1EmbeddingR38 N z') + fun z' => z' i) := by
      have hopen : IsOpen {z' : FourierPlane N | ‖planeH1Embedding38 N z'‖ < 4 * R} :=
        isOpen_lt ((planeH1Embedding38_continuous N).norm) continuous_const
      filter_upwards [hopen.mem_nhds (show ‖planeH1Embedding38 N z‖ < 4 * R by linarith)]
        with z' hz'
      have := actualSchurBallMap38_high_sub N M R hR i hi hM z' (le_of_lt hz')
      simp only [Pi.add_apply, Function.comp]
      rw [planeH1EmbeddingR38_apply, ← this]; ring
    simp only [actualSchurBallMapRowDeriv38, hi, if_false]
    exact hsum.congr_of_eventuallyEq hev

/-- `B = DΨ - I` as a real-linear map of the plane (plain real structure). -/
def actualSchurBallMapB38 (N M : ℕ) (z : FourierPlane N) :
    FourierPlane N →L[ℝ] FourierPlane N :=
  fderiv ℝ (actualSchurBallMap38 N M) z - ContinuousLinearMap.id ℝ (FourierPlane N)

theorem actualSchurBallMapB38_apply_low (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) (w : FourierPlane N)
    (i : Fin (2 * N + 1)) (hi : (modeIndex N i).natAbs ≤ M) :
    actualSchurBallMapB38 N M z w i = 0 := by
  have h := actualSchurBallMap38_hasFDerivAt N M R hR hM z hz
  unfold actualSchurBallMapB38
  rw [h.fderiv]
  simp [actualSchurBallMapRowDeriv38, hi]

theorem actualSchurBallMapB38_apply_high (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) (w : FourierPlane N)
    (i : Fin (2 * N + 1)) (hi : ¬ (modeIndex N i).natAbs ≤ M) :
    actualSchurBallMapB38 N M z w i =
      fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) (modeIndex N i))
        (planeH1Embedding38 N z) (planeH1Embedding38 N w) := by
  have h := actualSchurBallMap38_hasFDerivAt N M R hR hM z hz
  unfold actualSchurBallMapB38
  rw [h.fderiv]
  simp [actualSchurBallMapRowDeriv38, hi, planeH1EmbeddingR38_apply]

/-- Row bound (F:eq:qCauchy, second inequality, on the plane): for a high output row the
complex-valued real-linear row of `B` has H¹-operator norm at most `C (4R)^4/n^2/R`. -/
theorem actualSchurBallMapB38_row_bound (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) (w : FourierPlane N)
    (i : Fin (2 * N + 1)) (hi : ¬ (modeIndex N i).natAbs ≤ M) :
    ‖actualSchurBallMapB38 N M z w i‖ ≤
      (actualSchurBremConstant38 * (4 * R) ^ 4 / |((modeIndex N i : ℤ) : ℝ)| ^ 2 / R) *
        ‖planeH1Embedding38 N w‖ := by
  have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤
      |((modeIndex N i : ℤ) : ℝ)| := by
    have := natAbs_gt_abs38 M _ hi
    linarith
  rw [actualSchurBallMapB38_apply_high N M R hR hM z hz w i hi]
  exact (ContinuousLinearMap.le_of_opNorm_le _
    (actualSchurQnRealRemainder38_fderiv_norm_le R hR (modeIndex N i) hthr _ hz.le) _)

/-! ### Real matrices -/

/-- The finite real index type `Fin (2N+1) × Fin 2` (real / imaginary parts). -/
abbrev PlaneRealIndex38 (N : ℕ) := Fin (2 * N + 1) × Fin 2

/-- The plain real coordinate basis of `FourierPlane N ≅ ℝ^{2(2N+1)}`: index `(i, 0)` is the
real part of coordinate `i`, `(i, 1)` the imaginary part. -/
def planeRealBasis38 (N : ℕ) : Module.Basis (PlaneRealIndex38 N) ℝ (FourierPlane N) :=
  (Pi.basis fun _ : Fin (2 * N + 1) => Complex.basisOneI).reindex
    (Equiv.sigmaEquivProd (Fin (2 * N + 1)) (Fin 2))

theorem planeRealBasis38_repr (N : ℕ) (w : FourierPlane N) (i : Fin (2 * N + 1)) (a : Fin 2) :
    (planeRealBasis38 N).repr w (i, a) = ![(w i).re, (w i).im] a := by
  unfold planeRealBasis38
  rw [Module.Basis.repr_reindex_apply, Pi.basis_repr]
  simp [Complex.coe_basisOneI_repr]

/-- The scale `⟨n_i⟩ = (1 + n_i²)^{1/2}` converting plain real coordinates to the
H¹-orthonormal real coordinates. -/
def planeH1Scale38 (N : ℕ) (r : PlaneRealIndex38 N) : ℝ :=
  Real.sqrt (1 + ((modeIndex N r.1 : ℤ) : ℝ) ^ 2)

theorem planeH1Scale38_pos (N : ℕ) (r : PlaneRealIndex38 N) : 0 < planeH1Scale38 N r := by
  unfold planeH1Scale38
  exact Real.sqrt_pos.2 (by positivity)

theorem planeH1Scale38_sq (N : ℕ) (r : PlaneRealIndex38 N) :
    planeH1Scale38 N r ^ 2 = 1 + ((modeIndex N r.1 : ℤ) : ℝ) ^ 2 := by
  unfold planeH1Scale38
  exact Real.sq_sqrt (by positivity)

/-- The matrix of `B = DΨ - I` in the plain real coordinate basis. -/
def actualSchurBallMapPlainMatrix38 (N M : ℕ) (z : FourierPlane N) :
    Matrix (PlaneRealIndex38 N) (PlaneRealIndex38 N) ℝ :=
  LinearMap.toMatrix (planeRealBasis38 N) (planeRealBasis38 N)
    (actualSchurBallMapB38 N M z : FourierPlane N →ₗ[ℝ] FourierPlane N)

/-- The matrix of `B = DΨ - I` in the H¹-ORTHONORMAL real basis
`ε_{(i,a)} = ⟨n_i⟩⁻¹ · (1 or I) δ_i` (entry `⟨n_r⟩ B_{rc} ⟨n_c⟩⁻¹`). -/
def actualSchurBallMapH1Matrix38 (N M : ℕ) (z : FourierPlane N) :
    Matrix (PlaneRealIndex38 N) (PlaneRealIndex38 N) ℝ :=
  fun r c => planeH1Scale38 N r * actualSchurBallMapPlainMatrix38 N M z r c / planeH1Scale38 N c

theorem actualSchurBallMapH1Matrix38_eq (N M : ℕ) (z : FourierPlane N) :
    actualSchurBallMapH1Matrix38 N M z =
      Matrix.diagonal (planeH1Scale38 N) * actualSchurBallMapPlainMatrix38 N M z *
        Matrix.diagonal (fun r => (planeH1Scale38 N r)⁻¹) := by
  ext r c
  simp [actualSchurBallMapH1Matrix38, Matrix.mul_apply, Matrix.diagonal_apply, div_eq_mul_inv]

theorem actualSchurBallMapH1Matrix38_trace (N M : ℕ) (z : FourierPlane N) :
    Matrix.trace (actualSchurBallMapH1Matrix38 N M z) =
      Matrix.trace (actualSchurBallMapPlainMatrix38 N M z) := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun r _ => ?_
  have := (planeH1Scale38_pos N r).ne'
  simp [actualSchurBallMapH1Matrix38]
  field_simp

theorem actualSchurBallMapH1Matrix38_det (N M : ℕ) (z : FourierPlane N) :
    Matrix.det (1 + actualSchurBallMapH1Matrix38 N M z) =
      Matrix.det (1 + actualSchurBallMapPlainMatrix38 N M z) := by
  have hD : IsUnit (Matrix.diagonal (planeH1Scale38 N)) := by
    rw [Matrix.isUnit_diagonal]
    exact Pi.isUnit_iff.2 fun r => (planeH1Scale38_pos N r).ne'.isUnit
  have hinv : (Matrix.diagonal (planeH1Scale38 N))⁻¹ =
      Matrix.diagonal (fun r => (planeH1Scale38 N r)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => planeH1Scale38 N i * (planeH1Scale38 N i)⁻¹) = fun _ => (1 : ℝ) := by
      funext r; exact mul_inv_cancel₀ (planeH1Scale38_pos N r).ne'
    rw [this, Matrix.diagonal_one]
  rw [← Matrix.det_conj hD (1 + actualSchurBallMapPlainMatrix38 N M z), hinv, mul_add, add_mul,
    mul_one, Matrix.diagonal_mul_diagonal]
  have : (fun i => planeH1Scale38 N i * (planeH1Scale38 N i)⁻¹) = fun _ => (1 : ℝ) := by
    funext r; exact mul_inv_cancel₀ (planeH1Scale38_pos N r).ne'
  rw [this, Matrix.diagonal_one, actualSchurBallMapH1Matrix38_eq]

/-- The determinant of the real derivative `DΨ(z)` equals `det(I + B)` in either real basis. -/
theorem actualSchurBallMap38_det_eq (N M : ℕ) (z : FourierPlane N) :
    LinearMap.det (fderiv ℝ (actualSchurBallMap38 N M) z : FourierPlane N →ₗ[ℝ] FourierPlane N) =
      Matrix.det (1 + actualSchurBallMapH1Matrix38 N M z) := by
  rw [actualSchurBallMapH1Matrix38_det, ← LinearMap.det_toMatrix (planeRealBasis38 N)]
  congr 1
  unfold actualSchurBallMapPlainMatrix38 actualSchurBallMapB38
  rw [← LinearMap.toMatrix_id (planeRealBasis38 N), ← map_add]
  congr 1
  ext w : 1
  simp

theorem planeRealBasis38_coord_eq (N : ℕ) (w : FourierPlane N) (i : Fin (2 * N + 1)) (a : Fin 2) :
    (planeRealBasis38 N).coord (i, a) w = ![(w i).re, (w i).im] a := by
  rw [Module.Basis.coord_apply, planeRealBasis38_repr]

/-- Cauchy-Schwarz for a real functional in the H¹-orthonormal real coordinates: if
`|ℓ w| ≤ ρ ‖w‖_{H¹}` then the squared norm of its coordinate vector is at most `ρ²`. -/
theorem plane_functional_hs_le38 (N : ℕ) (ℓ : FourierPlane N →ₗ[ℝ] ℝ) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (h : ∀ w, |ℓ w| ≤ ρ * ‖planeH1Embedding38 N w‖) :
    ∑ c : PlaneRealIndex38 N, (ℓ (planeRealBasis38 N c) / planeH1Scale38 N c) ^ 2 ≤ ρ ^ 2 := by
  set m : PlaneRealIndex38 N → ℝ := fun c => ℓ (planeRealBasis38 N c) / planeH1Scale38 N c with hm
  set S := ∑ c, m c ^ 2 with hS
  set w : FourierPlane N := (planeRealBasis38 N).equivFun.symm (fun c => m c / planeH1Scale38 N c)
    with hw
  have hrepr : ∀ c, (planeRealBasis38 N).repr w c = m c / planeH1Scale38 N c := by
    intro c
    have := (planeRealBasis38 N).equivFun.apply_symm_apply (fun c => m c / planeH1Scale38 N c)
    rw [← hw, Module.Basis.equivFun_apply] at this
    exact congrFun this c
  have hℓ : ℓ w = S := by
    conv_lhs => rw [← (planeRealBasis38 N).sum_repr w]
    rw [map_sum, hS]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hrepr, smul_eq_mul, hm]
    have := (planeH1Scale38_pos N c).ne'
    simp only
    field_simp
  have hnorm : ‖planeH1Embedding38 N w‖ ^ 2 = S := by
    rw [planeH1Embedding38_norm_sq, hS, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
    have h0 := hrepr (i, 0)
    have h1 := hrepr (i, 1)
    rw [planeRealBasis38_repr] at h0 h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [h0, h1]
    have hd := planeH1Scale38_sq N (i, 0)
    have hd' : planeH1Scale38 N (i, 1) = planeH1Scale38 N (i, 0) := rfl
    rw [hd'] 
    have := (planeH1Scale38_pos N (i, 0)).ne'
    simp only at hd
    rw [← hd]
    field_simp
  have hx := h w
  rw [hℓ] at hx
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hxn : ‖planeH1Embedding38 N w‖ ^ 2 = S := hnorm
  have hx0 := norm_nonneg (planeH1Embedding38 N w)
  rw [abs_of_nonneg hS0] at hx
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

/-! ### Tail sums -/

theorem inv_sq_tail_nat38 (M : ℕ) (hM : 1 ≤ M) (K : ℕ) (hK : M ≤ K) :
    ∑ k ∈ Finset.Ioc M K, 1 / ((k : ℝ) ^ 2) ≤ 1 / (M : ℝ) - 1 / (K : ℝ) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hMK ih =>
    rw [Finset.sum_Ioc_succ_top hMK]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_trans hM hMK
    have hKpos : (0 : ℝ) < K := by linarith
    have : 1 / (((K + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hKpos.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem inv_sq_tail_nat_le38 (M : ℕ) (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ Finset.Ioc M K, 1 / ((k : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
  by_cases hK : M ≤ K
  · have := inv_sq_tail_nat38 M hM K hK
    have : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity

/-- `Σ_{M < |n_i|} 1/n_i² ≤ 2/M` over the plane modes. -/
theorem plane_inv_sq_tail38 (N M : ℕ) (hM : 1 ≤ M) :
    ∑ i : Fin (2 * N + 1),
      (if (modeIndex N i).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N i : ℤ) : ℝ) ^ 2)
      ≤ 2 / (M : ℝ) := by
  have h1 : ∀ i : Fin (2 * N + 1),
      (if (modeIndex N i).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N i : ℤ) : ℝ) ^ 2) =
      (if (modeIndex N i).natAbs ≤ M then (0 : ℝ)
        else 1 / (((modeIndex N i).natAbs : ℕ) : ℝ) ^ 2) := by
    intro i
    split_ifs
    · rfl
    · have h3 : (((modeIndex N i).natAbs : ℕ) : ℝ) = |((modeIndex N i : ℤ) : ℝ)| := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
      rw [h3, sq_abs]
  simp_rw [h1]
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin (2 * N + 1))).filter
      (fun i => ¬ (modeIndex N i).natAbs ≤ M), (modeIndex N i).natAbs ∈ Finset.Ioc M N := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨h1, h2⟩ := modeIndex_bounds N i
    simp only [Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => (modeIndex N i).natAbs ≤ M)]
  have hz : ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * N + 1) => (modeIndex N i).natAbs ≤ M),
      (if (modeIndex N i).natAbs ≤ M then (0 : ℝ) else 1 / (((modeIndex N i).natAbs : ℕ) : ℝ) ^ 2)
      = 0 := Finset.sum_eq_zero fun i hi => by
    rw [Finset.mem_filter] at hi
    simp [hi.2]
  rw [hz, zero_add]
  rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_filter.1 hi).2)]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ Finset.Ioc M N,
      ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ (modeIndex N i).natAbs ≤ M)).filter
          (fun i => (modeIndex N i).natAbs = k), 1 / (((modeIndex N i).natAbs : ℕ) : ℝ) ^ 2
        ≤ 2 * (1 / ((k : ℕ) : ℝ) ^ 2) := by
    intro k _
    have e : ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ (modeIndex N i).natAbs ≤ M)).filter
          (fun i => (modeIndex N i).natAbs = k), 1 / (((modeIndex N i).natAbs : ℕ) : ℝ) ^ 2
        = ∑ i ∈ (Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ (modeIndex N i).natAbs ≤ M)).filter
          (fun i => (modeIndex N i).natAbs = k), 1 / ((k : ℕ) : ℝ) ^ 2 :=
      Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2])
    rw [e]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ (modeIndex N i).natAbs ≤ M)).filter
          (fun i => (modeIndex N i).natAbs = k)).card ≤ 2 := by
      calc _ ≤ ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card := by
            apply Finset.card_le_card_of_injOn (modeIndex N)
            · intro i hi
              rw [Finset.mem_coe, Finset.mem_filter] at hi
              have := hi.2
              simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
              omega
            · intro i _ j _ h
              exact modeIndex_injective N h
        _ ≤ 2 := Finset.card_le_two
    have : ((Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ (modeIndex N i).natAbs ≤ M)).filter
          (fun i => (modeIndex N i).natAbs = k)).card • (1 / ((k : ℕ) : ℝ) ^ 2) ≤ 2 • (1 / ((k : ℕ) : ℝ) ^ 2) :=
      nsmul_le_nsmul_left (by positivity) hcard
    simpa [nsmul_eq_mul] using this
  calc _ ≤ ∑ k ∈ Finset.Ioc M N, 2 * (1 / ((k : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum hfib
    _ = 2 * ∑ k ∈ Finset.Ioc M N, 1 / ((k : ℕ) : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 / (M : ℝ)) := by
        gcongr
        exact inv_sq_tail_nat_le38 M hM N
    _ = 2 / (M : ℝ) := by ring

/-! ### Hilbert-Schmidt bound -/

theorem actualSchurBremConstant38_nonneg : 0 ≤ actualSchurBremConstant38 := by
  unfold actualSchurBremConstant38
  have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hS : 0 ≤ freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant; positivity
  have hMp := physicalH1MultiplierConstant_pos
  positivity

/-- The absolute constant in the Hilbert-Schmidt bound of `B`. -/
def actualSchurBallHSConstant38 : ℝ := 8 * (256 * actualSchurBremConstant38) ^ 2

theorem actualSchurBallMap38_hs_le (N M : ℕ) (hM1 : 1 ≤ M) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) :
    ∑ r : PlaneRealIndex38 N, ∑ c : PlaneRealIndex38 N,
        (actualSchurBallMapH1Matrix38 N M z r c) ^ 2 ≤
      actualSchurBallHSConstant38 * R ^ 6 / (M : ℝ) := by
  have hRpos : 0 < R := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hCb := actualSchurBremConstant38_nonneg
  -- the row functionals
  set ρ : Fin (2 * N + 1) → ℝ := fun j =>
    if (modeIndex N j).natAbs ≤ M then 0
    else actualSchurBremConstant38 * (4 * R) ^ 4 / |((modeIndex N j : ℤ) : ℝ)| ^ 2 / R with hρ
  have hρ0 : ∀ j, 0 ≤ ρ j := by
    intro j; simp only [hρ]; split_ifs <;> positivity
  have hrow : ∀ r : PlaneRealIndex38 N,
      ∑ c, (actualSchurBallMapH1Matrix38 N M z r c) ^ 2 ≤
        (1 + ((modeIndex N r.1 : ℤ) : ℝ) ^ 2) * ρ r.1 ^ 2 := by
    intro r
    have hcs := plane_functional_hs_le38 N
      ((planeRealBasis38 N).coord r ∘ₗ (actualSchurBallMapB38 N M z : FourierPlane N →ₗ[ℝ] FourierPlane N))
      (ρ r.1) (hρ0 _) (by
        intro w
        simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
        rw [Module.Basis.coord_apply]
        obtain ⟨j, b⟩ := r
        rw [planeRealBasis38_repr]
        by_cases hi : (modeIndex N j).natAbs ≤ M
        · have := actualSchurBallMapB38_apply_low N M R hR hM z hz w j hi
          rw [this]; simp only [hρ, hi, if_true, zero_mul]
          fin_cases b <;> simp
        · have hb := actualSchurBallMapB38_row_bound N M R hR hM z hz w j hi
          have hb' : |![(actualSchurBallMapB38 N M z w j).re, (actualSchurBallMapB38 N M z w j).im] b|
              ≤ ‖actualSchurBallMapB38 N M z w j‖ := by
            fin_cases b
            · exact Complex.abs_re_le_norm _
            · exact Complex.abs_im_le_norm _
          simp only [hρ, hi, if_false]
          exact hb'.trans hb)
    have hsum : ∑ c, (actualSchurBallMapH1Matrix38 N M z r c) ^ 2 =
        planeH1Scale38 N r ^ 2 * ∑ c, ((planeRealBasis38 N).coord r
          ((actualSchurBallMapB38 N M z : FourierPlane N →ₗ[ℝ] FourierPlane N)
            (planeRealBasis38 N c)) / planeH1Scale38 N c) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [actualSchurBallMapH1Matrix38, actualSchurBallMapPlainMatrix38,
        LinearMap.toMatrix_apply, Module.Basis.coord_apply]
      rw [← mul_pow]; congr 1; ring
    rw [hsum, planeH1Scale38_sq]
    have h0 : 0 ≤ 1 + ((modeIndex N r.1 : ℤ) : ℝ) ^ 2 := by positivity
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe] at hcs
    exact mul_le_mul_of_nonneg_left hcs h0
  -- sum over rows
  have hrows : ∑ r : PlaneRealIndex38 N, (1 + ((modeIndex N r.1 : ℤ) : ℝ) ^ 2) * ρ r.1 ^ 2 =
      ∑ j : Fin (2 * N + 1), 2 * ((1 + ((modeIndex N j : ℤ) : ℝ) ^ 2) * ρ j ^ 2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_two]; ring
  have hper : ∀ j : Fin (2 * N + 1),
      2 * ((1 + ((modeIndex N j : ℤ) : ℝ) ^ 2) * ρ j ^ 2) ≤
        4 * (256 * actualSchurBremConstant38) ^ 2 * R ^ 6 *
          (if (modeIndex N j).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N j : ℤ) : ℝ) ^ 2) := by
    intro j
    by_cases hi : (modeIndex N j).natAbs ≤ M
    · simp [hρ, hi]
    · simp only [hρ, hi, if_false]
      have hn := natAbs_gt_abs38 M _ hi
      have hn1 : (1 : ℝ) ≤ |((modeIndex N j : ℤ) : ℝ)| := by
        have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
        linarith
      set t : ℝ := ((modeIndex N j : ℤ) : ℝ) ^ 2 with ht
      have ht1 : 1 ≤ t := by
        rw [ht, ← sq_abs]; nlinarith
      have hρe : actualSchurBremConstant38 * (4 * R) ^ 4 / |((modeIndex N j : ℤ) : ℝ)| ^ 2 / R =
          256 * actualSchurBremConstant38 * R ^ 3 / t := by
        rw [sq_abs, ← ht]
        field_simp
        ring
      rw [hρe]
      have htpos : 0 < t := by linarith
      have hA : 0 ≤ (256 * actualSchurBremConstant38) ^ 2 * R ^ 6 := by positivity
      have e1 : (256 * actualSchurBremConstant38 * R ^ 3 / t) ^ 2 =
          ((256 * actualSchurBremConstant38) ^ 2 * R ^ 6) / t ^ 2 := by
        rw [div_pow]; ring
      have e2 : 2 * ((1 + t) * (((256 * actualSchurBremConstant38) ^ 2 * R ^ 6) / t ^ 2)) =
          (2 * (1 + t) * ((256 * actualSchurBremConstant38) ^ 2 * R ^ 6)) / t ^ 2 := by ring
      have e3 : 4 * (256 * actualSchurBremConstant38) ^ 2 * R ^ 6 * (1 / t) =
          (4 * t * ((256 * actualSchurBremConstant38) ^ 2 * R ^ 6)) / t ^ 2 := by
        field_simp
      rw [e1, e2, e3]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hA (sub_nonneg.2 ht1)]
  have htail := plane_inv_sq_tail38 N M hM1
  calc ∑ r, ∑ c, (actualSchurBallMapH1Matrix38 N M z r c) ^ 2
      ≤ ∑ r : PlaneRealIndex38 N, (1 + ((modeIndex N r.1 : ℤ) : ℝ) ^ 2) * ρ r.1 ^ 2 :=
        Finset.sum_le_sum fun r _ => hrow r
    _ = _ := hrows
    _ ≤ ∑ j : Fin (2 * N + 1), 4 * (256 * actualSchurBremConstant38) ^ 2 * R ^ 6 *
          (if (modeIndex N j).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N j : ℤ) : ℝ) ^ 2) :=
        Finset.sum_le_sum fun j _ => hper j
    _ = 4 * (256 * actualSchurBremConstant38) ^ 2 * R ^ 6 *
          ∑ j : Fin (2 * N + 1),
            (if (modeIndex N j).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N j : ℤ) : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * (256 * actualSchurBremConstant38) ^ 2 * R ^ 6 * (2 / (M : ℝ)) := by
        gcongr
    _ = _ := by unfold actualSchurBallHSConstant38; ring

/-! ### Trace -/

theorem planeRealBasis38_apply_zero (N : ℕ) (i : Fin (2 * N + 1)) :
    planeRealBasis38 N (i, 0) = Pi.single i (1 : ℂ) := by
  unfold planeRealBasis38
  simp [Module.Basis.reindex_apply, Pi.basis_apply]

theorem planeRealBasis38_apply_one (N : ℕ) (i : Fin (2 * N + 1)) :
    planeRealBasis38 N (i, 1) = Pi.single i Complex.I := by
  unfold planeRealBasis38
  simp [Module.Basis.reindex_apply, Pi.basis_apply]

theorem planeH1Embedding38_single_I (N : ℕ) (i : Fin (2 * N + 1)) :
    planeH1Embedding38 N (Pi.single i Complex.I) =
      Complex.I • actualH1ModeVector38 (modeIndex N i) := by
  have : (Pi.single i Complex.I : FourierPlane N) = Complex.I • Pi.single i (1 : ℂ) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [this, map_smul, planeH1Embedding38_single]

/-- The Wirtinger derivative `∂q_n/∂(u₁)_n - 1` of the radius-`4R` auxiliary coordinate at the
real-type point `(u, ū)`, `u = embed z`. -/
def actualSchurBallWirtinger38 (R : ℝ) (n : ℤ) (u : H1) : ℂ :=
  fderiv ℂ (actualSchurQn38 (4 * R) n) (u, actualH1Conj38 u) (actualH1ModeVector38 n, 0) - 1

/-- F:eq:traceJac: `tr_ℝ B = 2 Re Σ_{M<|n|≤N} (∂_{u_n} q_n - 1)`, with the trace taken in the
H¹-orthonormal real basis (equivalently, in the plain real basis). -/
theorem actualSchurBallMap38_trace_eq (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) :
    Matrix.trace (actualSchurBallMapH1Matrix38 N M z) =
      2 * (∑ i : Fin (2 * N + 1),
        if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else actualSchurBallWirtinger38 R (modeIndex N i) (planeH1Embedding38 N z)).re := by
  have h4R : 1 ≤ 4 * R := by linarith
  rw [actualSchurBallMapH1Matrix38_trace]
  unfold Matrix.trace
  rw [Fintype.sum_prod_type, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp only [Matrix.diag_apply, actualSchurBallMapPlainMatrix38, LinearMap.toMatrix_apply,
    planeRealBasis38_repr, planeRealBasis38_apply_zero, planeRealBasis38_apply_one,
    ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hi : (modeIndex N i).natAbs ≤ M
  · rw [actualSchurBallMapB38_apply_low N M R hR hM z hz _ i hi,
      actualSchurBallMapB38_apply_low N M R hR hM z hz _ i hi]
    simp [hi]
  · rw [actualSchurBallMapB38_apply_high N M R hR hM z hz _ i hi,
      actualSchurBallMapB38_apply_high N M R hR hM z hz _ i hi]
    have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤
        |((modeIndex N i : ℤ) : ℝ)| := by
      have := natAbs_gt_abs38 M _ hi
      linarith
    have hw := actualSchurQnRealRemainder38_wirtinger (4 * R) h4R (modeIndex N i) hthr
      (planeH1Embedding38 N z) (by linarith) (actualH1ModeVector38 (modeIndex N i))
    rw [planeH1Embedding38_single, planeH1Embedding38_single_I]
    have h1 : (actualH1ModeVector38 (modeIndex N i) : ℤ → ℂ) (modeIndex N i) = 1 := by
      rw [actualH1ModeVector38_apply]; simp
    simp only [hi, if_false, actualSchurBallWirtinger38]
    rw [← h1, ← hw]
    simp [Complex.mul_re]

/-- Constant of the trace bound. -/
def actualSchurBallTraceConstant38 : ℝ :=
  2048 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
    freeResolventSchurUniformConstant ^ 2)

theorem actualSchurBallWirtinger38_norm_le (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)|)
    (u : H1) (hu : ‖u‖ ≤ R) :
    ‖actualSchurBallWirtinger38 R n u‖ ≤
      2 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2) := by
  have h22 : 2 * (2 * R) = 4 * R := by ring
  have h := actualSchurQnRealType_ownMode_wirtinger38 (2 * R) (by linarith) n
    (by rw [h22]; exact hthr) u (by linarith)
  rw [h22] at h
  have hw := actualSchurQnRealRemainder38_wirtinger (4 * R) (by linarith) n hthr u
    (by linarith) (actualH1ModeVector38 n)
  have h1 : (actualH1ModeVector38 n : ℤ → ℂ) n = 1 := by
    rw [actualH1ModeVector38_apply]; simp
  rw [hw, h1] at h
  unfold actualSchurBallWirtinger38
  unfold actualSchurOwnModeScale38 at h
  exact h

theorem actualSchurBallMap38_trace_le (N M : ℕ) (hM1 : 1 ≤ M) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : ‖planeH1Embedding38 N z‖ < R) :
    |Matrix.trace (actualSchurBallMapH1Matrix38 N M z)| ≤
      actualSchurBallTraceConstant38 * R ^ 4 / (M : ℝ) := by
  rw [actualSchurBallMap38_trace_eq N M R hR hM z hz]
  set c := freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ i : Fin (2 * N + 1),
      ‖(if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else actualSchurBallWirtinger38 R (modeIndex N i) (planeH1Embedding38 N z))‖ ≤
      2 * (256 * c * R ^ 4) *
        (if (modeIndex N i).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N i : ℤ) : ℝ) ^ 2) := by
    intro i
    by_cases hi : (modeIndex N i).natAbs ≤ M
    · simp [hi]
    · simp only [hi, if_false]
      have hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤
          |((modeIndex N i : ℤ) : ℝ)| := by
        have := natAbs_gt_abs38 M _ hi
        linarith
      refine (actualSchurBallWirtinger38_norm_le R hR _ hthr _ hz.le).trans ?_
      rw [sq_abs]
      have : 2 * (c * (4 * R) ^ 4 / ((modeIndex N i : ℤ) : ℝ) ^ 2) =
          2 * (256 * c * R ^ 4) * (1 / ((modeIndex N i : ℤ) : ℝ) ^ 2) := by ring
      rw [this]
  have hsumC : ‖∑ i : Fin (2 * N + 1),
      (if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else actualSchurBallWirtinger38 R (modeIndex N i) (planeH1Embedding38 N z))‖ ≤
      2 * (256 * c * R ^ 4) * (2 / (M : ℝ)) :=
    calc _ ≤ ∑ i : Fin (2 * N + 1), ‖(if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else actualSchurBallWirtinger38 R (modeIndex N i) (planeH1Embedding38 N z))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin (2 * N + 1), 2 * (256 * c * R ^ 4) *
        (if (modeIndex N i).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N i : ℤ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * (256 * c * R ^ 4) * ∑ i : Fin (2 * N + 1),
        (if (modeIndex N i).natAbs ≤ M then (0 : ℝ) else 1 / ((modeIndex N i : ℤ) : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          exact plane_inv_sq_tail38 N M hM1
  have hre := Complex.abs_re_le_norm (∑ i : Fin (2 * N + 1),
      (if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else actualSchurBallWirtinger38 R (modeIndex N i) (planeH1Embedding38 N z)))
  rw [abs_mul, abs_two]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  calc 2 * |(∑ i : Fin (2 * N + 1),
      (if (modeIndex N i).natAbs ≤ M then (0 : ℂ)
        else actualSchurBallWirtinger38 R (modeIndex N i) (planeH1Embedding38 N z))).re|
      ≤ 2 * (2 * (256 * c * R ^ 4) * (2 / (M : ℝ))) := by gcongr; exact hre.trans hsumC
    _ = _ := by unfold actualSchurBallTraceConstant38; rw [← hc]; ring

end NlsGge.Schur
