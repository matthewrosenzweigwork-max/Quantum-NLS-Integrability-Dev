import NlsGge.Atomic.LIB.LIB002
import NlsGge.Schur.FreeResolventRankTwoProjectionPrerequisites
import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# KST free spectral projection on the full doubled pair space

The source space is the full pair `L²(AddCircle 2) ⊕ L²(AddCircle 2)` with
probability Haar, i.e. the source normalization `(1/2) ∫₀²`.  The period-two
characters are `e_m(x) = exp(m π i x)`.  KST's projection at `n` is onto
`(e_{-n}, 0)` and `(0, e_n)`: in the project's reflected parity chart this is
the resonant projection at label `-n`.

The literal weak derivative graph below uses the all-smooth-periodic-test
definition from LIB002 at period two.  KST's `i diag(1,-1) ∂ₓ` is therefore
the negative of the existing project's `(-i ∂ₓ,+i ∂ₓ)` source action.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open MeasureTheory
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Atomic.KST003

open NlsGge.Schur
open NlsGge.Atomic.LIB002

/-- The source's full doubled pair `L²` space; no parity restriction is imposed. -/
abbrev KSTPairL2 : Type := PiLp 2 (fun _ : Bool => SpectralScalarL2)

/-- The upper KST resonant vector is the source character `e_{-n}`. -/
def kstPnUpper (n : ℤ) : KSTPairL2 :=
  PiLp.single 2 true (spectralBasis (-n))

/-- The lower KST resonant vector is the source character `e_n`. -/
def kstPnLower (n : ℤ) : KSTPairL2 :=
  PiLp.single 2 false (spectralBasis n)

/-- The orthonormal pair spanning the full source projection `P_n`. -/
def kstPnFrame (n : ℤ) (b : Bool) : KSTPairL2 :=
  if b then kstPnUpper n else kstPnLower n

/-- The two actual source vectors are orthonormal in the full doubled pair space. -/
theorem kstPnFrame_orthonormal (n : ℤ) : Orthonormal ℂ (kstPnFrame n) := by
  rw [orthonormal_iff_ite]
  intro b c
  cases b <;> cases c <;>
    simp [kstPnFrame, kstPnUpper, kstPnLower, PiLp.inner_apply,
      PiLp.single_apply, Fintype.sum_bool, spectralBasis_norm]

/-- The full-space source projection, as the sum of the two genuine rank-one maps. -/
def spectralPn (n : ℤ) : KSTPairL2 →L[ℂ] KSTPairL2 :=
  InnerProductSpace.rankOne ℂ (kstPnUpper n) (kstPnUpper n) +
    InnerProductSpace.rankOne ℂ (kstPnLower n) (kstPnLower n)

/-- Its coefficient formula fixes the conjugate-linear first-slot convention. -/
theorem spectralPn_apply (n : ℤ) (x : KSTPairL2) :
    spectralPn n x =
      inner ℂ (kstPnUpper n) x • kstPnUpper n +
        inner ℂ (kstPnLower n) x • kstPnLower n := by
  simp [spectralPn, InnerProductSpace.rankOne_apply]

/-- The true orthogonal complement is `Q_n = Id - P_n` on the same full source space. -/
def spectralQn (n : ℤ) : KSTPairL2 →L[ℂ] KSTPairL2 :=
  ContinuousLinearMap.id ℂ KSTPairL2 - spectralPn n

theorem spectralPn_upper (n : ℤ) : spectralPn n (kstPnUpper n) = kstPnUpper n := by
  rw [spectralPn_apply]
  have h := (orthonormal_iff_ite.mp (kstPnFrame_orthonormal n))
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
    simpa [kstPnFrame] using h true true
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by
    simpa [kstPnFrame] using h false true
  rw [huu, hlu]
  simp

theorem spectralPn_lower (n : ℤ) : spectralPn n (kstPnLower n) = kstPnLower n := by
  rw [spectralPn_apply]
  have h := (orthonormal_iff_ite.mp (kstPnFrame_orthonormal n))
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by
    simpa [kstPnFrame] using h true false
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
    simpa [kstPnFrame] using h false false
  rw [hul, hll]
  simp

/-- The range is exactly the source span of `(e_{-n},0)` and `(0,e_n)`. -/
theorem spectralPn_range (n : ℤ) :
    LinearMap.range (spectralPn n).toLinearMap =
      Submodule.span ℂ (Set.range (kstPnFrame n)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change spectralPn n x ∈ Submodule.span ℂ (Set.range (kstPnFrame n))
    rw [spectralPn_apply]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self true)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self false)))
  · apply Submodule.span_le.2
    rintro v ⟨b, rfl⟩
    cases b
    · exact ⟨kstPnLower n, spectralPn_lower n⟩
    · exact ⟨kstPnUpper n, spectralPn_upper n⟩

/-- `P_n` is idempotent on the full doubled source space. -/
theorem spectralPn_idempotent (n : ℤ) :
    (spectralPn n).comp (spectralPn n) = spectralPn n := by
  apply ContinuousLinearMap.ext
  intro x
  calc
    spectralPn n (spectralPn n x) = spectralPn n
        (inner ℂ (kstPnUpper n) x • kstPnUpper n +
          inner ℂ (kstPnLower n) x • kstPnLower n) := by
      exact congrArg (spectralPn n) (spectralPn_apply n x)
    _ = inner ℂ (kstPnUpper n) x • kstPnUpper n +
          inner ℂ (kstPnLower n) x • kstPnLower n := by
      rw [spectralPn_apply]
      have h := (orthonormal_iff_ite.mp (kstPnFrame_orthonormal n))
      have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
        simpa [kstPnFrame] using h true true
      have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by
        simpa [kstPnFrame] using h true false
      have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by
        simpa [kstPnFrame] using h false true
      have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
        simpa [kstPnFrame] using h false false
      simp only [inner_add_right, inner_smul_right]
      rw [huu, hul, hlu, hll]
      simp
    _ = spectralPn n x := (spectralPn_apply n x).symm

/-- The residual after `P_n` is orthogonal to both actual spanning characters. -/
theorem spectralPn_residual_orthogonal (n : ℤ) (x : KSTPairL2) (b : Bool) :
    inner ℂ (kstPnFrame n b) (x - spectralPn n x) = 0 := by
  rw [spectralPn_apply]
  have h := (orthonormal_iff_ite.mp (kstPnFrame_orthonormal n))
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
    simpa [kstPnFrame] using h true true
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by
    simpa [kstPnFrame] using h true false
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by
    simpa [kstPnFrame] using h false true
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
    simpa [kstPnFrame] using h false false
  cases b
  · change inner ℂ (kstPnLower n) (x -
      (inner ℂ (kstPnUpper n) x • kstPnUpper n +
       inner ℂ (kstPnLower n) x • kstPnLower n)) = 0
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    rw [hlu, hll]
    ring
  · change inner ℂ (kstPnUpper n) (x -
      (inner ℂ (kstPnUpper n) x • kstPnUpper n +
       inner ℂ (kstPnLower n) x • kstPnLower n)) = 0
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    rw [huu, hul]
    ring

private theorem piLp_single_smul (b : Bool) (c : ℂ) (v : SpectralScalarL2) :
    c • (PiLp.single 2 b v : KSTPairL2) =
      (PiLp.single 2 b (c • v) : KSTPairL2) := by
  apply PiLp.ext
  intro i
  by_cases h : i = b
  · subst i
    simp
  · simp [h]

/-- Literal componentwise period-two weak graph of KST's free Dirac operator. -/
def HasKSTFreeDiracGraph (x y : KSTPairL2) : Prop :=
  ∃ du dl : SpectralScalarL2,
    HasWeakDerivativeL2 (2 : ℝ) 1 (x true) du ∧
    HasWeakDerivativeL2 (2 : ℝ) 1 (x false) dl ∧
    y = PiLp.single 2 true (Complex.I • du) +
      PiLp.single 2 false ((-Complex.I) • dl)

/-- A weak derivative graph is preserved by a common complex scalar. -/
private theorem weakDerivative_smul {u v : SpectralScalarL2}
    (h : HasWeakDerivativeL2 (2 : ℝ) 1 u v) (c : ℂ) :
    HasWeakDerivativeL2 (2 : ℝ) 1 (c • u) (c • v) := by
  intro φ
  calc
    inner ℂ (SmoothPeriodicTest.toL2 (SmoothPeriodicTest.iterated φ 1)) (c • u) =
        c * inner ℂ (SmoothPeriodicTest.toL2 (SmoothPeriodicTest.iterated φ 1)) u :=
      inner_smul_right _ _ _
    _ = c * ((-1 : ℂ) ^ 1 * inner ℂ (SmoothPeriodicTest.toL2 φ) v) :=
      congrArg (fun z : ℂ => c * z) (h φ)
    _ = (-1 : ℂ) ^ 1 * inner ℂ (SmoothPeriodicTest.toL2 φ) (c • v) := by
      rw [inner_smul_right]
      ring

/-- Actual period-two character derivative, proved against every literal weak test. -/
private theorem spectralBasis_weakDerivative (m : ℤ) :
    HasWeakDerivativeL2 (2 : ℝ) 1 (spectralBasis m)
      (LIB002.fourierMultiplier (2 : ℝ) m • spectralBasis m) := by
  apply (weakDerivative_fourierCoeff_iff (T := (2 : ℝ)) (m := 1)).2
  intro k
  have hcoeff (j : ℤ) :
      fourierCoeff (spectralBasis m) j = if j = m then 1 else 0 := by
    have ho := (orthonormal_iff_ite.mp
      (orthonormal_fourier (T := (2 : ℝ)))) j m
    calc
      fourierCoeff (spectralBasis m) j =
          inner ℂ (fourierLp 2 j) (spectralBasis m) :=
        (inner_fourierLp_eq_fourierCoeff (T := (2 : ℝ)) (f := spectralBasis m) j).symm
      _ = if j = m then 1 else 0 := by simpa [spectralBasis] using ho
  have hsmul (j : ℤ) :
      fourierCoeff (LIB002.fourierMultiplier (2 : ℝ) m • spectralBasis m) j =
        LIB002.fourierMultiplier (2 : ℝ) m * fourierCoeff (spectralBasis m) j := by
    calc
      fourierCoeff (LIB002.fourierMultiplier (2 : ℝ) m • spectralBasis m) j =
          inner ℂ (fourierLp 2 j)
            (LIB002.fourierMultiplier (2 : ℝ) m • spectralBasis m) :=
        (inner_fourierLp_eq_fourierCoeff (T := (2 : ℝ))
          (f := LIB002.fourierMultiplier (2 : ℝ) m • spectralBasis m) j).symm
      _ = LIB002.fourierMultiplier (2 : ℝ) m *
          inner ℂ (fourierLp 2 j) (spectralBasis m) := inner_smul_right _ _ _
      _ = LIB002.fourierMultiplier (2 : ℝ) m *
          fourierCoeff (spectralBasis m) j := by rw [inner_fourierLp_eq_fourierCoeff]
  by_cases hk : k = m
  · subst k
    rw [hsmul, hcoeff]
    simp [LIB002.fourierMultiplier]
  · rw [hsmul]
    simp [hcoeff, hk]

/-- The weak graph for KST's operator is the negative of the project's
`(-i∂,+i∂)` action, preserving the source matrix convention. -/
theorem kstFreeDirac_on_Pn (n : ℤ) (x : KSTPairL2) :
    HasKSTFreeDiracGraph (spectralPn n x) ((n * Real.pi : ℝ) • spectralPn n x) := by
  let a := inner ℂ (kstPnUpper n) x
  let b := inner ℂ (kstPnLower n) x
  let fneg := LIB002.fourierMultiplier (2 : ℝ) (-n)
  let fpos := LIB002.fourierMultiplier (2 : ℝ) n
  have hpu : (spectralPn n x) true = a • spectralBasis (-n) := by
    have h := congrArg (fun z : KSTPairL2 => z true) (spectralPn_apply n x)
    simpa [a, kstPnUpper, kstPnLower] using h
  have hpl : (spectralPn n x) false = b • spectralBasis n := by
    have h := congrArg (fun z : KSTPairL2 => z false) (spectralPn_apply n x)
    simpa [b, kstPnUpper, kstPnLower] using h
  have hneg : Complex.I * fneg = ((n * Real.pi : ℝ) : ℂ) := by
    simp [fneg, LIB002.fourierMultiplier, Complex.I_sq] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring
  have hpos : -Complex.I * fpos = ((n * Real.pi : ℝ) : ℂ) := by
    simp [fpos, LIB002.fourierMultiplier, Complex.I_sq] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring
  have hnegCoeff : ((n * Real.pi : ℝ) : ℂ) * a =
      Complex.I * a * fneg := by
    calc
      _ = (Complex.I * fneg) * a := by rw [hneg]
      _ = Complex.I * a * fneg := by ring
  have hposCoeff : ((n * Real.pi : ℝ) : ℂ) * b =
      -Complex.I * b * fpos := by
    calc
      _ = (-Complex.I * fpos) * b := by rw [hpos]
      _ = -Complex.I * b * fpos := by ring
  have hnegVec : ((n * Real.pi : ℝ) : ℂ) • (a • spectralBasis (-n)) =
      Complex.I • (a • (fneg • spectralBasis (-n))) := by
    calc
      _ = (((n * Real.pi : ℝ) : ℂ) * a) • spectralBasis (-n) := by
        rw [smul_smul]
      _ = (Complex.I * a * fneg) • spectralBasis (-n) := by rw [hnegCoeff]
      _ = Complex.I • (a • (fneg • spectralBasis (-n))) := by
        rw [smul_smul, smul_smul]
  have hposVec : ((n * Real.pi : ℝ) : ℂ) • (b • spectralBasis n) =
      -Complex.I • (b • (fpos • spectralBasis n)) := by
    calc
      _ = (((n * Real.pi : ℝ) : ℂ) * b) • spectralBasis n := by
        rw [smul_smul]
      _ = (-Complex.I * b * fpos) • spectralBasis n := by rw [hposCoeff]
      _ = -Complex.I • (b • (fpos • spectralBasis n)) := by
        rw [smul_smul, smul_smul]
  refine ⟨a • (fneg • spectralBasis (-n)),
    b • (fpos • spectralBasis n), ?_, ?_, ?_⟩
  · rw [hpu]
    exact weakDerivative_smul (spectralBasis_weakDerivative (-n)) a
  · rw [hpl]
    exact weakDerivative_smul (spectralBasis_weakDerivative n) b
  · rw [spectralPn_apply]
    change ((n * Real.pi : ℝ) •
        (a • (PiLp.single 2 true (spectralBasis (-n)) : KSTPairL2) +
          b • (PiLp.single 2 false (spectralBasis n) : KSTPairL2))) = _
    calc
      _ = ((n * Real.pi : ℝ) •
          (a • (PiLp.single 2 true (spectralBasis (-n)) : KSTPairL2))) +
          ((n * Real.pi : ℝ) •
            (b • (PiLp.single 2 false (spectralBasis n) : KSTPairL2))) := by
        rw [smul_add]
      _ = PiLp.single 2 true
            (((n * Real.pi : ℝ) : ℂ) • (a • spectralBasis (-n))) +
          PiLp.single 2 false
            (((n * Real.pi : ℝ) : ℂ) • (b • spectralBasis n)) := by
        simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := KSTPairL2)]
        simp only [smul_smul, piLp_single_smul]
        rfl
      _ = PiLp.single 2 true
            (Complex.I • (a • (fneg • spectralBasis (-n)))) +
          PiLp.single 2 false
            (-Complex.I • (b • (fpos • spectralBasis n))) := by
        rw [hnegVec, hposVec]

/-- Componentwise inclusion of the actual parity carrier into the full source
doubled-circle pair carrier. -/
def parityPairFullLinear (n : ℤ) : ParityPair n →ₗ[ℂ] KSTPairL2 where
  toFun x := WithLp.toLp 2 (fun b => (x b).val)
  map_add' x y := by
    apply PiLp.ext
    intro b
    simp
  map_smul' c x := by
    apply PiLp.ext
    intro b
    simp

theorem parityPairFullLinear_inner (n : ℤ) (x y : ParityPair n) :
    inner ℂ (parityPairFullLinear n x) (parityPairFullLinear n y) = inner ℂ x y := by
  simp [parityPairFullLinear, PiLp.inner_apply, Fintype.sum_bool, Submodule.coe_inner]

/-- Inner-product-preserving inclusion from the parity carrier into the full source. -/
def parityPairFullEmbedding (n : ℤ) : ParityPair n →ₗ[ℂ] KSTPairL2 :=
  parityPairFullLinear n

theorem parityPairFullEmbedding_vector (n : ℤ) (i : Bool × Sector n) :
    parityPairFullEmbedding n (parityPairVector n i) =
      PiLp.single 2 i.1 (spectralBasis (mixedIndex n i).val) := by
  apply PiLp.ext
  intro b
  by_cases hb : b = i.1
  · subst b
    simp [parityPairFullEmbedding, parityPairFullLinear, parityPairVector,
      scalarParityVector, PiLp.single_apply]
  · simp [parityPairFullEmbedding, parityPairFullLinear, parityPairVector,
      PiLp.single_apply, hb]

/-- In the source's true/upper convention, the parity chart uses label -n. -/
theorem parityPairFullEmbedding_upper (n : ℤ) :
    parityPairFullEmbedding (-n)
      (parityPairVector (-n) (true, resonantIndex (-n))) = kstPnUpper n := by
  rw [parityPairFullEmbedding_vector]
  simp [kstPnUpper, mixedIndex, resonantIndex]

/-- In the source's true/upper convention, the parity chart uses label -n. -/
theorem parityPairFullEmbedding_lower (n : ℤ) :
    parityPairFullEmbedding (-n)
      (parityPairVector (-n) (false, resonantIndex (-n))) = kstPnLower n := by
  rw [parityPairFullEmbedding_vector]
  simp [kstPnLower, mixedIndex, negateIndex, resonantIndex]

/-- On the embedded ParityPair (-n), the full source projection restricts
exactly to the project's proved resonant projection at the reflected label. -/
theorem spectralPn_parity_restriction (n : ℤ) (x : ParityPair (-n)) :
    spectralPn n (parityPairFullEmbedding (-n) x) =
      parityPairFullEmbedding (-n) (resonantParityPair (-n) x) := by
  rw [spectralPn_apply, ← parityPairFullEmbedding_upper, ← parityPairFullEmbedding_lower]
  have hu : inner ℂ
      (parityPairFullEmbedding (-n)
        (parityPairVector (-n) (true, resonantIndex (-n))))
      (parityPairFullEmbedding (-n) x) =
      inner ℂ (parityPairVector (-n) (true, resonantIndex (-n))) x :=
    parityPairFullLinear_inner (-n) _ _
  have hl : inner ℂ
      (parityPairFullEmbedding (-n)
        (parityPairVector (-n) (false, resonantIndex (-n))))
      (parityPairFullEmbedding (-n) x) =
      inner ℂ (parityPairVector (-n) (false, resonantIndex (-n))) x :=
    parityPairFullLinear_inner (-n) _ _
  rw [hu, hl]
  rw [← (parityPairFullEmbedding (-n)).map_smul,
    ← (parityPairFullEmbedding (-n)).map_smul,
    ← (parityPairFullEmbedding (-n)).map_add]
  rw [resonantParityPair_two_term_prerequisite]

/-- The full complement Q_n = Id - P_n restricts to the corresponding
complement on the actual parity chart. -/
theorem spectralQn_parity_restriction (n : ℤ) (x : ParityPair (-n)) :
    spectralQn n (parityPairFullEmbedding (-n) x) =
      parityPairFullEmbedding (-n) (x - resonantParityPair (-n) x) := by
  simp only [spectralQn, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, spectralPn_parity_restriction]
  exact ((parityPairFullEmbedding (-n)).map_sub x _).symm

/-- Full doubled-pair norm normalization: probability Haar is one half
ordinary volume on the length-two source interval, componentwise. -/
theorem kstPair_norm_sq_doubled_interval (x : KSTPairL2) :
    ‖x‖ ^ 2 = (1 / 2 : ℝ) *
      ((∫ t in Set.Ioc (0 : ℝ) 2, ‖x true (t : SpectralCircle)‖ ^ 2) +
       (∫ t in Set.Ioc (0 : ℝ) 2, ‖x false (t : SpectralCircle)‖ ^ 2)) := by
  calc
    ‖x‖ ^ 2 = ‖x true‖ ^ 2 + ‖x false‖ ^ 2 := by
      simpa only [Fintype.sum_bool] using
        (PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2) x)
    _ = (1 / 2 : ℝ) *
        ((∫ t in Set.Ioc (0 : ℝ) 2, ‖x true (t : SpectralCircle)‖ ^ 2) +
         (∫ t in Set.Ioc (0 : ℝ) 2, ‖x false (t : SpectralCircle)‖ ^ 2)) := by
      rw [spectral_norm_sq_doubled_interval, spectral_norm_sq_doubled_interval]
      ring

end NlsGge.Atomic.KST003
