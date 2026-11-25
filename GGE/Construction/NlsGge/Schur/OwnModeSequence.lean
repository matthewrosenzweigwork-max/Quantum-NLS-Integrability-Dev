import NlsGge.Schur.ResonantIndices
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Logic.Equiv.Bool

/-!
# Concrete own-mode cancellation on sequence coordinates

These operators act on actual two-component parity-sector sequences. Their
cross zeros are conclusions, not hypotheses. This is a coordinate model only:
the first layer uses raw sequences; the second supplies genuine square-summable
Hilbert coordinates and bounded operators. Physical Fourier identification is open.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace NlsGge.Schur

/-- Upper and lower coefficient sequences, indexed by the source parity sector. -/
abbrev SectorSequence (n : ℤ) := (Sector n → ℂ) × (Sector n → ℂ)

/-- Upper component unit vector at the actual spectral integer `m`. -/
def upperBasis (n : ℤ) (m : Sector n) : SectorSequence n :=
  (fun i => if i = m then 1 else 0, 0)

/-- Lower component unit vector at the actual spectral integer `m`. -/
def lowerBasis (n : ℤ) (m : Sector n) : SectorSequence n :=
  (0, fun i => if i = m then 1 else 0)

/-- Coordinate action of variation in `(u₁)_n`, with `u₂` held fixed. -/
def ownModeSequence (n : ℤ) : SectorSequence n →ₗ[ℂ] SectorSequence n where
  toFun x := (fun m => x.2 (reflectIndex n m), 0)
  map_add' x y := by ext m <;> simp
  map_smul' c x := by ext m <;> simp

/-- The two resonant coordinates and zero everywhere else. -/
def resonantSequence (n : ℤ) : SectorSequence n →ₗ[ℂ] SectorSequence n where
  toFun x := (fun m => if m = resonantIndex n then x.1 m else 0,
    fun m => if m = resonantIndex n then x.2 m else 0)
  map_add' x y := by
    ext m <;> by_cases hm : m = resonantIndex n <;> simp [hm]
  map_smul' c x := by
    ext m <;> by_cases hm : m = resonantIndex n <;> simp [hm]

/-- The complement is exactly `1-P`, with the operator subtraction taken pointwise. -/
def complementarySequence (n : ℤ) : SectorSequence n →ₗ[ℂ] SectorSequence n :=
  LinearMap.id - resonantSequence n

/-- Every upper basis vector is annihilated. -/
theorem ownModeSequence_upperBasis (n : ℤ) (m : Sector n) :
    ownModeSequence n (upperBasis n m) = 0 := by
  ext i <;> simp [ownModeSequence, upperBasis]

/-- A lower basis vector is sent to upper index `2*n-m`. -/
theorem ownModeSequence_lowerBasis (n : ℤ) (m : Sector n) :
    ownModeSequence n (lowerBasis n m) = upperBasis n (reflectIndex n m) := by
  have hiff (i : Sector n) : reflectIndex n i = m ↔ i = reflectIndex n m := by
    constructor
    · intro h
      have hh := congrArg (reflectIndex n) h
      simpa using hh
    · rintro rfl
      simp
  ext i <;> simp [ownModeSequence, lowerBasis, upperBasis, hiff]

/-- The resonant lower vector goes to the resonant upper vector. -/
theorem ownModeSequence_lower_resonant (n : ℤ) :
    ownModeSequence n (lowerBasis n (resonantIndex n)) =
      upperBasis n (resonantIndex n) := by
  simpa using ownModeSequence_lowerBasis n (resonantIndex n)

/-- Projection onto the two resonant coordinates is idempotent. -/
theorem resonantSequence_idempotent (n : ℤ) :
    (resonantSequence n).comp (resonantSequence n) = resonantSequence n := by
  ext x m <;> by_cases hm : m = resonantIndex n <;> simp [resonantSequence, hm]

/-- The own-mode variation preserves the resonant coordinates. -/
theorem ownModeSequence_commutes_resonant (n : ℤ) :
    (ownModeSequence n).comp (resonantSequence n) =
      (resonantSequence n).comp (ownModeSequence n) := by
  ext x m <;> simp [ownModeSequence, resonantSequence]

/-- Actual `Q H_n P = 0`, in the source composition order. -/
theorem complementary_ownMode_resonant_zero (n : ℤ) :
    (complementarySequence n).comp
      ((ownModeSequence n).comp (resonantSequence n)) = 0 := by
  ext x m <;> by_cases hm : m = resonantIndex n <;>
    simp [complementarySequence, ownModeSequence, resonantSequence, hm]

/-- Actual `P H_n Q = 0`, in the source composition order. -/
theorem resonant_ownMode_complementary_zero (n : ℤ) :
    (resonantSequence n).comp
      ((ownModeSequence n).comp (complementarySequence n)) = 0 := by
  ext x m <;> by_cases hm : m = resonantIndex n <;>
    simp [complementarySequence, ownModeSequence, resonantSequence, hm]


/-- Square-summable complex sequences with their genuine Hilbert norm. -/
abbrev SquareSequence (I : Type) : Type := lp (fun _ : I => ℂ) 2

/-- Reindexing preserves membership, by the actual summability theorem. -/
def reindexSquare {I : Type} (e : I ≃ I) (x : SquareSequence I) : SquareSequence I :=
  ⟨fun i => x (e i), memℓp_gen ((e.summable_iff).mpr ((lp.memℓp x).summable (by norm_num)))⟩

theorem reindexSquare_norm {I : Type} (e : I ≃ I) (x : SquareSequence I) :
    ‖reindexSquare e x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact e.tsum_eq (fun i => ‖x i‖ ^ (2 : ℝ≥0∞).toReal)

/-- A coordinate mask preserves square-summability. -/
def maskSquare {I : Type} (s : I → Prop) [DecidablePred s]
    (x : SquareSequence I) : SquareSequence I :=
  ⟨fun i => if s i then x i else 0, (lp.memℓp x).mono' (by
    intro i
    split_ifs <;> simp)⟩

theorem maskSquare_norm_le {I : Type} (s : I → Prop) [DecidablePred s]
    (x : SquareSequence I) : ‖maskSquare s x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num)
  intro i
  change ‖if s i then x i else 0‖ ≤ ‖x i‖
  split_ifs <;> simp

/-- Bounded reindexing as a complex continuous linear map. -/
def reindexSquareCLM {I : Type} (e : I ≃ I) :
    SquareSequence I →L[ℂ] SquareSequence I :=
  ({ toFun := reindexSquare e
     map_add' := by intro x y; ext i; rfl
     map_smul' := by intro c x; ext i; rfl } :
       SquareSequence I →ₗ[ℂ] SquareSequence I).mkContinuous 1
    (by intro x; simpa using le_of_eq (reindexSquare_norm e x))

/-- Pointwise additivity of the concrete mask, isolated before operator packaging. -/
theorem maskSquare_add {I : Type} (s : I → Prop) [DecidablePred s]
    (x y : SquareSequence I) : maskSquare s (x + y) = maskSquare s x + maskSquare s y := by
  ext i
  change (if s i then x i + y i else 0) =
    (if s i then x i else 0) + (if s i then y i else 0)
  by_cases hi : s i <;> simp [hi]

/-- Bounded coordinate mask as a complex continuous linear map. -/
def maskSquareCLM {I : Type} (s : I → Prop) [DecidablePred s] :
    SquareSequence I →L[ℂ] SquareSequence I :=
  ({ toFun := maskSquare s
     map_add' := maskSquare_add s
     map_smul' := by
       intro c x
       ext i
       by_cases hi : s i <;> simp [maskSquare, hi] } :
       SquareSequence I →ₗ[ℂ] SquareSequence I).mkContinuous 1
    (by intro x; simpa using maskSquare_norm_le s x)

/-- One Hilbert space for both components; `true` means upper and `false` lower. -/
abbrev SectorSquare (n : ℤ) : Type := SquareSequence (Bool × Sector n)

/-- The total index permutation combines component exchange and spectral reflection. -/
def ownModePermutation (n : ℤ) : (Bool × Sector n) ≃ (Bool × Sector n) :=
  Equiv.prodCongr Equiv.boolNot (reflectEquiv n)

/-- The bounded own-mode coordinate operator on the actual square-summable space. -/
def ownModeSquare (n : ℤ) : SectorSquare n →L[ℂ] SectorSquare n :=
  (maskSquareCLM (fun i : Bool × Sector n => i.1 = true)).comp
    (reindexSquareCLM (ownModePermutation n))

/-- Resonant coordinate projection in the genuine Hilbert space. -/
def resonantSquare (n : ℤ) : SectorSquare n →L[ℂ] SectorSquare n :=
  maskSquareCLM (fun i : Bool × Sector n => i.2 = resonantIndex n)

/-- The complementary coordinate projection is exactly identity minus resonant projection. -/
def complementarySquare (n : ℤ) : SectorSquare n →L[ℂ] SectorSquare n :=
  ContinuousLinearMap.id ℂ (SectorSquare n) - resonantSquare n

@[simp] theorem ownModeSquare_upper_apply (n : ℤ) (x : SectorSquare n) (m : Sector n) :
    ownModeSquare n x (true, m) = x (false, reflectIndex n m) := rfl

@[simp] theorem ownModeSquare_lower_apply (n : ℤ) (x : SectorSquare n) (m : Sector n) :
    ownModeSquare n x (false, m) = 0 := rfl

@[simp] theorem resonantSquare_apply (n : ℤ) (x : SectorSquare n) (i : Bool × Sector n) :
    resonantSquare n x i = if i.2 = resonantIndex n then x i else 0 := rfl

@[simp] theorem complementarySquare_apply (n : ℤ) (x : SectorSquare n)
    (i : Bool × Sector n) :
    complementarySquare n x i = if i.2 = resonantIndex n then 0 else x i := by
  change x i - (if i.2 = resonantIndex n then x i else 0) = _
  split_ifs <;> simp

/-- Concrete bounded-operator `Q H_n P = 0` on the square-summable coordinate space. -/
theorem complementary_ownModeSquare_resonant_zero (n : ℤ) :
    (complementarySquare n).comp ((ownModeSquare n).comp (resonantSquare n)) = 0 := by
  ext x ⟨b,m⟩
  cases b <;> by_cases hm : m = resonantIndex n <;> simp [hm]

/-- Concrete bounded-operator `P H_n Q = 0` on the square-summable coordinate space. -/
theorem resonant_ownModeSquare_complementary_zero (n : ℤ) :
    (resonantSquare n).comp ((ownModeSquare n).comp (complementarySquare n)) = 0 := by
  ext x ⟨b,m⟩
  cases b <;> by_cases hm : m = resonantIndex n <;> simp [hm]

/-- The coordinate own-mode operator is a contraction. -/
theorem ownModeSquare_norm_le_one (n : ℤ) : ‖ownModeSquare n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖maskSquare _ (reindexSquare (ownModePermutation n) x)‖ ≤ 1 * ‖x‖
  simpa [reindexSquare_norm] using maskSquare_norm_le
    (fun i : Bool × Sector n => i.1 = true) (reindexSquare (ownModePermutation n) x)

/-- Exact action on every lower component Hilbert coordinate unit vector. -/
theorem ownModeSquare_lower_single (n : ℤ) (m : Sector n) :
    ownModeSquare n (lp.single 2 (false, m) (1 : ℂ)) =
      lp.single 2 (true, reflectIndex n m) (1 : ℂ) := by
  have hiff (i : Sector n) : reflectIndex n i = m ↔ i = reflectIndex n m := by
    constructor
    · intro h
      have hh := congrArg (reflectIndex n) h
      simpa using hh
    · rintro rfl
      simp
  ext ⟨b,i⟩
  cases b <;> simp [lp.single_apply, Pi.single, Function.update_apply, hiff]

/-- The contraction bound is sharp: the genuine l2 operator norm is one. -/
theorem ownModeSquare_norm (n : ℤ) : ‖ownModeSquare n‖ = 1 := by
  apply le_antisymm (ownModeSquare_norm_le_one n)
  have h := (ownModeSquare n).le_opNorm
    (lp.single 2 (false, resonantIndex n) (1 : ℂ))
  rw [ownModeSquare_lower_single] at h
  simpa [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using h


/-- The resonant Hilbert coordinate map is idempotent. -/
theorem resonantSquare_idempotent (n : ℤ) :
    (resonantSquare n).comp (resonantSquare n) = resonantSquare n := by
  ext x ⟨b,m⟩
  by_cases hm : m = resonantIndex n <;> simp [hm]

/-- The complementary Hilbert coordinate map is idempotent. -/
theorem complementarySquare_idempotent (n : ℤ) :
    (complementarySquare n).comp (complementarySquare n) = complementarySquare n := by
  ext x ⟨b,m⟩
  by_cases hm : m = resonantIndex n <;> simp [hm]

/-- The two projections sum to the actual Hilbert-space identity. -/
theorem resonantSquare_add_complementary (n : ℤ) :
    resonantSquare n + complementarySquare n = ContinuousLinearMap.id ℂ (SectorSquare n) := by
  ext x ⟨b,m⟩
  by_cases hm : m = resonantIndex n <;> simp [hm]

/-- The resonant Hilbert projection is a contraction. -/
theorem resonantSquare_norm_le_one (n : ℤ) : ‖resonantSquare n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖maskSquare (fun i : Bool × Sector n => i.2 = resonantIndex n) x‖ ≤ 1 * ‖x‖
  simpa using maskSquare_norm_le (fun i : Bool × Sector n => i.2 = resonantIndex n) x

/-- The complementary Hilbert projection is a contraction. -/
theorem complementarySquare_norm_le_one (n : ℤ) : ‖complementarySquare n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  apply lp.norm_mono (by norm_num)
  rintro ⟨b,m⟩
  by_cases hm : m = resonantIndex n <;> simp [hm]

/-- Orthogonality follows from the actual disjoint coordinate supports.
The imported HasSum theorem proves inner-series summability before uniqueness.
-/
theorem resonantSquare_inner_complementary (n : ℤ) (x y : SectorSquare n) :
    inner ℂ (resonantSquare n x) (complementarySquare n y) = 0 := by
  have hz : ∀ i : Bool × Sector n,
      inner ℂ (resonantSquare n x i) (complementarySquare n y i) = 0 := by
    rintro ⟨b,m⟩
    by_cases hm : m = resonantIndex n <;> simp [hm]
  have hzero : HasSum
      (fun i : Bool × Sector n => inner ℂ (resonantSquare n x i) (complementarySquare n y i)) 0 := by
    simpa only [hz] using (hasSum_zero : HasSum (fun _ : Bool × Sector n => (0 : ℂ)) 0)
  exact (lp.hasSum_inner (resonantSquare n x) (complementarySquare n y)).unique hzero

end NlsGge.Schur
