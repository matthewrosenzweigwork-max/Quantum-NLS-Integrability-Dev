import NlsGge.Schur.SignedInterval
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Genuine paired reflected Fourier representation

The upper frequency is +m and the lower frequency is −m. The complete mixed
family constructs the representation on the actual Bool sum-of-squares norm.
The unit-interval equivalence is derived from the constructed signed extension.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Schur

/-- Negation preserves every signed parity sector. -/
def negateIndex (n : ℤ) (m : Sector n) : Sector n :=
  ⟨-m.val, by have hm := m.property; omega⟩

@[simp] theorem negateIndex_val (n : ℤ) (m : Sector n) :
    (negateIndex n m).val = -m.val := rfl

@[simp] theorem negateIndex_involutive (n : ℤ) (m : Sector n) :
    negateIndex n (negateIndex n m) = m := by
  apply Subtype.ext
  simp [negateIndex]

def negateEquiv (n : ℤ) : Sector n ≃ Sector n where
  toFun := negateIndex n
  invFun := negateIndex n
  left_inv := negateIndex_involutive n
  right_inv := negateIndex_involutive n

@[simp] theorem negateIndex_eq_iff (n : ℤ) (m l : Sector n) :
    negateIndex n m = negateIndex n l ↔ m = l :=
  (negateEquiv n).injective.eq_iff

/-- `true` is upper +m, `false` is lower −m. -/
def mixedIndex (n : ℤ) (i : Bool × Sector n) : Sector n :=
  if i.1 = true then i.2 else negateIndex n i.2

abbrev ParityPair (n : ℤ) : Type := PiLp 2 (fun _ : Bool => scalarParity n)

abbrev SourcePairL2 : Type := PiLp 2 (fun _ : Bool => SourceIntervalL2)

def parityPairVector (n : ℤ) (i : Bool × Sector n) : ParityPair n :=
  PiLp.single 2 i.1 (scalarParityVector n (mixedIndex n i))

theorem parityPairVector_orthonormal (n : ℤ) :
    Orthonormal ℂ (parityPairVector n) := by
  classical
  have hs := orthonormal_iff_ite.mp (scalarParityVector_orthonormal n)
  simp only [Submodule.coe_inner] at hs
  rw [orthonormal_iff_ite]
  rintro ⟨b,m⟩ ⟨c,l⟩
  cases b <;> cases c <;>
    simp [parityPairVector, mixedIndex, PiLp.inner_apply, hs]

/-- The actual scalar representation coefficient in terms of its constructed vector. -/
theorem scalarParityRepr_inner (n : ℤ) (f : scalarParity n) (m : Sector n) :
    scalarParityRepr n f m = inner ℂ (scalarParityVector n m) f := by
  simp only [scalarParityRepr, HilbertBasis.repr_apply_apply,
    scalarParityFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- Completeness uses component coefficients and the proved signed permutation. -/
theorem parityPairVector_orthogonal_eq_bot (n : ℤ) :
    (Submodule.span ℂ (Set.range (parityPairVector n)))ᗮ = ⊥ := by
  classical
  apply le_antisymm
  · intro f hf
    change f = 0
    have hi (i : Bool × Sector n) :
        inner ℂ (scalarParityVector n (mixedIndex n i)) (f i.1) = 0 := by
      have h := (Submodule.mem_orthogonal
        (Submodule.span ℂ (Set.range (parityPairVector n))) f).mp hf
        (parityPairVector n i)
        (Submodule.subset_span (Set.mem_range_self i))
      rcases i with ⟨b,m⟩
      cases b <;>
        simpa [parityPairVector, mixedIndex, PiLp.inner_apply, Fintype.sum_bool] using h
    apply PiLp.ext
    intro b
    apply (scalarParityRepr n).injective
    apply lp.ext
    funext m
    have hc : scalarParityRepr n (f b) m = 0 := by
      rw [scalarParityRepr_inner]
      cases b
      · simpa [mixedIndex] using hi (false, negateIndex n m)
      · simpa [mixedIndex] using hi (true, m)
    have hz : scalarParityRepr n (0 : scalarParity n) m = 0 := by
      rw [scalarParityRepr_inner, inner_zero_right]
    change scalarParityRepr n (f b) m = scalarParityRepr n (0 : scalarParity n) m
    exact hc.trans hz.symm
  · exact bot_le

/-- Constructed only after the true mixed family is proved orthonormal and complete. -/
def parityPairFourierBasis (n : ℤ) :
    HilbertBasis (Bool × Sector n) ℂ (ParityPair n) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (parityPairVector_orthonormal n) (parityPairVector_orthogonal_eq_bot n)

def parityPairRepr (n : ℤ) : ParityPair n ≃ₗᵢ[ℂ] SectorSquare n :=
  (parityPairFourierBasis n).repr

theorem parityPairRepr_apply (n : ℤ) (f : ParityPair n) (i : Bool × Sector n) :
    parityPairRepr n f i = scalarParityRepr n (f i.1) (mixedIndex n i) := by
  classical
  rw [scalarParityRepr_inner]
  change (parityPairFourierBasis n).repr f i = _
  rw [HilbertBasis.repr_apply_apply]
  simp only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rcases i with ⟨b,m⟩
  cases b <;>
    simp [parityPairVector, mixedIndex, PiLp.inner_apply, Fintype.sum_bool]

theorem parityPairRepr_vector (n : ℤ) (i : Bool × Sector n) :
    parityPairRepr n (parityPairVector n i) = lp.single 2 i (1 : ℂ) := by
  classical
  have h := (parityPairFourierBasis n).repr_self i
  simpa only [parityPairRepr, parityPairFourierBasis,
    HilbertBasis.coe_mkOfOrthogonalEqBot] using h

/-- The actual onto unit-interval map has no √2 scaling. -/
def parityPairIntervalEquiv (n : ℤ) : ParityPair n ≃ₗᵢ[ℂ] SourcePairL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Bool => scalarParityIntervalEquiv n)

def sourcePairRepr (n : ℤ) : SourcePairL2 ≃ₗᵢ[ℂ] SectorSquare n :=
  (parityPairIntervalEquiv n).symm.trans (parityPairRepr n)

def sourcePairVector (n : ℤ) (i : Bool × Sector n) : SourcePairL2 :=
  parityPairIntervalEquiv n (parityPairVector n i)

end NlsGge.Schur
