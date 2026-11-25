import NlsGge.Schur.ParityFourier
import NlsGge.Schur.OwnModeSequence
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# The actual complete Fourier basis of the physical parity kernel

Fourier support is derived from the actual translation operator, not assumed.
The restricted representation is constructed from a proved orthonormal family
with zero orthogonal complement. The source interval isometry remains separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

theorem spectralSign_star (n : ℤ) : star (spectralSign n) = spectralSign n := by
  unfold spectralSign
  split_ifs <;> simp

theorem spectralSign_mul_self (n : ℤ) : spectralSign n * spectralSign n = 1 := by
  unfold spectralSign
  split_ifs <;> simp

theorem spectralSign_eq_iff (m n : ℤ) :
    spectralSign m = spectralSign n ↔ m % 2 = n % 2 := by
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn <;>
    norm_num [spectralSign, hm, hn]

/-- The full Haar Fourier basis gives the actual inner-product coefficient.
The imported contract is applied explicitly before identifying its basis vector.
-/
theorem spectralBasis_repr_inner (f : SpectralScalarL2) (m : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr f m = inner ℂ (spectralBasis m) f := by
  have h := (fourierBasis (T := (2 : ℝ))).repr_apply_apply f m
  simpa only [coe_fourierBasis, spectralBasis, SpectralScalarL2, spectralHaar] using! h

/-- Actual half-translation Fourier coefficient action for every L² class. -/
theorem halfTranslation_repr (f : SpectralScalarL2) (m : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr (halfTranslation f) m =
      spectralSign m * (fourierBasis (T := (2 : ℝ))).repr f m := by
  have hi := (Lp.compMeasurePreservingₗᵢ ℂ
    (fun x : SpectralCircle => x + ((1 : ℝ) : SpectralCircle))
    halfShift_preserving).inner_map_map (spectralBasis m) f
  change inner ℂ (halfTranslation (spectralBasis m)) (halfTranslation f) =
    inner ℂ (spectralBasis m) f at hi
  rw [halfTranslation_basis, inner_smul_left] at hi
  change star (spectralSign m) * inner ℂ (spectralBasis m) (halfTranslation f) =
    inner ℂ (spectralBasis m) f at hi
  rw [spectralSign_star] at hi
  rw [spectralBasis_repr_inner, spectralBasis_repr_inner]
  calc
    inner ℂ (spectralBasis m) (halfTranslation f) =
        (spectralSign m * spectralSign m) *
          inner ℂ (spectralBasis m) (halfTranslation f) := by
      rw [spectralSign_mul_self, one_mul]
    _ = spectralSign m * (spectralSign m *
        inner ℂ (spectralBasis m) (halfTranslation f)) := mul_assoc _ _ _
    _ = spectralSign m * inner ℂ (spectralBasis m) f := by rw [hi]

/-- The actual parity kernel equals support in the prescribed signed sector. -/
theorem mem_scalarParity_iff_fourier_support (n : ℤ) (f : SpectralScalarL2) :
    f ∈ scalarParity n ↔
      ∀ m : ℤ, m % 2 ≠ n % 2 →
        (fourierBasis (T := (2 : ℝ))).repr f m = 0 := by
  constructor
  · intro hf m hm
    have he := congrArg
      (fun g : SpectralScalarL2 => (fourierBasis (T := (2 : ℝ))).repr g m)
      ((mem_scalarParity n f).mp hf)
    change (fourierBasis (T := (2 : ℝ))).repr (halfTranslation f) m =
      (fourierBasis (T := (2 : ℝ))).repr (spectralSign n • f) m at he
    have hs : (fourierBasis (T := (2 : ℝ))).repr (spectralSign n • f) m =
        spectralSign n * (fourierBasis (T := (2 : ℝ))).repr f m := by
      rw [spectralBasis_repr_inner, spectralBasis_repr_inner, inner_smul_right]
    rw [halfTranslation_repr, hs] at he
    have hne : spectralSign m ≠ spectralSign n :=
      fun h => hm ((spectralSign_eq_iff m n).mp h)
    have hz : (spectralSign m - spectralSign n) *
        (fourierBasis (T := (2 : ℝ))).repr f m = 0 := by
      rw [sub_mul, he, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  · intro hf
    rw [mem_scalarParity]
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    apply lp.ext
    funext m
    have hs : (fourierBasis (T := (2 : ℝ))).repr (spectralSign n • f) m =
        spectralSign n * (fourierBasis (T := (2 : ℝ))).repr f m := by
      rw [spectralBasis_repr_inner, spectralBasis_repr_inner, inner_smul_right]
    rw [halfTranslation_repr, hs]
    by_cases hm : m % 2 = n % 2
    · rw [spectralSign_eq_of_parity m n hm]
    · rw [hf m hm, mul_zero, mul_zero]

/-- A permitted Fourier vector in the actual closed parity subspace. -/
def scalarParityVector (n : ℤ) (m : Sector n) : scalarParity n :=
  ⟨spectralBasis m.val, spectralBasis_mem_scalarParity n m⟩

theorem scalarParityVector_orthonormal (n : ℤ) :
    Orthonormal ℂ (scalarParityVector n) := by
  have hfull : Orthonormal ℂ (fun m : Sector n => spectralBasis m.val) := by
    simpa only [spectralBasis, SpectralScalarL2, spectralHaar, Sector, Function.comp_def] using!
      (orthonormal_fourier (T := (2 : ℝ))).comp
        (Subtype.val : Sector n → ℤ) Subtype.val_injective
  exact hfull.codRestrict (scalarParity n) (spectralBasis_mem_scalarParity n)

/-- Completeness of the restricted Fourier family is derived from full Fourier injectivity. -/
theorem scalarParityVector_orthogonal_eq_bot (n : ℤ) :
    (Submodule.span ℂ (Set.range (scalarParityVector n)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    apply Subtype.ext
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    apply lp.ext
    funext m
    have hc : (fourierBasis (T := (2 : ℝ))).repr f.val m = 0 := by
      by_cases hm : m % 2 = n % 2
      · have hinner := (Submodule.mem_orthogonal
          (Submodule.span ℂ (Set.range (scalarParityVector n))) f).mp hf
          (scalarParityVector n ⟨m, hm⟩)
          (Submodule.subset_span (Set.mem_range_self (⟨m, hm⟩ : Sector n)))
        change inner ℂ (spectralBasis m) f.val = 0 at hinner
        rw [spectralBasis_repr_inner]
        exact hinner
      · exact (mem_scalarParity_iff_fourier_support n f.val).mp f.property m hm
    change (fourierBasis (T := (2 : ℝ))).repr f.val m =
      (fourierBasis (T := (2 : ℝ))).repr (0 : SpectralScalarL2) m
    have hz : (fourierBasis (T := (2 : ℝ))).repr (0 : SpectralScalarL2) m = 0 := by
      rw [spectralBasis_repr_inner, inner_zero_right]
    simpa only using! hc.trans hz.symm
  · exact bot_le

/-- Derived complete basis; no supplied Fourier-isometry premise. -/
def scalarParityFourierBasis (n : ℤ) : HilbertBasis (Sector n) ℂ (scalarParity n) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (scalarParityVector_orthonormal n) (scalarParityVector_orthogonal_eq_bot n)

/-- The actual parity Fourier representation into a genuine square-summable carrier. -/
def scalarParityRepr (n : ℤ) : scalarParity n ≃ₗᵢ[ℂ] SquareSequence (Sector n) :=
  (scalarParityFourierBasis n).repr

theorem scalarParityRepr_apply (n : ℤ) (f : scalarParity n) (m : Sector n) :
    scalarParityRepr n f m =
      (fourierBasis (T := (2 : ℝ))).repr f.val m.val := by
  rw [spectralBasis_repr_inner]
  simp only [scalarParityRepr, HilbertBasis.repr_apply_apply,
    scalarParityFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot,
    scalarParityVector, Submodule.coe_inner, coe_fourierBasis, spectralBasis]

end NlsGge.Schur
