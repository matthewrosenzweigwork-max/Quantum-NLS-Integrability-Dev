import NlsGge.Schur.FreeDomainPointwise

/-!
NEW-F02.02 concrete coordinate-domain prerequisite. D is the previously built
bounded complementary diagonal, and the free diagonal acts only on its actual
weighted-lp domain as an unbounded linear map. No physical weak-derivative
domain identification or whole manuscript resolvent bound is asserted here.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Schur

lemma spectralCenter_mul_freeResolventCoeff
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m : Sector n) :
    spectralCenter m.val * freeResolventCoeff n z m =
      z * freeResolventCoeff n z m -
        if m = resonantIndex n then 0 else 1 := by
  by_cases hm : m = resonantIndex n
  · simp [freeResolventCoeff, hm]
  · have hd := spectral_denominator_ne_zero n z hz m hm
    simp only [freeResolventCoeff, if_neg hm]
    field_simp [hd]
    ring

lemma freeWeightedCoordinates_freeResolventSquare
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (x : SectorSquare n) :
    freeWeightedCoordinates n (freeResolventSquare n z hz x) =
      fun i => z * freeResolventSquare n z hz x i - complementarySquare n x i := by
  funext i
  change spectralCenter i.2.val * (freeResolventCoeff n z i.2 * x i) = _
  rw [← mul_assoc, spectralCenter_mul_freeResolventCoeff n z hz]
  rw [complementarySquare_apply, freeResolventSquare_apply]
  by_cases hm : i.2 = resonantIndex n <;> simp [hm] <;> ring

lemma freeResolventSquare_mem_freeWeightedDomain
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (x : SectorSquare n) :
    freeResolventSquare n z hz x ∈ freeWeightedDomainPointwise n := by
  change Memℓp (freeWeightedCoordinates n (freeResolventSquare n z hz x)) 2
  rw [freeWeightedCoordinates_freeResolventSquare n z hz x]
  have he :
      z • (freeResolventSquare n z hz x : Bool × Sector n → ℂ) -
        (complementarySquare n x : Bool × Sector n → ℂ) =
      (fun i => z * freeResolventSquare n z hz x i - complementarySquare n x i) := by
    funext i
    rfl
  rw [← he]
  exact ((lp.memℓp (freeResolventSquare n z hz x)).const_smul z).sub
    (lp.memℓp (complementarySquare n x))

/-- The free diagonal is linear on its proper domain; no boundedness claim. -/
def freeCoordinateDirac (n : ℤ) :
    freeWeightedDomainPointwise n →ₗ[ℂ] SectorSquare n where
  toFun x := ⟨freeWeightedCoordinates n x.val, x.property⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change spectralCenter i.2.val * (x.val i + y.val i) =
      spectralCenter i.2.val * x.val i + spectralCenter i.2.val * y.val i
    ring
  map_smul' a x := by
    apply lp.ext
    funext i
    change spectralCenter i.2.val * (a * x.val i) =
      a * (spectralCenter i.2.val * x.val i)
    ring

@[simp] lemma freeCoordinateDirac_apply
    (n : ℤ) (x : freeWeightedDomainPointwise n) (i : Bool × Sector n) :
    freeCoordinateDirac n x i = spectralCenter i.2.val * x.val i := rfl

def freeShiftedCoordinateDirac (n : ℤ) (z : ℂ) :
    freeWeightedDomainPointwise n →ₗ[ℂ] SectorSquare n :=
  z • (freeWeightedDomainPointwise n).subtype - freeCoordinateDirac n

lemma freeShiftedCoordinateDirac_right_inverse_complement
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (x : SectorSquare n) :
    freeShiftedCoordinateDirac n z
      ⟨freeResolventSquare n z hz x,
        freeResolventSquare_mem_freeWeightedDomain n z hz x⟩ =
      complementarySquare n x := by
  apply lp.ext
  funext i
  change z * freeResolventSquare n z hz x i -
    freeWeightedCoordinates n (freeResolventSquare n z hz x) i = _
  rw [freeWeightedCoordinates_freeResolventSquare n z hz x]
  simp

lemma freeShiftedCoordinateDirac_left_inverse_complement
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : freeWeightedDomainPointwise n) :
    freeResolventSquare n z hz (freeShiftedCoordinateDirac n z x) =
      complementarySquare n x.val := by
  apply lp.ext
  funext i
  change freeResolventCoeff n z i.2 *
    (z * x.val i - spectralCenter i.2.val * x.val i) = _
  rw [complementarySquare_apply]
  by_cases hm : i.2 = resonantIndex n
  · simp [freeResolventCoeff, hm]
  · have hd := spectral_denominator_ne_zero n z hz i.2 hm
    simp only [freeResolventCoeff, if_neg hm]
    field_simp [hd]

end NlsGge.Schur
