import NlsGge.Schur.ActualComplementarySchurUnitAndAnalyticInverse23
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

open scoped InnerProduct

/-- The actual coordinate block swap on the full two-channel square-summable
carrier.  The sector coordinate is left unchanged. -/
def actualCoordinateBlockSwap23 (n : ℤ) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  reindexSquareCLM (Equiv.prodCongr Equiv.boolNot (Equiv.refl (Sector n)))

@[simp] theorem actualCoordinateBlockSwap23_apply
    (n : ℤ) (x : SectorSquare n) (i : Bool × Sector n) :
    actualCoordinateBlockSwap23 n x i = x (!i.1, i.2) := rfl

/-- Coordinatewise complex conjugation followed by the actual component swap.
This is semilinear for complex conjugation, not a complex-linear operator. -/
def actualCoordinateConjugation23 (n : ℤ) :
    SectorSquare n →SL[starRingEnd ℂ] SectorSquare n :=
  (actualCoordinateBlockSwap23 n : SectorSquare n →SL[RingHom.id ℂ] SectorSquare n) ∘SL
    ((starL ℂ : SectorSquare n ≃L⋆[ℂ] SectorSquare n).toContinuousLinearMap)

@[simp] theorem actualCoordinateConjugation23_apply
    (n : ℤ) (x : SectorSquare n) (i : Bool × Sector n) :
    actualCoordinateConjugation23 n x i = star (x (!i.1, i.2)) := by
  simp [actualCoordinateConjugation23]

theorem actualCoordinateConjugation23_involutive (n : ℤ) (x : SectorSquare n) :
    actualCoordinateConjugation23 n
      (actualCoordinateConjugation23 n x) = x := by
  ext i
  cases i with
  | mk b m => cases b <;> simp [actualCoordinateConjugation23_apply]


/-- Coordinate conjugation acts on the actual single-coordinate basis by
swapping channels and conjugating the coefficient. -/
theorem actualCoordinateConjugation23_single (n : ℤ) (b : Bool) (m : Sector n) :
    actualCoordinateConjugation23 n (lp.single 2 (b, m) (1 : ℂ)) =
      lp.single 2 (!b, m) (1 : ℂ) := by
  classical
  ext i
  rcases i with ⟨c, k⟩
  rw [actualCoordinateConjugation23_apply]
  cases b <;> cases c <;> by_cases hkm : k = m <;>
    simp [lp.single_apply, hkm]

/-- The transpose convention used in the Schur argument is `J Tᵀ J`,
implemented as `C T† C` for the concrete coordinate conjugation `C=J K`.
It is complex-linear because both outer maps are conjugate-linear. -/
def actualCoordinateTranspose23 (n : ℤ) (T : SectorSquare n →L[ℂ] SectorSquare n) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  (actualCoordinateConjugation23 n ∘SL
      (T.adjoint : SectorSquare n →SL[RingHom.id ℂ] SectorSquare n)) ∘SL
    actualCoordinateConjugation23 n

/-- The actual transpose reverses products.  No self-adjointness or relation
between potential components is used. -/
theorem actualCoordinateTranspose23_comp (n : ℤ)
    (T S : SectorSquare n →L[ℂ] SectorSquare n) :
    actualCoordinateTranspose23 n (T.comp S) =
      (actualCoordinateTranspose23 n S).comp (actualCoordinateTranspose23 n T) := by
  ext x i
  simp [actualCoordinateTranspose23, actualCoordinateConjugation23_apply,
    actualCoordinateBlockSwap23_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compSL_apply,
    actualCoordinateConjugation23_involutive, star_mul, star_star]

/-- Coordinate diagonal maps with an explicit boundedness proof. -/
def actualCoordinateDiagonal23 {I : Type*} (d : I → ℂ)
    (hd : ∀ i, ‖d i‖ ≤ 1) : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  lp.mapCLM 2 (fun i => d i • ContinuousLinearMap.id ℂ ℂ) zero_le_one (by
    intro i
    simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd i)

@[simp] theorem actualCoordinateDiagonal23_apply {I : Type*}
    (d : I → ℂ) (hd : ∀ i, ‖d i‖ ≤ 1)
    (x : lp (fun _ : I => ℂ) 2) (i : I) :
    actualCoordinateDiagonal23 d hd x i = d i * x i := rfl

/-- The adjoint of an actual diagonal multiplier conjugates each diagonal
coefficient; this supplies the scalar step for the transpose identities. -/
theorem actualCoordinateDiagonal23_adjoint_apply {I : Type*}
    (d : I → ℂ) (hd : ∀ i, ‖d i‖ ≤ 1)
    (x : lp (fun _ : I => ℂ) 2) (i : I) :
    (actualCoordinateDiagonal23 d hd).adjoint x i = star (d i) * x i := by
  classical
  let e : lp (fun _ : I => ℂ) 2 := lp.single 2 i (1 : ℂ)
  have he : actualCoordinateDiagonal23 d hd e = lp.single 2 i (d i) := by
    apply lp.ext
    funext j
    by_cases hji : j = i
    · subst j
      simp [e, actualCoordinateDiagonal23_apply]
    · simp [e, actualCoordinateDiagonal23_apply, hji]
  have h := ContinuousLinearMap.adjoint_inner_left
    (actualCoordinateDiagonal23 d hd) e x
  rw [lp.inner_single_right, he, lp.inner_single_right] at h
  apply star_injective
  simpa [star_mul, star_star, mul_comm] using h

/-- The transpose of a diagonal multiplier reads the coefficient at the
swapped coordinate. -/
theorem actualCoordinateTranspose23_diagonal {n : ℤ}
    (d : Bool × Sector n → ℂ) (hd : ∀ i, ‖d i‖ ≤ 1) :
    actualCoordinateTranspose23 n (actualCoordinateDiagonal23 d hd) =
      actualCoordinateDiagonal23 (fun i => d (!i.1, i.2))
        (fun i => hd (!i.1, i.2)) := by
  ext x i
  simp [actualCoordinateTranspose23, actualCoordinateConjugation23_apply,
    actualCoordinateBlockSwap23_apply, actualCoordinateDiagonal23_adjoint_apply,
    star_mul, star_star]
  ring

/-- The actual free diagonal is fixed by transpose, even for nonreal spectral
parameter: its coefficient depends on the sector index, not the channel. -/
theorem actualCoordinateTranspose23_freeResolvent (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralDisk n) :
    actualCoordinateTranspose23 n (freeResolventSquare n z hz) =
      freeResolventSquare n z hz := by
  have hdiag : freeResolventSquare n z hz =
      actualCoordinateDiagonal23 (fun i : Bool × Sector n => freeResolventCoeff n z i.2)
        (fun i => freeResolventCoeff_norm_le_one n z hz i.2) := by
    ext x i
    simp [freeResolventSquare, actualCoordinateDiagonal23]
  rw [hdiag, actualCoordinateTranspose23_diagonal]

/-- The actual resonant projection is fixed by transpose. -/
theorem actualCoordinateTranspose23_resonant (n : ℤ) :
    actualCoordinateTranspose23 n (resonantSquare n) = resonantSquare n := by
  have hdiag : resonantSquare n =
      actualCoordinateDiagonal23
        (fun i : Bool × Sector n => if i.2 = resonantIndex n then 1 else 0)
        (by intro i; split_ifs <;> norm_num) := by
    ext x i
    rw [actualCoordinateDiagonal23_apply, resonantSquare_apply]
    by_cases hi : i.2 = resonantIndex n <;> simp [hi]
  rw [hdiag, actualCoordinateTranspose23_diagonal]

/-- The actual complementary projection is fixed by transpose. -/
theorem actualCoordinateTranspose23_complementary (n : ℤ) :
    actualCoordinateTranspose23 n (complementarySquare n) = complementarySquare n := by
  have hdiag : complementarySquare n =
      actualCoordinateDiagonal23
        (fun i : Bool × Sector n => if i.2 = resonantIndex n then 0 else 1)
        (by intro i; split_ifs <;> norm_num) := by
    ext x i
    rw [actualCoordinateDiagonal23_apply, complementarySquare_apply]
    by_cases hi : i.2 = resonantIndex n <;> simp [hi]
  rw [hdiag, actualCoordinateTranspose23_diagonal]

end NlsGge.Schur
