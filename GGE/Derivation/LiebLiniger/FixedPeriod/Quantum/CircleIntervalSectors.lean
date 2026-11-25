import LiebLiniger.FixedPeriod.Quantum.CircleIntervalL2
import LiebLiniger.FixedPeriod.Quantum.MixedTensorCore

/-!
Finite-product and symmetric-sector transport between the existing physical
mass-L circle and the literal centered-interval kernel model. The maps are
actual pullbacks, including the empty product, and intertwine permutations.
No coefficient-operator or Hilbert-Schmidt assertion is assumed.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LiebLiniger.FixedPeriod.Quantum

variable (L : ℝ) [Fact (0 < L)]

/-- The measurable centered fundamental-domain representative. -/
def circleIntervalSection (x : AddCircle L) : ℝ :=
  (AddCircle.equivIoc L (-L / 2) x : ℝ)

theorem circleIntervalSection_measurePreserving :
    MeasurePreserving (circleIntervalSection L) (volume : Measure (AddCircle L))
      (transferIntervalMeasure L) := by
  rw [transferIntervalMeasure_eq_Ioc]
  exact (measurePreserving_subtype_coe measurableSet_Ioc).comp
    (AddCircle.measurePreserving_equivIoc L)

theorem circleIntervalSection_projection_ae :
    (fun x : ℝ => circleIntervalSection L (x : AddCircle L)) =ᵐ[transferIntervalMeasure L]
      fun x => x := by
  have hm : ∀ᵐ x ∂transferIntervalMeasure L, x ∈ Ioc (-L / 2) (-L / 2 + L) := by
    rw [transferIntervalMeasure_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioc
  filter_upwards [hm] with x hx
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq hx)

/-- The actual coordinatewise periodic projection on the n-particle space. -/
def intervalToCircleCoordinates (n : ℕ) (x : Fin n → ℝ) : Fin n → AddCircle L :=
  fun i => (x i : AddCircle L)

def circleToIntervalCoordinates (n : ℕ) (x : Fin n → AddCircle L) : Fin n → ℝ :=
  fun i => circleIntervalSection L (x i)

theorem intervalToCircleCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (intervalToCircleCoordinates L n) (transferCoordinateMeasure L n)
      (Measure.pi fun _ : Fin n => (volume : Measure (AddCircle L))) :=
  measurePreserving_pi (fun _ : Fin n => transferIntervalMeasure L)
    (fun _ : Fin n => (volume : Measure (AddCircle L)))
    (fun _ => intervalToCircle_measurePreserving L)

theorem circleToIntervalCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (circleToIntervalCoordinates L n)
      (Measure.pi fun _ : Fin n => (volume : Measure (AddCircle L)))
      (transferCoordinateMeasure L n) :=
  measurePreserving_pi (fun _ : Fin n => (volume : Measure (AddCircle L)))
    (fun _ : Fin n => transferIntervalMeasure L)
    (fun _ => circleIntervalSection_measurePreserving L)

theorem circleToIntervalCoordinates_projection_ae (n : ℕ) :
    (fun x => circleToIntervalCoordinates L n (intervalToCircleCoordinates L n x))
      =ᵐ[transferCoordinateMeasure L n] fun x => x :=
  Measure.ae_eq_pi (fun _ : Fin n => circleIntervalSection_projection_ae L)

/-- This is the actual pullback by the coordinatewise quotient projection. -/
def circleToIntervalProductL2 (n : ℕ) :
    ProductL2 (volume : Measure (AddCircle L)) (Fin n) →ₗᵢ[ℂ]
      ProductL2 (transferIntervalMeasure L) (Fin n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (intervalToCircleCoordinates L n)
    (intervalToCircleCoordinates_measurePreserving L n)

/-- The reverse pullback uses the measurable fundamental-domain representative. -/
def intervalToCircleProductL2 (n : ℕ) :
    ProductL2 (transferIntervalMeasure L) (Fin n) →ₗᵢ[ℂ]
      ProductL2 (volume : Measure (AddCircle L)) (Fin n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (circleToIntervalCoordinates L n)
    (circleToIntervalCoordinates_measurePreserving L n)

theorem circleToIntervalProductL2_coeFn (n : ℕ)
    (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n)) :
    circleToIntervalProductL2 L n f =ᵐ[transferCoordinateMeasure L n]
      fun x => f (intervalToCircleCoordinates L n x) :=
  Lp.coeFn_compMeasurePreserving f (intervalToCircleCoordinates_measurePreserving L n)

theorem circleToIntervalProductL2_intervalToCircle (n : ℕ)
    (f : ProductL2 (transferIntervalMeasure L) (Fin n)) :
    circleToIntervalProductL2 L n (intervalToCircleProductL2 L n f) = f := by
  apply Lp.ext
  have hr := (intervalToCircleCoordinates_measurePreserving L n).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f (circleToIntervalCoordinates_measurePreserving L n))
  filter_upwards [circleToIntervalProductL2_coeFn L n (intervalToCircleProductL2 L n f),
    hr, circleToIntervalCoordinates_projection_ae L n] with x hx hrx hxx
  dsimp only [Function.comp_apply] at hrx
  change (intervalToCircleProductL2 L n f) (intervalToCircleCoordinates L n x) =
    f (circleToIntervalCoordinates L n (intervalToCircleCoordinates L n x)) at hrx
  rw [hx, hrx, hxx]

/-- Genuine full-sector unitary, onto by an explicit reverse pullback. -/
def circleIntervalProductL2Equiv (n : ℕ) :
    ProductL2 (volume : Measure (AddCircle L)) (Fin n) ≃ₗᵢ[ℂ]
      ProductL2 (transferIntervalMeasure L) (Fin n) :=
  LinearIsometryEquiv.ofSurjective (circleToIntervalProductL2 L n)
    (fun f => ⟨intervalToCircleProductL2 L n f,
      circleToIntervalProductL2_intervalToCircle L n f⟩)

@[simp] theorem circleIntervalProductL2Equiv_apply (n : ℕ)
    (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n)) :
    circleIntervalProductL2Equiv L n f = circleToIntervalProductL2 L n f := rfl

/-- All elementary tensor families are transported by the checked one-body
unitary in each factor; this includes the empty tensor/vacuum. -/
theorem circleIntervalProductL2Equiv_mixedTensor (n : ℕ)
    (u : Fin n → Lp ℂ 2 (volume : Measure (AddCircle L))) :
    circleIntervalProductL2Equiv L n (mixedTensorL2 (volume : Measure (AddCircle L)) u) =
      mixedTensorL2 (transferIntervalMeasure L) (fun i => circleIntervalL2Equiv L (u i)) := by
  apply Lp.ext
  have hm := (intervalToCircleCoordinates_measurePreserving L n).quasiMeasurePreserving.ae_eq_comp
    (coeFn_mixedTensorL2 (volume : Measure (AddCircle L)) u)
  have hf : (fun x : Fin n → ℝ => fun i => circleIntervalL2Equiv L (u i) (x i))
      =ᵐ[transferCoordinateMeasure L n]
      fun x => fun i => u i (x i : AddCircle L) := by
    exact Measure.ae_eq_pi (μ := fun _ : Fin n => transferIntervalMeasure L)
      (f := fun i x => circleIntervalL2Equiv L (u i) x)
      (f' := fun i x => u i (x : AddCircle L))
      (fun i => circleToIntervalL2_coeFn L (u i))
  filter_upwards [circleToIntervalProductL2_coeFn L n
      (mixedTensorL2 (volume : Measure (AddCircle L)) u), hm,
    coeFn_mixedTensorL2 (transferIntervalMeasure L) (fun i => circleIntervalL2Equiv L (u i)),
    hf] with x hx hmx htarget hfx
  dsimp only [Function.comp_apply] at hmx
  change (circleToIntervalProductL2 L n (mixedTensorL2 (volume : Measure (AddCircle L)) u)) x =
    (mixedTensorL2 (transferIntervalMeasure L) (fun i => circleIntervalL2Equiv L (u i))) x
  rw [hx, hmx, htarget]
  exact (congrArg (fun v : Fin n → ℂ => ∏ i, v i) hfx).symm

/-- Coordinatewise projection commutes exactly with every slot permutation. -/
theorem circleToIntervalProductL2_permutation (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n)) :
    circleToIntervalProductL2 L n (permutationL2 (volume : Measure (AddCircle L)) σ f) =
      permutationL2 (transferIntervalMeasure L) σ (circleToIntervalProductL2 L n f) := by
  apply Lp.ext
  have hcircle := (intervalToCircleCoordinates_measurePreserving L n).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f
      (coordinatePermutation_measurePreserving (volume : Measure (AddCircle L)) σ))
  have hinter := (coordinatePermutation_measurePreserving (transferIntervalMeasure L) σ).quasiMeasurePreserving.ae_eq_comp
      (circleToIntervalProductL2_coeFn L n f)
  filter_upwards [circleToIntervalProductL2_coeFn L n
      (permutationL2 (volume : Measure (AddCircle L)) σ f), hcircle,
    Lp.coeFn_compMeasurePreserving (circleToIntervalProductL2 L n f)
      (coordinatePermutation_measurePreserving (transferIntervalMeasure L) σ),
    hinter] with x hx hcx hpx hix
  dsimp only [Function.comp_apply] at hcx hpx hix
  change (permutationL2 (volume : Measure (AddCircle L)) σ f)
    (intervalToCircleCoordinates L n x) =
    f (coordinatePermutation σ (intervalToCircleCoordinates L n x)) at hcx
  change (permutationL2 (transferIntervalMeasure L) σ (circleToIntervalProductL2 L n f)) x =
    (circleToIntervalProductL2 L n f) (coordinatePermutation σ x) at hpx
  rw [hx, hcx, hpx, hix]
  congr 1
  funext i
  simp only [coordinatePermutation_apply, intervalToCircleCoordinates]

/-- The normalized genuine permutation averages intertwine. -/
theorem circleToIntervalProductL2_symmetrize (n : ℕ)
    (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n)) :
    circleToIntervalProductL2 L n (symmetrizeL2 (volume : Measure (AddCircle L)) f) =
      symmetrizeL2 (transferIntervalMeasure L) (circleToIntervalProductL2 L n f) := by
  simp only [symmetrizeL2_apply, map_smul, map_sum, circleToIntervalProductL2_permutation]

/-- Membership in the closed invariant sector is preserved in both directions. -/
theorem circleIntervalProductL2Equiv_mem_symmetric_iff (n : ℕ)
    (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n)) :
    f ∈ SymmetricSectorSpace (volume : Measure (AddCircle L)) n ↔
      circleIntervalProductL2Equiv L n f ∈ SymmetricSectorSpace (transferIntervalMeasure L) n := by
  rw [mem_symmetricSectorSpace, mem_symmetricSectorSpace]
  constructor
  · intro hf
    change symmetrizeL2 (transferIntervalMeasure L) (circleToIntervalProductL2 L n f) = _
    rw [← circleToIntervalProductL2_symmetrize, hf]
    rfl
  · intro hf
    apply (circleToIntervalProductL2 L n).injective
    rw [circleToIntervalProductL2_symmetrize]
    exact hf

/-- The SAME physical symmetric sector transported to the literal interval
kernel model, with no finite-dimensional restriction or normalization factor. -/
def circleIntervalSymmetricSectorEquiv (n : ℕ) :
    SymmetricSector (volume : Measure (AddCircle L)) n ≃ₗᵢ[ℂ]
      SymmetricSector (transferIntervalMeasure L) n where
  toFun f := ⟨circleIntervalProductL2Equiv L n f,
    (circleIntervalProductL2Equiv_mem_symmetric_iff L n f).mp f.property⟩
  invFun f := ⟨(circleIntervalProductL2Equiv L n).symm f,
    (circleIntervalProductL2Equiv_mem_symmetric_iff L n _).mpr (by
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact f.property)⟩
  left_inv f := by
    apply Subtype.ext
    exact (circleIntervalProductL2Equiv L n).symm_apply_apply f
  right_inv f := by
    apply Subtype.ext
    exact (circleIntervalProductL2Equiv L n).apply_symm_apply f
  map_add' f g := by
    apply Subtype.ext
    exact map_add (circleIntervalProductL2Equiv L n)
      (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n))
      (g : ProductL2 (volume : Measure (AddCircle L)) (Fin n))
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (circleIntervalProductL2Equiv L n) c
      (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n))
  norm_map' f := (circleIntervalProductL2Equiv L n).norm_map
    (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n))

@[simp] theorem circleIntervalSymmetricSectorEquiv_coe (n : ℕ)
    (f : SymmetricSector (volume : Measure (AddCircle L)) n) :
    (circleIntervalSymmetricSectorEquiv L n f : ProductL2 (transferIntervalMeasure L) (Fin n)) =
      circleIntervalProductL2Equiv L n (f : ProductL2 (volume : Measure (AddCircle L)) (Fin n)) := rfl

end LiebLiniger.FixedPeriod.Quantum
