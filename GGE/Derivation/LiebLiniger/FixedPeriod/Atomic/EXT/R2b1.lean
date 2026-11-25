import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.SymplecticGroup

/-! # Intrinsic symplectic Liouville measure

A Darboux basis has matrix `[0,1;-1,0]` for the real bilinear form.
Its basis-normalized additive Haar measure is independent of the Darboux
basis: the change matrix preserves that matrix, hence has absolute determinant
one. This defines the positive Liouville density without choosing orientation
or using a desired coordinate-volume formula as its definition.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open Module MeasureTheory MeasureTheory.Measure

variable {ι V W : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

/-- A real Darboux basis for `ω`, indexed by the first and second member of
each canonical pair. Its matrix is literally `[0,1;-1,0]`. In particular
this certificate implies alternation and nondegeneracy, rather than asserting
anything about volume. -/
structure DarbouxBasis38 (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) where
  basis : Basis (ι ⊕ ι) ℝ V
  matrix_eq : LinearMap.toMatrix₂ basis basis ω = -Matrix.J ι ℝ

namespace DarbouxBasis38

variable {ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Changes between Darboux bases have absolute determinant one. The proof
takes determinants of the bilinear change-of-basis identity. -/
theorem abs_det_change (b c : DarbouxBasis38 (ι := ι) ω) :
    |b.basis.det c.basis| = 1 := by
  classical
  let A := b.basis.toMatrix c.basis
  have hc := LinearMap.toMatrix₂_mul_basis_toMatrix b.basis b.basis
    c.basis c.basis ω
  rw [b.matrix_eq, c.matrix_eq] at hc
  have hJ : A.transpose * Matrix.J ι ℝ * A = Matrix.J ι ℝ := by
    simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_inj] using hc
  have hd := congrArg Matrix.det hJ
  simp only [Matrix.det_mul, Matrix.det_transpose] at hd
  have hj : (Matrix.J ι ℝ).det ≠ 0 := (Matrix.isUnit_det_J ι ℝ).ne_zero
  have hs : A.det * A.det = 1 := by
    apply mul_right_cancel₀ hj
    calc
      A.det * A.det * (Matrix.J ι ℝ).det =
          A.det * (Matrix.J ι ℝ).det * A.det := by ring
      _ = (Matrix.J ι ℝ).det := hd
      _ = 1 * (Matrix.J ι ℝ).det := (one_mul _).symm
  change |A.det| = 1
  rcases mul_self_eq_one_iff.mp hs with h | h <;> simp [h]

/-- Haar normalization in one Darboux basis gives mass one to every other
Darboux parallelepiped, including the zero-dimensional parallelepiped. -/
theorem addHaar_parallelepiped (b c : DarbouxBasis38 (ι := ι) ω) :
    b.basis.addHaar (_root_.parallelepiped c.basis) = 1 := by
  rw [MeasureTheory.Measure.addHaar_parallelepiped, abs_det_change, ENNReal.ofReal_one]

/-- Independence of the Darboux basis. -/
theorem addHaar_eq (b c : DarbouxBasis38 (ι := ι) ω) :
    b.basis.addHaar = c.basis.addHaar := by
  symm
  apply (c.basis.addHaar_eq_iff b.basis.addHaar).2
  exact b.addHaar_parallelepiped c

/-- Transport a Darboux basis along a real linear equivalence preserving
the two forms. This is a statement about forms, with no measure premise. -/
def map (b : DarbouxBasis38 (ι := ι) ω) (e : V ≃ₗ[ℝ] W)
    (η : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (he : ∀ x y, η (e x) (e y) = ω x y) :
    DarbouxBasis38 (ι := ι) η where
  basis := b.basis.map e
  matrix_eq := by
    convert b.matrix_eq using 1
    ext i j
    simpa only [LinearMap.toMatrix₂_apply, Basis.map_apply] using he (b.basis i) (b.basis j)

end DarbouxBasis38

/-- The intrinsic positive Liouville measure of a real symplectic vector
space admitting a Darboux basis. Choose a Darboux basis and normalize additive
Haar measure to give its unit parallelepiped mass one. The theorem
`liouvilleMeasure38_eq` proves that this choice is immaterial. -/
def liouvilleMeasure38 (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h : Nonempty (DarbouxBasis38 (ι := ι) ω)) : Measure V :=
  h.some.basis.addHaar

/-- The intrinsic measure equals normalization in any Darboux basis. -/
theorem liouvilleMeasure38_eq (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h : Nonempty (DarbouxBasis38 (ι := ι) ω)) (b : DarbouxBasis38 (ι := ι) ω) :
    liouvilleMeasure38 ω h = b.basis.addHaar :=
  h.some.addHaar_eq b

/-- The intrinsic measure is additive Haar measure, and hence translation
invariant and finite on compact sets. -/
instance liouvilleMeasure38_isAddHaar (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h : Nonempty (DarbouxBasis38 (ι := ι) ω)) :
    IsAddHaarMeasure (liouvilleMeasure38 ω h) := by
  unfold liouvilleMeasure38
  infer_instance

/-- Existence and uniqueness characterization: among sigma-finite
translation-invariant Borel measures, Liouville measure is exactly the measure
assigning mass one to a Darboux parallelepiped. -/
theorem liouvilleMeasure38_characterization (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h : Nonempty (DarbouxBasis38 (ι := ι) ω)) (b : DarbouxBasis38 (ι := ι) ω)
    (μ : Measure V) [SigmaFinite μ] [IsAddLeftInvariant μ] :
    liouvilleMeasure38 ω h = μ ↔ μ b.basis.parallelepiped = 1 := by
  rw [liouvilleMeasure38_eq ω h b]
  exact b.basis.addHaar_eq_iff μ

/-- Naturality under symplectic linear isomorphisms, including between
different finite-dimensional carriers. -/
theorem liouvilleMeasure38_map (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (η : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hω : Nonempty (DarbouxBasis38 (ι := ι) ω))
    (hη : Nonempty (DarbouxBasis38 (ι := ι) η))
    (e : V ≃L[ℝ] W) (he : ∀ x y, η (e x) (e y) = ω x y) :
    (liouvilleMeasure38 ω hω).map e = liouvilleMeasure38 η hη := by
  let b := hω.some
  haveI : FiniteDimensional ℝ W := (b.basis.map e.toLinearEquiv).finiteDimensional_of_finite
  rw [liouvilleMeasure38_eq ω hω b, Module.Basis.map_addHaar]
  exact (liouvilleMeasure38_eq η hη (b.map e.toLinearEquiv η he)).symm

end LiebLiniger.FixedPeriod.EXT
