import NlsGge.GK38.GradEigenStateL2
import NlsGge.GK38.GradEigenCharacteristic

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
theorem floquet_coefficients (a b c d p m : ℂ)
    (hs : p + m = a + d) (hp : p * m = 1) (hd : a*d-b*c = 1)
    (hb : b ≠ 0) :
    b * ((p-a)/b + (m-a)/b) = d-a ∧
    b * ((p-a)/b) * ((m-a)/b) = -c := by
  constructor
  · field_simp
    linear_combination hs
  · field_simp
    linear_combination hp - a * hs - hd

theorem floquet_eigenvector_algebra (M : PairMat38) (p m : ℂ)
    (hs : p + m = M 0 0 + M 1 1) (hp : p * m = 1)
    (hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (hb : M 0 1 ≠ 0) :
    Matrix.mulVec M (![1, (p-M 0 0)/M 0 1] : PairVec38) =
      p • (![1, (p-M 0 0)/M 0 1] : PairVec38) := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    <;> ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination hp - hd - p * hs

theorem floquet_eigenvector10_algebra (M : PairMat38) (p m : ℂ)
    (hs : p + m = M 0 0 + M 1 1) (hp : p * m = 1)
    (hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (hc : M 1 0 ≠ 0) :
    Matrix.mulVec M (![(p-M 1 1)/M 1 0, 1] : PairVec38) =
      p • (![(p-M 1 1)/M 1 0, 1] : PairVec38) := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination hp - hd - p * hs
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    <;> ring

theorem floquet_polynomial (b c d a r s u v : ℂ)
    (hs : b * (r+s) = d-a) (hp : b*r*s = -c) :
    b * ((u+r*v)*(u+s*v)) = b*u*u+(d-a)*u*v-c*v*v := by
  linear_combination u*v * hs + v*v * hp

theorem monodromy_det_scalar (φ : PotPair) (z : ℂ) :
    monodromyPair φ z 0 0 * monodromyPair φ z 1 1 -
      monodromyPair φ z 0 1 * monodromyPair φ z 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using det_monodromyPair φ z

theorem floquet_gradient01 (φ : PotPair) (z p m : ℂ)
    (hs : p+m = monodromyPair φ z 0 0 + monodromyPair φ z 1 1)
    (hp : p*m = 1) (hb : monodromyPair φ z 0 1 ≠ 0) (t : Time) :
    Complex.I • gradDiscrim38 φ z t = monodromyPair φ z 0 1 •
      starProd38 (state φ z (floquetSeed01 φ z p) t)
        (state φ z (floquetSeed01 φ z m) t) := by
  have hc := floquet_coefficients _ _ _ _ _ _ hs hp (monodromy_det_scalar φ z) hb
  have hpoly (j : Fin 2) := floquet_polynomial _ _ _ _ _ _
    (fundColumn38 φ z t 0 j) (fundColumn38 φ z t 1 j) hc.1 hc.2
  ext i
  fin_cases i <;>
    simp [gradDiscrim38, starProd38, state, floquetSeed01, smul_eq_mul,
      ← mul_assoc, Complex.I_mul_I]
  · linear_combination -(hpoly 1)
  · linear_combination -(hpoly 0)

theorem floquet_gradient10 (φ : PotPair) (z p m : ℂ)
    (hs : p+m = monodromyPair φ z 0 0 + monodromyPair φ z 1 1)
    (hp : p*m = 1) (hb : monodromyPair φ z 1 0 ≠ 0) (t : Time) :
    Complex.I • gradDiscrim38 φ z t = (-monodromyPair φ z 1 0) •
      starProd38 (state φ z (floquetSeed10 φ z p) t)
        (state φ z (floquetSeed10 φ z m) t) := by
  have hs' : p+m = monodromyPair φ z 1 1 + monodromyPair φ z 0 0 := by
    rw [hs, add_comm]
  have hd' : monodromyPair φ z 1 1 * monodromyPair φ z 0 0 -
      monodromyPair φ z 1 0 * monodromyPair φ z 0 1 = 1 := by
    linear_combination monodromy_det_scalar φ z
  have hc := floquet_coefficients _ _ _ _ _ _ hs' hp hd' hb
  have hpoly (j : Fin 2) := floquet_polynomial _ _ _ _ _ _
    (fundColumn38 φ z t 1 j) (fundColumn38 φ z t 0 j) hc.1 hc.2
  ext i
  fin_cases i <;>
    simp [gradDiscrim38, starProd38, state, floquetSeed10, smul_eq_mul,
      ← mul_assoc, Complex.I_mul_I]
  · linear_combination hpoly 1
  · linear_combination hpoly 0

def FloquetGradient01Target : Prop :=
  ∀ (φ : PotPair) (z ξp ξm : ℂ),
    ξp + ξm = monodromyPair φ z 0 0 + monodromyPair φ z 1 1 →
    ξp * ξm = 1 →
    monodromyPair φ z 0 1 ≠ 0 →
    (Matrix.mulVec (monodromyPair φ z)
        (![1, (ξp - monodromyPair φ z 0 0) /
          monodromyPair φ z 0 1] : PairVec38) =
      ξp • (![1, (ξp - monodromyPair φ z 0 0) /
        monodromyPair φ z 0 1] : PairVec38)) ∧
    (Matrix.mulVec (monodromyPair φ z)
        (![1, (ξm - monodromyPair φ z 0 0) /
          monodromyPair φ z 0 1] : PairVec38) =
      ξm • (![1, (ξm - monodromyPair φ z 0 0) /
        monodromyPair φ z 0 1] : PairVec38)) ∧
    ∀ t : Set.Icc (0 : ℝ) 1,
      Complex.I • gradDiscrim38 φ z (t : ℝ) =
        monodromyPair φ z 0 1 •
          starProd38
            (state φ z
              (![1, (ξp - monodromyPair φ z 0 0) /
                monodromyPair φ z 0 1] : PairVec38) t)
            (state φ z
              (![1, (ξm - monodromyPair φ z 0 0) /
                monodromyPair φ z 0 1] : PairVec38) t)

def FloquetGradient10Target : Prop :=
  ∀ (φ : PotPair) (z ξp ξm : ℂ),
    ξp + ξm = monodromyPair φ z 0 0 + monodromyPair φ z 1 1 →
    ξp * ξm = 1 →
    monodromyPair φ z 1 0 ≠ 0 →
    (Matrix.mulVec (monodromyPair φ z)
        (![(ξp - monodromyPair φ z 1 1) /
          monodromyPair φ z 1 0, 1] : PairVec38) =
      ξp • (![(ξp - monodromyPair φ z 1 1) /
        monodromyPair φ z 1 0, 1] : PairVec38)) ∧
    (Matrix.mulVec (monodromyPair φ z)
        (![(ξm - monodromyPair φ z 1 1) /
          monodromyPair φ z 1 0, 1] : PairVec38) =
      ξm • (![(ξm - monodromyPair φ z 1 1) /
        monodromyPair φ z 1 0, 1] : PairVec38)) ∧
    ∀ t : Set.Icc (0 : ℝ) 1,
      Complex.I • gradDiscrim38 φ z (t : ℝ) =
        (-monodromyPair φ z 1 0) •
          starProd38
            (state φ z
              (![(ξp - monodromyPair φ z 1 1) /
                monodromyPair φ z 1 0, 1] : PairVec38) t)
            (state φ z
              (![(ξm - monodromyPair φ z 1 1) /
                monodromyPair φ z 1 0, 1] : PairVec38) t)

theorem floquet_gradient01_target : FloquetGradient01Target := by
  intro φ z p m hs hp hb
  exact ⟨floquet_eigenvector_algebra _ p m hs hp (monodromy_det_scalar φ z) hb,
    floquet_eigenvector_algebra _ m p (by rw [add_comm]; exact hs)
      (by rw [mul_comm]; exact hp) (monodromy_det_scalar φ z) hb,
    floquet_gradient01 φ z p m hs hp hb⟩

theorem floquet_gradient10_target : FloquetGradient10Target := by
  intro φ z p m hs hp hb
  exact ⟨floquet_eigenvector10_algebra _ p m hs hp (monodromy_det_scalar φ z) hb,
    floquet_eigenvector10_algebra _ m p (by rw [add_comm]; exact hs)
      (by rw [mul_comm]; exact hp) (monodromy_det_scalar φ z) hb,
    floquet_gradient10 φ z p m hs hp hb⟩


end
end NlsGge.GK38.GradEigen38
