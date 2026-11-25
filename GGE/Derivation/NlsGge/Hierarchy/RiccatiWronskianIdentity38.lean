import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false

/-! Formal Wronskian-type identity for the Riccati generating series
`Γ = Σ p_k z^k` and its reflected partner `Δ`: with `u = X(false,0)`,
`ū = X(true,0)`,
`(u Γ + ū Δ)(1 - Γ Δ) = D(Γ Δ)`.
All statements are over the polynomial ring `Poly` of jets. -/

namespace NlsGge.HierarchyRiccati.Core

/-- Swap of the `u`- and `ū`-jet variables. -/
noncomputable def riccatiSwap38 : Poly →+* Poly :=
  (MvPolynomial.rename (fun v : Jet => (!v.1, v.2))).toRingHom

/-- The generating series `Γ = Σ_k p_k z^k`. -/
noncomputable def riccatiGamma38 : PowerSeries Poly := PowerSeries.mk p

/-- The reflected series `Δ = Σ_k (-1)^k swap(p_k) z^k`. -/
noncomputable def riccatiDelta38 : PowerSeries Poly :=
  PowerSeries.mk (fun k => (-1 : Poly) ^ k * riccatiSwap38 (p k))

/-- Coefficientwise spatial derivative of a formal power series. -/
noncomputable def seriesD38 (f : PowerSeries Poly) : PowerSeries Poly :=
  PowerSeries.mk (fun k => spatialD (PowerSeries.coeff k f))

theorem riccatiSwap38_X (v : Jet) :
    riccatiSwap38 (MvPolynomial.X v) = MvPolynomial.X (!v.1, v.2) := by
  simp [riccatiSwap38]

theorem riccatiSwap38_C (a : ℤ) :
    riccatiSwap38 (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [riccatiSwap38]

theorem riccatiSwap38_spatialD (f : Poly) :
    riccatiSwap38 (spatialD f) = spatialD (riccatiSwap38 f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [riccatiSwap38_C, MvPolynomial.derivation_C]
    simp
  | add f g hf hg =>
    rw [map_add, map_add, map_add, map_add, hf, hg]
  | mul_X f v hf =>
    simp only [Derivation.leibniz, map_add, map_mul, smul_eq_mul, spatialD_jet,
      riccatiSwap38_X, hf]

theorem seriesD38_coeff (f : PowerSeries Poly) (k : ℕ) :
    PowerSeries.coeff k (seriesD38 f) = spatialD (PowerSeries.coeff k f) := by
  simp [seriesD38]

theorem seriesD38_add (f g : PowerSeries Poly) :
    seriesD38 (f + g) = seriesD38 f + seriesD38 g := by
  ext k
  simp [seriesD38_coeff]

theorem seriesD38_leibniz (f g : PowerSeries Poly) :
    seriesD38 (f * g) = seriesD38 f * g + f * seriesD38 g := by
  refine PowerSeries.ext fun n => ?_
  simp only [seriesD38_coeff, map_add, PowerSeries.coeff_mul]
  rw [map_sum spatialD, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem seriesD38_X_mul (f : PowerSeries Poly) :
    seriesD38 (PowerSeries.X * f) = PowerSeries.X * seriesD38 f := by
  ext n
  cases n with
  | zero => simp [seriesD38_coeff]
  | succ n => simp [seriesD38_coeff, PowerSeries.coeff_succ_X_mul]

/-- Coefficients of `Γ²` at index `k+1` are the attached convolution sums. -/
theorem riccatiGamma38_sq_coeff (k : ℕ) :
    PowerSeries.coeff (k + 1) (riccatiGamma38 * riccatiGamma38) =
      (Finset.Icc 1 k).attach.sum fun l => p (k + 1 - l.1) * p l.1 := by
  rw [PowerSeries.coeff_mul, Finset.sum_attach (Finset.Icc 1 k)
    (fun l => p (k + 1 - l) * p l)]
  simp only [riccatiGamma38, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p i * p j),
    Finset.sum_range_succ', Finset.sum_range_succ]
  have h0 : p 0 = 0 := by simp [p]
  have hIcc : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext x; simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.sub_self, h0, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, add_comm 1 i]

/-- The Riccati equation `Γ = -ū z + z DΓ + z u Γ²` for the generating series. -/
theorem riccatiGamma38_eq :
    riccatiGamma38 =
      -(PowerSeries.C (MvPolynomial.X (true, 0)) * PowerSeries.X) +
        PowerSeries.X * seriesD38 riccatiGamma38 +
        PowerSeries.X * (PowerSeries.C (MvPolynomial.X (false, 0)) *
          (riccatiGamma38 * riccatiGamma38)) := by
  refine PowerSeries.ext fun n => ?_
  have h0 : p 0 = 0 := by simp [p]
  rcases n with _ | _ | k
  · simp [riccatiGamma38, h0]
  · rw [map_add, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, seriesD38_coeff, map_neg, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_eq_constantCoeff]
    have h1 : PowerSeries.coeff 0 (riccatiGamma38 * riccatiGamma38) = 0 := by
      simp [riccatiGamma38, h0]
    have h2 : PowerSeries.coeff 0 riccatiGamma38 = 0 := by simp [riccatiGamma38, h0]
    simp [riccatiGamma38, p_one, h0, PowerSeries.coeff_X]
  · rw [map_add, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, riccatiGamma38_sq_coeff, seriesD38_coeff, map_neg,
      PowerSeries.coeff_C_mul]
    have h3 : PowerSeries.coeff (k + 1 + 1) (PowerSeries.X : PowerSeries Poly) = 0 := by
      simp [PowerSeries.coeff_X]
    rw [h3]
    simp [riccatiGamma38, p_recurrence]

/-- The ring homomorphism `Σ a_k z^k ↦ Σ (-1)^k swap(a_k) z^k`. -/
noncomputable def riccatiReflect38 : PowerSeries Poly →+* PowerSeries Poly :=
  (PowerSeries.rescale (-1 : Poly)).comp (PowerSeries.map riccatiSwap38)

theorem riccatiReflect38_coeff (f : PowerSeries Poly) (k : ℕ) :
    PowerSeries.coeff k (riccatiReflect38 f) =
      (-1 : Poly) ^ k * riccatiSwap38 (PowerSeries.coeff k f) := by
  simp [riccatiReflect38, PowerSeries.coeff_rescale, PowerSeries.coeff_map]

theorem riccatiReflect38_Gamma : riccatiReflect38 riccatiGamma38 = riccatiDelta38 := by
  refine PowerSeries.ext fun k => ?_
  simp [riccatiReflect38_coeff, riccatiGamma38, riccatiDelta38]

theorem riccatiReflect38_seriesD38 (f : PowerSeries Poly) :
    riccatiReflect38 (seriesD38 f) = seriesD38 (riccatiReflect38 f) := by
  refine PowerSeries.ext fun k => ?_
  rw [riccatiReflect38_coeff, seriesD38_coeff, seriesD38_coeff, riccatiReflect38_coeff,
    riccatiSwap38_spatialD]
  have h : spatialD ((-1 : Poly) ^ k * riccatiSwap38 (PowerSeries.coeff k f)) =
      (-1 : Poly) ^ k * spatialD (riccatiSwap38 (PowerSeries.coeff k f)) := by
    rw [Derivation.leibniz]
    have : spatialD ((-1 : Poly) ^ k) = 0 := by
      have : ((-1 : Poly) ^ k) = MvPolynomial.C ((-1 : ℤ) ^ k) := by simp
      rw [this, MvPolynomial.derivation_C]
    simp [this]
  rw [h]

theorem riccatiReflect38_X : riccatiReflect38 PowerSeries.X = -PowerSeries.X := by
  simp [riccatiReflect38]

theorem riccatiReflect38_C (a : Poly) :
    riccatiReflect38 (PowerSeries.C a) = PowerSeries.C (riccatiSwap38 a) := by
  refine PowerSeries.ext fun k => ?_
  rw [riccatiReflect38_coeff]
  rcases k with _ | k
  · simp
  · simp

/-- The reflected equation `Δ = u z - z DΔ - z ū Δ²`. -/
theorem riccatiDelta38_eq :
    riccatiDelta38 =
      PowerSeries.C (MvPolynomial.X (false, 0)) * PowerSeries.X -
        PowerSeries.X * seriesD38 riccatiDelta38 -
        PowerSeries.X * (PowerSeries.C (MvPolynomial.X (true, 0)) *
          (riccatiDelta38 * riccatiDelta38)) := by
  have h := congrArg riccatiReflect38 riccatiGamma38_eq
  simp only [map_add, map_neg, map_mul, riccatiReflect38_Gamma, riccatiReflect38_seriesD38,
    riccatiReflect38_X, riccatiReflect38_C, riccatiSwap38_X] at h
  simp only [Bool.not_true, Bool.not_false] at h
  linear_combination h

theorem riccatiWronskian38 :
    (PowerSeries.C (MvPolynomial.X (false, 0)) * riccatiGamma38 +
        PowerSeries.C (MvPolynomial.X (true, 0)) * riccatiDelta38) *
      (1 - riccatiGamma38 * riccatiDelta38) =
    seriesD38 (riccatiGamma38 * riccatiDelta38) := by
  apply PowerSeries.X_mul_cancel
  rw [seriesD38_leibniz]
  have hG := riccatiGamma38_eq
  have hD := riccatiDelta38_eq
  linear_combination (riccatiDelta38) * hG - riccatiGamma38 * hD

end NlsGge.HierarchyRiccati.Core
