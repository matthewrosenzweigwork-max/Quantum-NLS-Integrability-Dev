import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open PowerSeries

/-- Coefficientwise extension of a derivation to power series. -/
noncomputable def serD {R : Type*} [CommRing R] (d : Derivation ℤ R R) (F : PowerSeries R) :
    PowerSeries R :=
  PowerSeries.mk (fun k => d (PowerSeries.coeff k F))

theorem coeff_serD {R : Type*} [CommRing R] (d : Derivation ℤ R R) (F : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (serD d F) = d (PowerSeries.coeff k F) := by
  simp [serD, PowerSeries.coeff_mk]

theorem serD_mul {R : Type*} [CommRing R] (d : Derivation ℤ R R) (F G : PowerSeries R) :
    serD d (F * G) = serD d F * G + F * serD d G := by
  ext n
  rw [coeff_serD, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Derivation.leibniz, coeff_serD, coeff_serD, smul_eq_mul, smul_eq_mul]
  ring

theorem serD_pow_succ {R : Type*} [CommRing R] (d : Derivation ℤ R R) (P : PowerSeries R)
    (m : ℕ) : serD d (P ^ (m + 1)) = (m + 1) • (P ^ m * serD d P) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ P (m + 1), serD_mul, ih]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_zero_serD {R : Type*} [CommRing R] (d : Derivation ℤ R R) (P : PowerSeries R)
    (hP : PowerSeries.constantCoeff P = 0) :
    PowerSeries.constantCoeff (serD d P) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_serD,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hP, map_zero]

theorem coeff_eq_sum_formalLog38 {R : Type*} [CommRing R] (d : Derivation ℤ R R)
    (A P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 0)
    (h : A * (1 - P) = serD d P) (k : ℕ) :
    PowerSeries.coeff k A =
      ∑ j ∈ Finset.range k, PowerSeries.coeff k (P ^ j * serD d P) := by
  have hXP : (PowerSeries.X : PowerSeries R) ∣ P := PowerSeries.X_dvd_iff.mpr hP
  have hXD : (PowerSeries.X : PowerSeries R) ∣ serD d P :=
    PowerSeries.X_dvd_iff.mpr (coeff_zero_serD d P hP)
  have h1 : A * (1 - P ^ (k + 1)) = serD d P * ∑ j ∈ Finset.range (k + 1), P ^ j := by
    rw [← mul_neg_geom_sum, ← mul_assoc, h]
  have h2 : PowerSeries.coeff k (A * P ^ (k + 1)) = 0 := by
    have : (PowerSeries.X : PowerSeries R) ^ (k + 1) ∣ A * P ^ (k + 1) :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hXP _) A
    exact PowerSeries.X_pow_dvd_iff.mp this k (Nat.lt_succ_self k)
  have h3 : PowerSeries.coeff k (P ^ k * serD d P) = 0 := by
    have : (PowerSeries.X : PowerSeries R) ^ (k + 1) ∣ P ^ k * serD d P := by
      rw [pow_succ]
      exact mul_dvd_mul (pow_dvd_pow_of_dvd hXP _) hXD
    exact PowerSeries.X_pow_dvd_iff.mp this k (Nat.lt_succ_self k)
  have h4 := congrArg (PowerSeries.coeff k) h1
  rw [mul_sub, mul_one, map_sub, h2, sub_zero, Finset.mul_sum, map_sum,
    Finset.sum_range_succ] at h4
  simp only [mul_comm (serD d P)] at h4
  rw [h3, add_zero] at h4
  exact h4

theorem formalLog_exact38 {R : Type*} [CommRing R] (d : Derivation ℤ R R) (A P : PowerSeries R)
    (hP : PowerSeries.constantCoeff P = 0)
    (h : A * (1 - P) = PowerSeries.mk (fun k => d (PowerSeries.coeff k P))) (k : ℕ) :
    ∃ ℓ : R, (k.factorial : R) * PowerSeries.coeff k A = d ℓ := by
  have h' : A * (1 - P) = serD d P := h
  refine ⟨∑ j ∈ Finset.range k,
    ((k.factorial / (j + 1) : ℕ) : R) * PowerSeries.coeff k (P ^ (j + 1)), ?_⟩
  rw [coeff_eq_sum_formalLog38 d A P hP h' k, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hdvd : (j + 1) ∣ k.factorial := Nat.dvd_factorial (Nat.succ_pos j) hjk
  have hc : PowerSeries.coeff k (serD d (P ^ (j + 1))) =
      ((j + 1 : ℕ) : R) * PowerSeries.coeff k (P ^ j * serD d P) := by
    rw [serD_pow_succ, map_nsmul, nsmul_eq_mul]
  rw [coeff_serD] at hc
  have hk : (k.factorial : R) = ((k.factorial / (j + 1) : ℕ) : R) * ((j + 1 : ℕ) : R) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  rw [hk, mul_assoc, ← hc]
  have : ((k.factorial / (j + 1) : ℕ) : R) * d (PowerSeries.coeff k (P ^ (j + 1))) =
      d (((k.factorial / (j + 1) : ℕ) : R) * PowerSeries.coeff k (P ^ (j + 1))) := by
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]
  rw [this]


end NlsGge.HierarchyRiccati.Core
