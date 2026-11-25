import Mathlib
import QuantumNLS.Local007Gauge

/-! LOCAL-020 stage S8a: the discriminant under conjugation, `Δ_{ū}(z) = Δ_u(-z)`.

`A_{ū}(z, x) = S A_u(-z, x) S` with `S = [[0,1],[1,0]]` (a.e. on the period), so `U_{ū}(z, ·) = S U_u(-z, ·) S`
by uniqueness of the integral equation (same argument as `Local007Gauge.transfer_neg`). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Matrix Interval
namespace QuantumNLS.Local020DiscC
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.SpatialTransfer (balCoef coef Mat2)
open QuantumNLS.L1SpatialTransfer QuantumNLS.L2SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

def Sm : Mat2 := !![0, 1; 1, 0]

theorem Sm_mul_Sm : Sm * Sm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sm, Matrix.mul_apply, Fin.sum_univ_two]

def Sc : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 Sm Sm

theorem Sc_apply (m : Mat2) : Sc m = Sm * m * Sm := rfl

theorem Sc_mul (a b : Mat2) : Sc (a * b) = Sc a * Sc b := by
  rw [Sc_apply, Sc_apply, Sc_apply]
  calc Sm * (a * b) * Sm = Sm * a * (Sm * Sm) * b * Sm := by rw [Sm_mul_Sm]; simp [mul_assoc]
    _ = Sm * a * Sm * (Sm * b * Sm) := by simp [mul_assoc]

theorem Sc_one : Sc 1 = 1 := by rw [Sc_apply]; simp [Sm_mul_Sm]

theorem trace_Sc (m : Mat2) : Matrix.trace (Sc m) = Matrix.trace m := by
  rw [Sc_apply]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Sm]
  simp; ring

theorem profile_star (u : L2T L) :
    (fun x : ℝ => L2SpatialTransfer.profile (star u) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)]
      fun x => conj (L2SpatialTransfer.profile u x) := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star u)
  simpa [L2SpatialTransfer.profile, Function.comp_def, zero_add] using h

theorem balCoef_star (κ : ℝ) (u : L2T L) (z : ℂ) :
    (fun x => balCoef κ (L2SpatialTransfer.profile (star u)) z x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)]
      fun x => Sc (balCoef κ (L2SpatialTransfer.profile u) (-z) x) := by
  filter_upwards [profile_star u] with x hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sc_apply, Sm, balCoef, coef, hx, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

open QuantumNLS.L2SpatialTransfer (spatialTransfer discriminant)

theorem transfer_star (κ : ℝ) (u : L2T L) (z : ℂ) :
    EqOn (spatialTransfer κ (star u) z) (fun x => Sc (spatialTransfer κ u (-z) x)) (Icc 0 L) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  let A := balCoef κ (L2SpatialTransfer.profile u) (-z)
  let A' := balCoef κ (L2SpatialTransfer.profile (star u)) z
  let U := spatialTransfer κ u (-z)
  let U' := spatialTransfer κ (star u) z
  have hi : IntervalIntegrable A' volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile (star u)) _ _ z
  have hiA : IntervalIntegrable A volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile u) _ _ (-z)
  have hc : ContinuousOn U (Icc 0 L) := continuousOn_transfer hL hiA
  have hc' : ContinuousOn U' (Icc 0 L) := continuousOn_transfer hL hi
  have hp : IntervalIntegrable (fun x => A x * U x) volume 0 L :=
    hiA.mul_continuousOn (by rw [uIcc_of_le hL]; exact hc)
  apply integral_solution_unique hL hi hc'
    (Sc.continuous.comp_continuousOn hc)
  · exact fun x hx => spatialTransfer_integral_eq κ (star u) z hx
  · intro x hx
    have hs : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]
      exact Icc_subset_Icc_right hx.2
    change Sc (U x) = 1 + ∫ s in (0 : ℝ)..x, A' s * Sc (U s)
    rw [show U x = 1 + ∫ s in (0 : ℝ)..x, A s * U s from
      spatialTransfer_integral_eq κ u (-z) hx, map_add, Sc_one]
    apply congrArg (fun y : Mat2 => 1 + y)
    calc
      Sc (∫ s in (0 : ℝ)..x, A s * U s) = ∫ s in (0 : ℝ)..x, Sc (A s * U s) :=
        (Sc.intervalIntegral_comp_comm (hp.mono_set hs)).symm
      _ = ∫ s in (0 : ℝ)..x, A' s * Sc (U s) := by
        have hae : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) x → Sc (A s * U s) = A' s * Sc (U s) := by
          have h1 : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) L), Sc (A s * U s) = A' s * Sc (U s) := by
            filter_upwards [balCoef_star κ u z] with s hs'
            rw [Sc_mul]
            exact congrArg (· * Sc (U s)) hs'.symm
          have h2 := (ae_restrict_iff' measurableSet_Ioc).1 h1
          filter_upwards [h2] with s hs2 hsI
          apply hs2
          rw [uIoc_of_le hx.1] at hsI
          exact ⟨hsI.1, hsI.2.trans hx.2⟩
        exact intervalIntegral.integral_congr_ae (by
          filter_upwards [hae] with s hs3 hs4 using hs3 hs4)

/-- **`Δ_{ū}(z) = Δ_u(-z)`.** -/
theorem disc_star (κ : ℝ) (u : L2T L) (z : ℂ) : discriminant κ (star u) z = discriminant κ u (-z) := by
  have h := transfer_star κ u z (show L ∈ Icc 0 L from ⟨(Fact.out : 0 < L).le, le_rfl⟩)
  unfold discriminant
  rw [h]
  exact trace_Sc _

end QuantumNLS.Local020DiscC

#print axioms QuantumNLS.Local020DiscC.disc_star
