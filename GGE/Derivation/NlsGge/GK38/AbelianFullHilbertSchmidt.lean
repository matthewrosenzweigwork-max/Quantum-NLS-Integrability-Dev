import NlsGge.GK38.AbelianFullRealSpace
import NlsGge.GK38.AbelianHilbertSchmidtCompact

/-! Actual full-Z row bound to genuine Hilbert-Schmidt membership. Finite
column energy is controlled before infinite real sums or HS membership. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38.P6OperatorBridge
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant

theorem matrix_row_bound_isHS
    (T : P6RealSpace38 →L[ℝ] P6RealSpace38) (e : ℤ → ℝ) (A : ℝ)
    (_hA : 0 ≤ A) (_he0 : ∀ m, 0 ≤ e m) (hes : Summable (fun m : ℤ => e m^2))
    (hbound : ∀ m r : ℤ,
      ‖T (lp.single 2 r (1 : ℝ)) m‖ ≤ A*e m*Lib.c3w m r) :
    IsHilbertSchmidt T ∧
    Summable (fun r : ℤ => ‖T (lp.single 2 r (1 : ℝ))‖^2) ∧
    (∑' r : ℤ, ‖T (lp.single 2 r (1 : ℝ))‖^2) ≤
      A^2*Lib.invSqSum*(∑' m : ℤ, e m^2) := by
  classical
  have hcol (r : ℤ) :
      HasSum (fun m : ℤ => ‖T (lp.single 2 r (1 : ℝ)) m‖^2)
        (‖T (lp.single 2 r (1 : ℝ))‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (T (lp.single 2 r (1 : ℝ)))
  have hfinite (S : Finset (ℤ)) :
      ∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ))‖^2 ≤
        A^2*Lib.invSqSum*(∑' m : ℤ, e m^2) := by
    have hfin : HasSum
        (fun m : ℤ => ∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ)) m‖^2)
        (∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ))‖^2) :=
      hasSum_sum (fun r _ => hcol r)
    have hpoint (m : ℤ) :
        ∑ r ∈ S, ‖T (lp.single 2 r (1 : ℝ)) m‖^2 ≤
          (A^2*Lib.invSqSum)*e m^2 := by
      have hws := Lib.summable_c3w_sq m
      have hwmass : (∑' r : ℤ, Lib.c3w m r^2) ≤ Lib.invSqSum :=
        le_of_eq (Lib.tsum_c3w_sq m)
      have hwfinite : (∑ r ∈ S, Lib.c3w m r^2) ≤ Lib.invSqSum :=
        (hws.sum_le_tsum S (fun _ _ => sq_nonneg _)).trans hwmass
      have hsq (r : ℤ) :
          ‖T (lp.single 2 r (1 : ℝ)) m‖^2 ≤ (A^2*e m^2)*Lib.c3w m r^2 := by
        have hh := mul_self_le_mul_self (norm_nonneg _) (hbound m r)
        nlinarith [hh]
      calc
        _ ≤ ∑ r ∈ S, (A^2*e m^2)*Lib.c3w m r^2 := Finset.sum_le_sum (fun r _ => hsq r)
        _ = (A^2*e m^2)*(∑ r ∈ S, Lib.c3w m r^2) := by rw [Finset.mul_sum]
        _ ≤ (A^2*e m^2)*Lib.invSqSum :=
          mul_le_mul_of_nonneg_left hwfinite (mul_nonneg (sq_nonneg A) (sq_nonneg _))
        _ = _ := by ring
    have hdom := hes.mul_left (A^2*Lib.invSqSum)
    have hb := hfin.summable.tsum_le_tsum hpoint hdom
    rw [hfin.tsum_eq,tsum_mul_left] at hb
    exact hb
  have hsum : Summable (fun r : ℤ => ‖T (lp.single 2 r (1 : ℝ))‖^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  have hmass : (∑' r : ℤ, ‖T (lp.single 2 r (1 : ℝ))‖^2) ≤
      A^2*Lib.invSqSum*(∑' m : ℤ, e m^2) :=
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite
  refine ⟨?_,hsum,hmass⟩
  apply isHilbertSchmidt_of_summable p6RealHilbertBasis38
  simpa only [p6RealHilbertBasis_apply38] using hsum

end
end NlsGge.GK38.P6OperatorBridge
