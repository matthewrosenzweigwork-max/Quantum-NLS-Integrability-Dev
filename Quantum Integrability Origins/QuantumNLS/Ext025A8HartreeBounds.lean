import QuantumNLS.Ext025A8Hartree

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Ext025A8
open TensorCarrier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem multilinear_diagonal_lipschitz {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {n : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => H) F)
    {S : ℝ} (hS : 0 ≤ S) {u v : H} (hu : ‖u‖ ≤ S) (hv : ‖v‖ ≤ S) :
    ‖P (fun _ => u) - P (fun _ => v)‖ ≤
      ‖P‖ * n * S ^ (n - 1) * ‖u - v‖ := by
  have hpu : ‖(fun _ : Fin n => u)‖ ≤ S :=
    (pi_norm_le_iff_of_nonneg hS).mpr (fun _ => hu)
  have hpv : ‖(fun _ : Fin n => v)‖ ≤ S :=
    (pi_norm_le_iff_of_nonneg hS).mpr (fun _ => hv)
  have hpd : ‖(fun _ : Fin n => u) - (fun _ : Fin n => v)‖ ≤ ‖u - v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun _ => le_rfl)
  exact (P.norm_image_sub_le _ _).trans (by
    simp only [Fintype.card_fin]
    gcongr
    exact max_le hpu hpv)

theorem insertFirst_lipschitz (n : ℕ) {S : ℝ} (hS : 0 ≤ S)
    {u v : H} (hu : ‖u‖ ≤ S) (hv : ‖v‖ ≤ S) :
    ‖insertFirst n u - insertFirst n v‖ ≤ n * S ^ (n - 1) * ‖u - v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hn : ‖(tensorMultilinear (H := H) (n + 1)).curryLeft w‖ ≤ ‖w‖ := by
    have hh := (tensorMultilinear (H := H) (n + 1)).curryLeft.le_opNorm w
    rw [ContinuousMultilinearMap.curryLeft_norm] at hh
    exact hh.trans (mul_le_of_le_one_left (norm_nonneg _) (tensorMultilinear_norm (n + 1)))
  have h := multilinear_diagonal_lipschitz
    ((tensorMultilinear (H := H) (n + 1)).curryLeft w) hS hu hv
  change ‖(tensorMultilinear (n + 1)).curryLeft w (fun _ => u) -
    (tensorMultilinear (n + 1)).curryLeft w (fun _ => v)‖ ≤ _
  apply h.trans
  calc
    _ ≤ ‖w‖ * n * S ^ (n - 1) * ‖u - v‖ := by gcongr
    _ = _ := by ring

theorem tensorPower_lipschitz (n : ℕ) {S : ℝ} (hS : 0 ≤ S)
    {u v : H} (hu : ‖u‖ ≤ S) (hv : ‖v‖ ≤ S) :
    ‖(htpow n u : HilbertTensorPower ℂ H n) - htpow n v‖ ≤ n * S ^ (n - 1) * ‖u - v‖ := by
  have h := multilinear_diagonal_lipschitz (tensorMultilinear (H := H) n) hS hu hv
  apply h.trans
  calc
    _ ≤ 1 * n * S ^ (n - 1) * ‖u - v‖ := by
      gcongr; exact tensorMultilinear_norm n
    _ = _ := by ring

variable [CompleteSpace H]

theorem hartreeTerm_lipschitz (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (n : ℕ) {S : ℝ} (hS : 0 ≤ S) {u v : H} (hu : ‖u‖ ≤ S) (hv : ‖v‖ ≤ S) :
    ‖hartreeTerm A n u - hartreeTerm A n v‖ ≤
      (n + 1 : ℕ) * (2 * n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n) * ‖u - v‖ := by
  have hJv : ‖insertFirst n v‖ ≤ S ^ n := (insertFirst_norm n v).trans (by gcongr)
  have hP : ‖(htpow (n + 1) u : HilbertTensorPower ℂ H (n + 1))‖ ≤ S ^ (n + 1) := by rw [norm_htpow]; gcongr
  have hdJ := insertFirst_lipschitz n hS hu hv
  have hdP := tensorPower_lipschitz (n + 1) hS hu hv
  have he : hartreeContraction (A n) u u - hartreeContraction (A n) v v =
      ((insertFirst n u).adjoint - (insertFirst n v).adjoint) (A n (htpow (n + 1) u)) +
      (insertFirst n v).adjoint (A n (htpow (n + 1) u - htpow (n + 1) v)) := by
    simp only [hartreeContraction, ContinuousLinearMap.comp_apply, insertFirst_self,
      sub_apply, map_sub]
    abel
  have hb : ‖hartreeContraction (A n) u u - hartreeContraction (A n) v v‖ ≤
      (2 * n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n) * ‖u - v‖ := by
    rw [he]
    calc
      _ ≤ ‖((insertFirst n u).adjoint - (insertFirst n v).adjoint)
          (A n (htpow (n + 1) u))‖ +
          ‖(insertFirst n v).adjoint
            (A n (htpow (n + 1) u - htpow (n + 1) v))‖ := norm_add_le _ _
      _ ≤ ‖(insertFirst n u).adjoint - (insertFirst n v).adjoint‖ *
          (‖A n‖ * ‖htpow (n + 1) u‖) +
          ‖(insertFirst n v).adjoint‖ *
            (‖A n‖ * ‖htpow (n + 1) u - htpow (n + 1) v‖) := by
        apply add_le_add
        · exact (((insertFirst n u).adjoint - (insertFirst n v).adjoint).le_opNorm
            (A n (htpow (n + 1) u))).trans
            (mul_le_mul_of_nonneg_left ((A n).le_opNorm (htpow (n + 1) u)) (norm_nonneg _))
        · exact ((insertFirst n v).adjoint.le_opNorm
            (A n (htpow (n + 1) u - htpow (n + 1) v))).trans
            (mul_le_mul_of_nonneg_left
              ((A n).le_opNorm (htpow (n + 1) u - htpow (n + 1) v)) (norm_nonneg _))
      _ ≤ (n * S ^ (n - 1) * ‖u - v‖) * (‖A n‖ * S ^ (n + 1)) +
          S ^ n * (‖A n‖ * ((n + 1 : ℕ) * S ^ n * ‖u - v‖)) := by
        rw [← map_sub ContinuousLinearMap.adjoint,
          ContinuousLinearMap.adjoint.norm_map, ContinuousLinearMap.adjoint.norm_map]
        simp only [Nat.add_sub_cancel] at hdP
        gcongr
      _ = _ := by
        by_cases hn : n = 0
        · subst n; simp
        · have hp : n - 1 + (n + 1) = 2 * n := by omega
          have hpow : S ^ (n - 1) * S ^ (n + 1) = S ^ (2 * n) := by
            rw [← pow_add, hp]
          have hpow' : S ^ n * S ^ n = S ^ (2 * n) := by rw [← pow_add]; congr 1; omega
          calc
            _ = ((n : ℝ) * (S ^ (n - 1) * S ^ (n + 1)) +
                (n + 1 : ℕ) * (S ^ n * S ^ n)) * ‖A n‖ * ‖u - v‖ := by ring
            _ = _ := by rw [hpow, hpow']; push_cast; ring
  calc
    _ = (n + 1 : ℕ) * ‖hartreeContraction (A n) u u - hartreeContraction (A n) v v‖ := by
      rw [hartreeTerm, hartreeTerm, ← smul_sub, norm_smul, Complex.norm_natCast]
    _ ≤ (n + 1 : ℕ) * ((2 * n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n) * ‖u - v‖) := by
      gcongr
    _ = _ := by ring
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.multilinear_diagonal_lipschitz
#print axioms QuantumNLS.Ext025A8.insertFirst_lipschitz
#print axioms QuantumNLS.Ext025A8.tensorPower_lipschitz
#print axioms QuantumNLS.Ext025A8.hartreeTerm_lipschitz
