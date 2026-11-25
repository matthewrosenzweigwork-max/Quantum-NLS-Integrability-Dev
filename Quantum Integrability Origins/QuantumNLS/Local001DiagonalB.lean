import QuantumNLS.Local001ModesB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

theorem resolvent_mode (hL : 0 < L) (κ : ℝ) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    {R : VectorInterval L →L[ℂ] VectorInterval L}
    (hR : LocalSpectral.IsResolvent L κ (fun _ => 0) (LocalSpectral.parity n) z R)
    (j : Fin 2) (k : ℤ) :
    R (vectorModeBasis L n (j, k)) =
      (z - (LocalSpectral.pm L (sourceMode n (j, k)) : ℂ))⁻¹ •
        vectorModeBasis L n (j, k) := by
  let m := sourceMode n (j, k)
  have hpm : LocalSpectral.parity m = LocalSpectral.parity n := by
    simpa [m] using sourceMode_parity n (j, k)
  have heig := LocalSpectral.free_eigen hL κ m j
  rw [hpm] at heig
  have hchi : vectorModeBasis L n (j, k) = LocalSpectral.chi L m j := by
    fin_cases j
    · simpa [m, sourceMode, sourceModeIndex] using
        (vectorModeBasis_eq_chi L n (0 : Fin 2) (-k))
    · simpa [m, sourceMode, sourceModeIndex] using
        (vectorModeBasis_eq_chi L n (1 : Fin 2) k)
  have hleft := hR.2
    (LocalSpectral.chi L m j, (LocalSpectral.pm L m : ℂ) • LocalSpectral.chi L m j) heig
  have hmul : (z - (LocalSpectral.pm L m : ℂ)) • R (LocalSpectral.chi L m j) =
      LocalSpectral.chi L m j := by
    have harg : z • LocalSpectral.chi L m j -
        (LocalSpectral.pm L m : ℂ) • LocalSpectral.chi L m j =
        (z - (LocalSpectral.pm L m : ℂ)) • LocalSpectral.chi L m j := by
      rw [sub_smul]
    rw [harg, map_smul] at hleft
    exact hleft
  have hneq : z - (LocalSpectral.pm L m : ℂ) ≠ 0 := by
    intro heq
    have heq' : z = (LocalSpectral.pm L m : ℂ) := sub_eq_zero.mp heq
    have hcontour := contour_ne_free_mode hL hr hsmall hz hpm
    exact hcontour heq'
  have hsolution := congrArg
      (fun v : VectorInterval L => (z - (LocalSpectral.pm L m : ℂ))⁻¹ • v) hmul
  have hvalue : (z - (LocalSpectral.pm L m : ℂ))⁻¹ *
      (z - (LocalSpectral.pm L m : ℂ)) = 1 := inv_mul_cancel₀ hneq
  have hresult : R (LocalSpectral.chi L m j) =
      (z - (LocalSpectral.pm L m : ℂ))⁻¹ • LocalSpectral.chi L m j := by
    calc
      R (LocalSpectral.chi L m j) =
          (z - (LocalSpectral.pm L m : ℂ))⁻¹ •
            ((z - (LocalSpectral.pm L m : ℂ)) • R (LocalSpectral.chi L m j)) := by
              rw [smul_smul, hvalue, one_smul]
      _ = (z - (LocalSpectral.pm L m : ℂ))⁻¹ • LocalSpectral.chi L m j := by rw [hmul]
  rw [← hchi] at hresult
  simpa [m, sourceMode, sourceModeIndex] using hresult


#print axioms resolvent_mode

def freeResolventMultiplier (n : ℤ) (z : ℂ) (i : Fin 2 × ℤ) : ℂ :=
  (z - (LocalSpectral.pm L (sourceMode n i : ℤ) : ℂ))⁻¹


#print axioms freeResolventMultiplier

theorem freeResolventMultiplier_norm_le (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ} (hr : 0 < r)
    (hsmall : r < spacing L / 2) (hz : OnGamma L r n z) (i : Fin 2 × ℤ) :
    ‖freeResolventMultiplier L n z i‖ ≤ r⁻¹ := by
  have hden := contour_denominator_lower hL hsmall hz (sourceMode_parity n i)
  have hdenpos : 0 < ‖z - (LocalSpectral.pm L (sourceMode n i : ℤ) : ℂ)‖ :=
    lt_of_lt_of_le hr hden
  rw [freeResolventMultiplier, norm_inv]
  exact (inv_le_inv₀ hdenpos hr).2 hden


#print axioms freeResolventMultiplier_norm_le

noncomputable def freeDiagonalResolvent (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z) :
    VectorInterval L →L[ℂ] VectorInterval L :=
  Classical.choose (QuantumNLS.HilbertDiagOp.diag_exists (vectorModeBasis L n)
    (freeResolventMultiplier L n z) r⁻¹
    (freeResolventMultiplier_norm_le L hL n hr hsmall hz) (inv_nonneg.mpr hr.le))

#print axioms freeDiagonalResolvent

theorem freeDiagonalResolvent_spec (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z) :
    (∀ (i : Fin 2 × ℤ) (f : VectorInterval L),
      ⟪vectorModeBasis L n i, freeDiagonalResolvent L hL n hr hsmall hz f⟫_ℂ =
      freeResolventMultiplier L n z i * ⟪vectorModeBasis L n i, f⟫_ℂ) ∧
      ‖freeDiagonalResolvent L hL n hr hsmall hz‖ ≤ r⁻¹ := by
  exact Classical.choose_spec (QuantumNLS.HilbertDiagOp.diag_exists (vectorModeBasis L n)
    (freeResolventMultiplier L n z) r⁻¹
    (freeResolventMultiplier_norm_le L hL n hr hsmall hz) (inv_nonneg.mpr hr.le))

#print axioms freeDiagonalResolvent_spec

theorem freeDiagonalResolvent_inner (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    (i : Fin 2 × ℤ) (f : VectorInterval L) :
    ⟪vectorModeBasis L n i, freeDiagonalResolvent L hL n hr hsmall hz f⟫_ℂ =
      freeResolventMultiplier L n z i * ⟪vectorModeBasis L n i, f⟫_ℂ :=
  (freeDiagonalResolvent_spec L hL n hr hsmall hz).1 i f

#print axioms freeDiagonalResolvent_inner

theorem freeDiagonalResolvent_norm_le (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z) :
    ‖freeDiagonalResolvent L hL n hr hsmall hz‖ ≤ r⁻¹ :=
  (freeDiagonalResolvent_spec L hL n hr hsmall hz).2


#print axioms freeDiagonalResolvent_norm_le

theorem vectorModeBasis_inner_component (n : ℤ) (j : Fin 2) (k : ℤ)
    (f : VectorInterval L) :
    ⟪vectorModeBasis L n (j, k), f⟫_ℂ =
      ⟪intervalShiftedBasis L (componentShift n j) k,
        vectorToComponentsLinear L f j⟫_ℂ := by
  rw [vectorModeBasis_apply]
  rw [← vectorToComponents_inner L (intervalFiberInsert L j
    (intervalShiftedBasis L (componentShift n j) k)) f]
  fin_cases j <;> simp [PiLp.inner_apply, component_intervalFiberInsert]


#print axioms vectorModeBasis_inner_component

theorem sourceResolvent_eq_freeDiagonal (hL : 0 < L) (κ : ℝ) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    {R : VectorInterval L →L[ℂ] VectorInterval L}
    (hR : LocalSpectral.IsResolvent L κ (fun _ => 0) (LocalSpectral.parity n) z R) :
    R = freeDiagonalResolvent L hL n hr hsmall hz := by
  apply ContinuousLinearMap.ext
  intro f
  apply (vectorModeBasis L n).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    QuantumNLS.HilbertDiagOp.eig_coeff (vectorModeBasis L n) R
      (freeResolventMultiplier L n z) (by
        rintro ⟨j, k⟩
        exact resolvent_mode L hL κ n hr hsmall hz hR j k) i,
    freeDiagonalResolvent_inner L hL n hr hsmall hz]




#print axioms sourceResolvent_eq_freeDiagonal

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
