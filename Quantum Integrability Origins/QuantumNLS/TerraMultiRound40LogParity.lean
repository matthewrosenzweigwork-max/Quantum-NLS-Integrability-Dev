import QuantumNLS.TerraMultiRound39FieldBridge

/-! The periodic logarithm step in the printed signed-parity proof. This is a
conditional ODE lemma; it does not identify the signed Fourier fixed points. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate MeasureTheory
namespace QuantumNLS.TerraMultiRound40LogParity

/-- Two periodic Riccati solutions at opposite parameters yield opposite scalar
integrals, provided the product stays inside the logarithm disk. -/
theorem periodic_riccati_integrals (L Y κ : ℝ) (hκ : κ ≠ 0)
    (u r z : ℝ → ℂ) (hu : Continuous u)
    (hr : ∀ x, HasDerivAt r (u x - (Y : ℂ) * r x - (κ : ℂ) * conj (u x) * r x ^ 2) x)
    (hz : ∀ x, HasDerivAt z (conj (u x) + (Y : ℂ) * z x - (κ : ℂ) * u x * z x ^ 2) x)
    (hrp : r L = r 0) (hzp : z L = z 0)
    (hsmall : ∀ x, ‖(κ : ℂ) * r x * z x‖ < 1) :
    (∫ x in 0..L, conj (u x) * r x) = -(∫ x in 0..L, u x * z x) := by
  let w : ℝ → ℂ := fun x => 1 - (κ : ℂ) * r x * z x
  let q : ℝ → ℂ := fun x => u x * z x + conj (u x) * r x
  have hw (x : ℝ) : w x ∈ Complex.slitPlane := by
    have h := Complex.mem_slitPlane_of_norm_lt_one (z := -((κ : ℂ) * r x * z x)) (by simpa using hsmall x)
    simpa [w, sub_eq_add_neg] using h
  have hwn (x : ℝ) : w x ≠ 0 := fun h => Complex.zero_notMem_slitPlane (h ▸ hw x)
  have hd (x : ℝ) : HasDerivAt (fun t => Complex.log (w t)) (-(κ : ℂ) * q x) x := by
    have hprod := (hr x).mul (hz x)
    have hwd : HasDerivAt w (-(κ : ℂ) * q x * w x) x := by
      dsimp [w, q]
      convert (hasDerivAt_const x (1 : ℂ)).sub ((hprod.const_mul (κ : ℂ))) using 1
      · funext t; simp [Pi.mul_apply]; ring
      · ring
    have hc := hwd.clog_real (hw x)
    convert hc using 1
    rw [mul_div_cancel_right₀ _ (hwn x)]
  have hcontR : Continuous r := continuous_iff_continuousAt.mpr (fun x => (hr x).continuousAt)
  have hcontZ : Continuous z := continuous_iff_continuousAt.mpr (fun x => (hz x).continuousAt)
  have hc : Continuous q := by
    dsimp [q]
    exact (hu.mul hcontZ).add ((Complex.continuous_conj.comp hu).mul hcontR)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L)
    (fun x _ => hd x) ((continuous_const.mul hc).intervalIntegrable _ _)
  have he : w L = w 0 := by simp [w, hrp, hzp]
  have hzero : (∫ x in 0..L, -(κ : ℂ) * q x) = 0 := by
    rw [hi, he, sub_self]
  have hq : (∫ x in 0..L, q x) = 0 := by
    rw [intervalIntegral.integral_const_mul] at hzero
    have hk : (-(κ : ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hκ)
    exact (mul_eq_zero.mp hzero).resolve_left hk
  have hadd : (∫ x in 0..L, u x * z x) + (∫ x in 0..L, conj (u x) * r x) = 0 := by
    have h₁ : IntervalIntegrable (fun x => u x * z x) volume 0 L := (hu.mul hcontZ).intervalIntegrable 0 L
    have h₂ : IntervalIntegrable (fun x => conj (u x) * r x) volume 0 L := ((Complex.continuous_conj.comp hu).mul hcontR).intervalIntegrable 0 L
    have h := intervalIntegral.integral_add h₁ h₂
    change (∫ x in 0..L, u x * z x + conj (u x) * r x) = _ at h
    exact h.symm.trans hq
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hadd)

end QuantumNLS.TerraMultiRound40LogParity
#print axioms QuantumNLS.TerraMultiRound40LogParity.periodic_riccati_integrals
