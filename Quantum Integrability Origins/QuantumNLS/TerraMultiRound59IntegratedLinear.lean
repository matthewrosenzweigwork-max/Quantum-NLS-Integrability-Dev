import QuantumNLS.TerraMultiRound59FactorLinear

/-! Multilinearity survives differentiation in the shift and orthant integration. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound59IntegratedLinear
open QuantumNLS.TranslatedCorrelation QuantumNLS.CorrelationDerivatives
open QuantumNLS.TerraMultiRound59FactorLinear
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51TaylorCoeff

variable {L : ℝ} [Fact (0 < L)]

theorem derivative_update_add {m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (f : Fin (m + 2) → Hk L k) (i : Fin (m + 2)) (a b : Hk L k)
    (h : Fin (m + 2) → ℝ) (v : Fin d → (Fin (m + 2) → ℝ)) :
    iteratedFDeriv ℝ d (Cfun (Function.update f i (a + b))) h v =
    iteratedFDeriv ℝ d (Cfun (Function.update f i a)) h v +
    iteratedFDeriv ℝ d (Cfun (Function.update f i b)) h v := by
  have ha : ContDiff ℝ (d : ℕ) (Cfun (Function.update f i a)) :=
    (contDiff_Cfun hk _).of_le (by exact_mod_cast hd)
  have hb : ContDiff ℝ (d : ℕ) (Cfun (Function.update f i b)) :=
    (contDiff_Cfun hk _).of_le (by exact_mod_cast hd)
  have he : Cfun (Function.update f i (a + b)) =
      Cfun (Function.update f i a) + Cfun (Function.update f i b) := by
    funext x
    exact cfun_update_add hk f i a b x
  rw [he, iteratedFDeriv_add_apply ha.contDiffAt hb.contDiffAt]
  rfl

theorem derivative_update_smul {m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (f : Fin (m + 2) → Hk L k) (i : Fin (m + 2)) (c : ℂ) (a : Hk L k)
    (h : Fin (m + 2) → ℝ) (v : Fin d → (Fin (m + 2) → ℝ)) :
    iteratedFDeriv ℝ d (Cfun (Function.update f i (c • a))) h v =
    c * iteratedFDeriv ℝ d (Cfun (Function.update f i a)) h v := by
  have ha : ContDiff ℝ (d : ℕ) (Cfun (Function.update f i a)) :=
    (contDiff_Cfun hk _).of_le (by exact_mod_cast hd)
  have he : Cfun (Function.update f i (c • a)) = c • Cfun (Function.update f i a) := by
    funext x
    exact cfun_update_smul hk f i c a x
  rw [he, iteratedFDeriv_const_smul_apply ha.contDiffAt]
  rfl

theorem integrated_update_add {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (f : Fin (m + 2) → Hk L k) (i : Fin (m + 2)) (a b : Hk L k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    integratedCoeff (Cfun (Function.update f i (a + b))) paths d =
    integratedCoeff (Cfun (Function.update f i a)) paths d +
    integratedCoeff (Cfun (Function.update f i b)) paths d := by
  unfold integratedCoeff
  have he : (fun t : Fin n → ℝ => ((∏ j, Real.exp (-t j) : ℝ) : ℂ) *
      pathCoeff (Cfun (Function.update f i (a + b))) paths d t) =
    (fun t => ((∏ j, Real.exp (-t j) : ℝ) : ℂ) * pathCoeff (Cfun (Function.update f i a)) paths d t) +
    (fun t => ((∏ j, Real.exp (-t j) : ℝ) : ℂ) * pathCoeff (Cfun (Function.update f i b)) paths d t) := by
    funext t
    simp only [Pi.add_apply, pathCoeff, derivative_update_add hk hd, smul_add, mul_add]
  rw [he]
  exact integral_add (pathCoeff_integrable _ _ _) (pathCoeff_integrable _ _ _)

theorem integrated_update_smul {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (f : Fin (m + 2) → Hk L k) (i : Fin (m + 2)) (c : ℂ) (a : Hk L k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    integratedCoeff (Cfun (Function.update f i (c • a))) paths d =
    c * integratedCoeff (Cfun (Function.update f i a)) paths d := by
  unfold integratedCoeff
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [pathCoeff, derivative_update_smul hk hd, Complex.real_smul]
  ring

#print axioms derivative_update_add
#print axioms derivative_update_smul
#print axioms integrated_update_add
#print axioms integrated_update_smul
end QuantumNLS.TerraMultiRound59IntegratedLinear
