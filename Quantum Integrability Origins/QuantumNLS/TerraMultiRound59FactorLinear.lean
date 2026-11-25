import QuantumNLS.CorrelationDerivatives
import QuantumNLS.TerraMultiRound51TaylorIntegral

/-! Factor-slot linearity of the correlation and its integrated Taylor coefficients. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound59FactorLinear
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.CorrelationDerivatives
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51TaylorCoeff

variable {L : ℝ} [Fact (0 < L)]

theorem contRep_add {k : ℕ} (hk : 1 ≤ k) (a b : Hk L k) :
    contRep hk (a + b) = contRep hk a + contRep hk b := by
  simp [contRep, toF1]

theorem contRep_smul {k : ℕ} (hk : 1 ≤ k) (c : ℂ) (a : Hk L k) :
    contRep hk (c • a) = c • contRep hk a := by
  simp [contRep, toF1]

theorem cfun_update_add {q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (i : Fin q) (a b : Hk L k) (h : Fin q → ℝ) :
    Cfun (Function.update f i (a + b)) h =
      Cfun (Function.update f i a) h + Cfun (Function.update f i b) h := by
  classical
  simp_rw [Cfun_eq_cont hk]
  let F : Hk L k → AddCircle L → ℂ := fun a x =>
    ∏ j, contRep hk ((Function.update f i a) j) (x + ((h j : ℝ) : AddCircle L))
  have hcont : ∀ a, Continuous (F a) := by
    intro a
    apply continuous_finset_prod
    intro j hj
    exact (contRep hk ((Function.update f i a) j)).continuous.comp
      (continuous_id.add continuous_const)
  have hsum : F (a + b) = F a + F b := by
    funext x
    dsimp [F]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self, contRep_add, ContinuousMap.add_apply, add_mul]
    congr 1 <;> congr 1 <;> apply Finset.prod_congr rfl <;> intro j hj <;>
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  change (∫ x, F (a + b) x) = (∫ x, F a x) + ∫ x, F b x
  rw [hsum]
  exact integral_add ((hcont a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hcont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))


theorem cfun_update_smul {q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (i : Fin q) (c : ℂ) (a : Hk L k) (h : Fin q → ℝ) :
    Cfun (Function.update f i (c • a)) h = c * Cfun (Function.update f i a) h := by
  classical
  simp_rw [Cfun_eq_cont hk]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, contRep_smul, ContinuousMap.smul_apply, smul_eq_mul]
  have hp : (∏ j ∈ Finset.univ.erase i,
      contRep hk ((Function.update f i (c • a)) j) (x + ((h j : ℝ) : AddCircle L))) =
      ∏ j ∈ Finset.univ.erase i,
      contRep hk ((Function.update f i a) j) (x + ((h j : ℝ) : AddCircle L)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp]
  ring

#print axioms contRep_add
#print axioms contRep_smul
#print axioms cfun_update_add
#print axioms cfun_update_smul
end QuantumNLS.TerraMultiRound59FactorLinear
