import QuantumNLS.TerraMultiRound48Orthant
import QuantumNLS.TranslatedCorrelation

/-! Concrete product integrability and Fubini for finite shifted Sobolev
correlations, with shifts indexed by arbitrary finite paths. This does not
identify the resulting integral with the recursively defined tree term. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set AddCircle
namespace QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)]

def pathShift {n q : ℕ} (paths : Fin q → Finset (Fin n)) (Y : ℝ)
    (t : Fin n → ℝ) (j : Fin q) : ℝ :=
  -(∑ i ∈ paths j, t i) / Y

theorem pathShift_continuous {n q : ℕ} (paths : Fin q → Finset (Fin n)) (Y : ℝ) :
    Continuous (pathShift paths Y) := by
  apply continuous_pi
  intro j
  exact ((continuous_finsetSum _ (fun i _ => continuous_apply i)).neg).div_const Y

def treeIntegrand {n q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (paths : Fin q → Finset (Fin n)) (Y : ℝ)
    (p : (Fin n → ℝ) × AddCircle L) : ℂ :=
  ((∏ i, Real.exp (-p.1 i) : ℝ) : ℂ) *
    ∏ j, contRep hk (f j) (p.2 + ((pathShift paths Y p.1 j : ℝ) : AddCircle L))

/-- The joint integrand on the orthant and the spatial torus is integrable,
proved from the Sobolev embedding and the integrable exponential product. -/
theorem tree_integrable {n q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (paths : Fin q → Finset (Fin n)) (Y : ℝ) :
    Integrable (treeIntegrand hk f paths Y)
      ((Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))).prod
        (volume : Measure (AddCircle L))) := by
  let B : ℝ := ∏ j, (cL L * ‖f j‖)
  have hg := ((TerraMultiRound48Orthant.orthant_exp_integrable n).const_mul B).comp_fst
    (volume : Measure (AddCircle L))
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    unfold treeIntegrand
    apply Continuous.mul
    · apply Complex.continuous_ofReal.comp
      exact continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp
        (((continuous_apply i).comp continuous_fst).neg))
    · apply continuous_finsetProd
      intro j hj
      apply (contRep hk (f j)).continuous.comp
      have hc : Continuous (fun z : ℝ => (z : AddCircle L)) := by fun_prop
      exact continuous_snd.add (hc.comp (((continuous_apply j).comp
        (pathShift_continuous paths Y)).comp continuous_fst))
  · filter_upwards with p
    have hp : 0 ≤ ∏ i : Fin n, Real.exp (-p.1 i) :=
      Finset.prod_nonneg (fun i hi => (Real.exp_pos _).le)
    have hprod : ‖∏ j, contRep hk (f j)
        (p.2 + ((pathShift paths Y p.1 j : ℝ) : AddCircle L))‖ ≤ B := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => norm_contRep_apply_le hk (f j) _)
    simp only [treeIntegrand, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    calc
      _ ≤ (∏ i : Fin n, Real.exp (-p.1 i)) * B := mul_le_mul_of_nonneg_left hprod hp
      _ = _ := mul_comm _ _

/-- Fubini identifies the spatial integral of the joint integrand with the
exponentially weighted actual translated correlation. -/
theorem tree_fubini {n q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (paths : Fin q → Finset (Fin n)) (Y : ℝ) :
    (∫ p, treeIntegrand hk f paths Y p ∂
      ((Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))).prod
        (volume : Measure (AddCircle L)))) =
    ∫ t, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * Cfun f (pathShift paths Y t) ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integral_prod _ (tree_integrable hk f paths Y)]
  apply integral_congr_ae
  filter_upwards with t
  rw [Cfun_eq_cont hk f]
  simp only [treeIntegrand, integral_const_mul]

#print axioms pathShift_continuous
#print axioms tree_integrable
#print axioms tree_fubini
end QuantumNLS.TerraMultiRound48TreeFubini
