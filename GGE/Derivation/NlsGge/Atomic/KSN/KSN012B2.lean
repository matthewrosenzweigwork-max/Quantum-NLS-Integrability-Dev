import Mathlib
import NlsGge.Atomic.KSN.KSN012Host

/- KSN012B2 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN012B2.lean.
   Supporting bridge B2 of proof development/KSN012_STOP.md (statement verbatim): `Continuous (pairPotential 1 (by norm_num))`.
   Route (as in the STOP file): x ↦ ⟨rawCoefficient 1 x b, _⟩ is additive in x with ‖·‖ ≤ ‖x‖ (scaleWeight ≥ 1,
   restriction to one Boolean fibre), hence 1-Lipschitz; physicalFourierL2.symm is a linear isometric equivalence,
   hence continuous; the pair is continuous componentwise. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- The ℓ² coefficient vector of one Boolean component (the argument of `physicalFourierL2.symm` in `pairPotential`). -/
def KSN012B2_rawL2 (b : Bool) (x : PairScale 1) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨rawCoefficient 1 x b, rawCoefficient_mem 1 (by norm_num) x b⟩

theorem KSN012B2_rawL2_norm_le (b : Bool) (x : PairScale 1) : ‖KSN012B2_rawL2 b x‖ ≤ ‖x‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_forall_sum_le hp (norm_nonneg _) (fun s => ?_)
  have hw : ∀ n : ℤ, ‖rawCoefficient 1 x b n‖ ≤ ‖x (b, n)‖ := by
    intro n
    have hw1 : 1 ≤ scaleWeight 1 n := by
      unfold scaleWeight bracket
      rw [Real.rpow_one]
      exact le_max_left _ _
    unfold rawCoefficient
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hw1
  calc ∑ n ∈ s, ‖KSN012B2_rawL2 b x n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑ n ∈ s, ‖x (b, n)‖ ^ (2 : ℝ≥0∞).toReal := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        exact Real.rpow_le_rpow (norm_nonneg _) (hw n) hp.le
    _ = ∑ j ∈ s.map ⟨Prod.mk b, Prod.mk_right_injective b⟩, ‖x j‖ ^ (2 : ℝ≥0∞).toReal := by
        rw [Finset.sum_map]
        rfl
    _ ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal := lp.sum_rpow_le_norm_rpow hp x _

theorem KSN012B2_rawL2_sub (b : Bool) (x y : PairScale 1) :
    KSN012B2_rawL2 b x - KSN012B2_rawL2 b y = KSN012B2_rawL2 b (x - y) := by
  ext n
  simp only [KSN012B2_rawL2, lp.coeFn_sub, Pi.sub_apply, rawCoefficient]
  rw [sub_div]

theorem KSN012B2_rawL2_continuous (b : Bool) : Continuous (KSN012B2_rawL2 b) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, KSN012B2_rawL2_sub, NNReal.coe_one, one_mul]
  exact KSN012B2_rawL2_norm_le b (x - y)

theorem KSN012B2_main : Continuous (pairPotential 1 (by norm_num)) := by
  have h1 := physicalFourierL2.symm.continuous.comp (KSN012B2_rawL2_continuous true)
  have h2 := physicalFourierL2.symm.continuous.comp (KSN012B2_rawL2_continuous false)
  exact h1.prodMk h2

end
end NlsGge.ThirdConsultation.KSN
