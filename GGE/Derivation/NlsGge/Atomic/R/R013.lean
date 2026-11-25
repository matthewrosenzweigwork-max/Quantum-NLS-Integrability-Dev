/- R-013 PRODUCTION01 (proof development kit; source proof development/R013_PROOF04.lean.txt, author proof development; reviewer proof development).
   Target NlsGge/Atomic/R/R013.lean, module NlsGge.Atomic.R.R013. Bindings H, E_s, inclE, IsHilbertSchmidt per Pro. -/
import NlsGge.Ramer.RamerStep8a
import NlsGge.Analysis.RegularizedDeterminant.RealHilbertSchmidt

/- R-013 PROOF01 (proof development, AUTHOR; not self-reviewed). Heads and bindings from defs3 followup PRO_DEFINITION_RESPONSE_FP80_01.md
   section "R-013 — one inclusion, the house HS predicate, and the factor-two CM norm". H = ActualCM c, E_s = FullWeightedHilbert c s,
   inclE = NlsGge.Ramer.inclE, IsHilbertSchmidt = NlsGge.Analysis.RegularizedDeterminant.IsHilbertSchmidt (energy ≠ ∞). The norm
   of HilbertSchmidt is the Hilbert-Schmidt norm (its columns in ℓ²), so ‖inclEHS c s hs‖ ^ 2 is the HS square sum.
   Normalization: production actualCM_norm_sq with cmModeWeight = 2 * sourceRate (CMWeightComparison.lean:11) gives ‖h‖² = 2 Σ a|h_n|². -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.ThirdConsultation.R.BindingR013

abbrev H {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) :=
  NlsGge.Ramer.ActualCM c

abbrev E_s {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :=
  NlsGge.Pilot.FullWeightedHilbert c s

abbrev inclE {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) : H c →L[ℝ] E_s c s :=
  NlsGge.Ramer.inclE c s hs

def inclEHS {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    NlsGge.Analysis.RegularizedDeterminant.HilbertSchmidt (H c) (E_s c s) :=
  NlsGge.Analysis.RegularizedDeterminant.HilbertSchmidt.ofCLM
    (inclE c s hs)
    (NlsGge.Analysis.RegularizedDeterminant.isHilbertSchmidt_of_summable
      (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c))
      (NlsGge.Pilot.cmToFullWeightedHilbert_basis_square_summable c s hs))

theorem inclE_norm_eq
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (x : H c) :
    ‖inclE c s hs x‖ =
      ‖NlsGge.Pilot.cmToFullWeightedHilbert c s (le_of_lt (by linarith : (0 : ℝ) < s)) x‖ :=
  rfl

theorem inclE_basis_summand_eq
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (p : ℤ × Fin 2) :
    ‖inclE c s hs (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2 =
      ‖NlsGge.Pilot.cmToFullWeightedHilbert c s (le_of_lt (by linarith : (0 : ℝ) < s))
        (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2 :=
  rfl

theorem inclE_energy_eq
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    NlsGge.Analysis.RegularizedDeterminant.energy (inclE c s hs) =
      ENNReal.ofReal (∑' n : ℤ, Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) := by
  have hsq : Summable (fun p : ℤ × Fin 2 =>
      ‖inclE c s hs (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2) := by
    simp only [inclE_basis_summand_eq]
    exact NlsGge.Pilot.cmToFullWeightedHilbert_basis_square_summable c s hs
  have h1 : NlsGge.Analysis.RegularizedDeterminant.energy (inclE c s hs) =
      ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖inclE c s hs
        (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2) :=
    NlsGge.Analysis.RegularizedDeterminant.energy_eq_basis (inclE c s hs)
      (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c))
  have h2 : (∑' p : ℤ × Fin 2, ENNReal.ofReal (‖inclE c s hs
        (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2)) =
      ENNReal.ofReal (∑' p : ℤ × Fin 2, ‖inclE c s hs
        (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hsq).symm
  have h3 : (∑' p : ℤ × Fin 2, ‖inclE c s hs
        (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c) p)‖ ^ 2) =
      ∑' n : ℤ, Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
    simp only [inclE_basis_summand_eq]
    exact (NlsGge.Pilot.cmToFullWeightedHilbert_basis_square_sum c s hs).tsum_eq
  rw [h1, h2, h3]

theorem cm_inclusion_hs
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    NlsGge.Analysis.RegularizedDeterminant.IsHilbertSchmidt (inclE c s hs) :=
  NlsGge.Analysis.RegularizedDeterminant.isHilbertSchmidt_of_summable
    (NlsGge.Pilot.weightedRealHilbertBasis (NlsGge.Pilot.cmModeWeight c))
    (NlsGge.Pilot.cmToFullWeightedHilbert_basis_square_summable c s hs)

theorem cm_inclusion_full_contract
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    Function.Injective (inclE c s hs) ∧
    DenseRange (inclE c s hs) ∧
    NlsGge.Analysis.RegularizedDeterminant.IsHilbertSchmidt (inclE c s hs) ∧
    Summable (fun n : ℤ =>
      Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) ∧
    ‖inclEHS c s hs‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
  have hsumm : Summable (fun n : ℤ =>
      Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) := by
    have h := NlsGge.Measure.summable_japaneseBracket_rpow_neg (2 * s) (by linarith)
    simpa only [neg_mul] using h
  have hS0 : 0 ≤ ∑' n : ℤ, Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
    rw [← (NlsGge.Pilot.cmToFullWeightedHilbert_basis_square_sum c s hs).tsum_eq]
    exact tsum_nonneg (fun p => sq_nonneg _)
  refine ⟨NlsGge.Ramer.cmToFullWeightedHilbert_injective c s ((le_of_lt (by linarith : (0 : ℝ) < s))),
    NlsGge.Ramer.cmToFullWeightedHilbert_denseRange c s ((le_of_lt (by linarith : (0 : ℝ) < s))),
    cm_inclusion_hs c s hs, hsumm, ?_⟩
  have hnorm := NlsGge.Analysis.RegularizedDeterminant.HilbertSchmidt.energy_eq_norm_sq
    (inclEHS c s hs)
  have hnorm' := hnorm.symm.trans (inclE_energy_eq c s hs)
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) hS0).1 hnorm'

theorem cm_norm_sq_normalization
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (h : H c) :
    Summable (fun n : ℤ =>
      NlsGge.Pilot.sourceRate c n * ‖NlsGge.Ramer.cmCoord h n‖ ^ 2) ∧
    ‖h‖ ^ 2 = 2 * ∑' n : ℤ,
      NlsGge.Pilot.sourceRate c n * ‖NlsGge.Ramer.cmCoord h n‖ ^ 2 := by
  have hw := (NlsGge.Pilot.weightedHilbert_hasSum (NlsGge.Pilot.cmModeWeight c)
    (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) from h)).summable
  constructor
  · have h2 := hw.mul_left (1 / 2 : ℝ)
    refine h2.congr (fun n => ?_)
    change (1 / 2 : ℝ) * (NlsGge.Pilot.cmModeWeight c n *
      ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) from h) n‖ ^ 2) =
      NlsGge.Pilot.sourceRate c n *
      ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) from h) n‖ ^ 2
    simp only [NlsGge.Pilot.cmModeWeight]
    ring
  · rw [NlsGge.Ramer.actualCM_norm_sq, ← tsum_mul_left]
    congr 1
    funext n
    simp only [NlsGge.Pilot.cmModeWeight]
    ring

end NlsGge.ThirdConsultation.R.BindingR013
end
