import QuantumNLS.REF88QuantumDef

/-! R-EF8C2837 item (iv): the accepted R-1E0C40B3 at arbitrary nonzero H¹ mass.
The law is the Born law of u/‖u‖ at effective coupling K=κ‖u‖², so contact is K/N.
The limiting action probabilities are I_n^{(κ)}(u)/‖u‖², not I_n^{(κ)}(u).
No general-mass law at κ/N is asserted. Author sol_multi round23; reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.REF88SRescale
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductEnergyPreparation (OneH1)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.ActualGapR26
open QuantumNLS.RootEnergyMomentLaws (law)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.F04SelBand (II)
open QuantumNLS.BornConvergence (TendstoInProbability)
variable {L κ : ℝ} [Fact (0 < L)]

theorem oneH1_smul (c : ℂ) {u : L2T L} (hH : OneH1 u) : OneH1 (c • u) := by
  unfold OneH1 Fourier.Mem04 at hH ⊢
  refine (hH.mul_left (‖c‖ ^ 2)).congr fun n => ?_
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

theorem oneH1_unitDir {u : L2T L} (hH : OneH1 u) : OneH1 (FullMass.unitDir u) :=
  oneH1_smul _ hH

/-- The full accepted actual-gap theorem, rescaled with all unit-norm hypotheses discharged.
Every active pair is tested using the original unnormalized indexed masses. -/
theorem general_mass_actual_gap (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) (hH : OneH1 u) :
    ∃ (hK : 0 < κ * ‖u‖ ^ 2) (D : Data hK (FullMass.unitDir u)),
      (∀ n : ℤ, II hK (FullMass.unitDir u) n = II hκ u n / ‖u‖ ^ 2) ∧
      (∀ a b : ℤ, 0 < II hκ u a → 0 < II hκ u b →
        IntervalIntegrable D.integrand volume (b : ℝ) a) ∧
      (∀ a : ℤ, D.omega a a = 0) ∧
      (∀ a b : ℤ, D.omega a b = -D.omega b a) ∧
      (∀ a b d : ℤ, 0 < II hκ u a → 0 < II hκ u b → 0 < II hκ u d →
        D.omega a b + D.omega b d = D.omega a d) ∧
      Tendsto (meanOccupationError hK (FullMass.unitDir u) (FullMass.norm_unitDir hu)) atTop (𝓝 0) ∧
      (∀ (default : ∀ N, MArr N → ℝ) (a b : ℤ), a ≠ b → 0 < II hκ u a → 0 < II hκ u b →
        TendstoInProbability (law hK (FullMass.unitDir u) (FullMass.norm_unitDir hu))
          (fun _ => gapWithDefault L (κ * ‖u‖ ^ 2) a b default) (D.omega a b) ∧
        Tendsto (V hK (FullMass.unitDir u) (FullMass.norm_unitDir hu) a b default (D.omega a b)) atTop (𝓝 0) ∧
        (∀ T : ℝ,
          (∀ N : ℕ, EpsSq hK (FullMass.unitDir u) (FullMass.norm_unitDir hu) a b default (D.omega a b) T N ≤
            ENNReal.ofReal (T ^ 2) * V hK (FullMass.unitDir u) (FullMass.norm_unitDir hu) a b default (D.omega a b) N +
              4 * meanOccupationError hK (FullMass.unitDir u) (FullMass.norm_unitDir hu) N /
                ENNReal.ofReal (radius hK (FullMass.unitDir u) a b)) ∧
          Tendsto (EpsSq hK (FullMass.unitDir u) (FullMass.norm_unitDir hu) a b default (D.omega a b) T) atTop (𝓝 0))) := by
  have hm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hu)
  let hK : 0 < κ * ‖u‖ ^ 2 := mul_pos hκ hm
  have hv := FullMass.norm_unitDir hu
  have hi (n : ℤ) : II hK (FullMass.unitDir u) n = II hκ u n / ‖u‖ ^ 2 := by
    rw [REF88QuantumDef.II_unitDir hκ hu hK]
    field_simp [hm.ne']
  have hp (n : ℤ) (hn : 0 < II hκ u n) : 0 < II hK (FullMass.unitDir u) n := by
    rw [hi]; exact div_pos hn hm
  obtain ⟨D,hint,hzero,hswap,hcoc,hocc,hpair⟩ :=
    actual_law_cubic_energy_gaps hK (FullMass.unitDir u) hv (oneH1_unitDir hH)
  exact ⟨hK,D,hi,fun a b ha hb => hint a b (hp a ha) (hp b hb),hzero,hswap,
    fun a b d ha hb hd => hcoc a b d (hp a ha) (hp b hb) (hp d hd),hocc,
    fun default a b hab ha hb => hpair default a b hab (hp a ha) (hp b hb)⟩

#print axioms oneH1_unitDir
#print axioms general_mass_actual_gap
end QuantumNLS.REF88SRescale
