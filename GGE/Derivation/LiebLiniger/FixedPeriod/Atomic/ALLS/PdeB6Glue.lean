import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6Rev

/-! # Track B, package 3: gluing interval solutions; local existence as interval solutions

* `MassHyp.glue`: solutions of the same trajectory on `[a,b]` and `[b,c]` glue (representative
  `U` for `t ≤ b`, `V` for `t > b`) to a solution on `[a,c]`;
* `MassHyp.of_base`: the coefficient identities from the left endpoint suffice;
* `local_massHyp_exists`: for every bound `M` there is `δ > 0` such that every datum of norm `≤ M`
  has interval solutions on `[0,δ]` and on `[-δ,0]` (the contraction of `PdeB5Local`, time reversal);
* `massHyp_point`: the constant trajectory on `[0,0]`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

/-- Glued representative. -/
def glueU (b : ℝ) (U V : ℝ × PhysicalCircle → ℂ) (p : ℝ × PhysicalCircle) : ℂ :=
  if p.1 ≤ b then U p else V p

namespace MassHyp

variable {u : ℝ → PhysicalL2} {U V : ℝ × PhysicalCircle → ℂ} {a b c : ℝ}

/-- Interval solutions from the left-endpoint coefficient identities. -/
theorem of_base (hc : ContinuousOn u (Set.Icc a b)) (hU : MemLp U 4 (slabM a b))
    (hs : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc a b)),
      (fun x => U (t, x)) =ᵐ[spatialMeasure] (u t : PhysicalCircle → ℂ))
    (hD : ∀ n : ℤ, ∀ t ∈ Set.Icc a b, intA u n t = intA u n a + ∫ r in a..t, intG U n r) :
    MassHyp u U a b where
  cont := hc
  memLp := hU
  slice := hs
  coeff := by
    intro n s hs' t ht
    have ha : a ∈ Set.Icc a b := ⟨le_rfl, hs'.1.trans hs'.2⟩
    rw [hD n t ht, hD n s hs', add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_intG hU n ha ht)
        (intervalIntegrable_intG hU n ha hs')]

theorem memLp_glue (H1 : MassHyp u U a b) (H2 : MassHyp u V b c) (hbc : b ≤ c) :
    MemLp (glueU b U V) 4 (slabM a c) := by
  have hm1 : MeasurableSet {p : ℝ × PhysicalCircle | p.1 ≤ b} :=
    measurableSet_le measurable_fst measurable_const
  have hm2 : MeasurableSet {p : ℝ × PhysicalCircle | b < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have e1 : (slabM a c).restrict {p : ℝ × PhysicalCircle | p.1 ≤ b} = slabM a b := by
    rw [Measure.restrict_restrict hm1]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc, Set.mem_univ,
      and_true]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.trans hbc⟩
  have e2 : (slabM a c).restrict {p : ℝ × PhysicalCircle | b < p.1} ≤ slabM b c := by
    rw [Measure.restrict_restrict hm2]
    refine Measure.restrict_mono (fun p hp => ?_) le_rfl
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc, Set.mem_univ,
      and_true] at hp ⊢
    exact ⟨hp.1.le, hp.2.2⟩
  have h1 : MemLp ({p : ℝ × PhysicalCircle | p.1 ≤ b}.indicator U) 4 (slabM a c) :=
    (memLp_indicator_iff_restrict hm1).2 (by rw [e1]; exact H1.memLp)
  have h2 : MemLp ({p : ℝ × PhysicalCircle | b < p.1}.indicator V) 4 (slabM a c) :=
    (memLp_indicator_iff_restrict hm2).2 (H2.memLp.mono_measure e2)
  have e : glueU b U V = {p : ℝ × PhysicalCircle | p.1 ≤ b}.indicator U +
      {p : ℝ × PhysicalCircle | b < p.1}.indicator V := by
    funext p
    by_cases h : p.1 ≤ b
    · simp [glueU, Set.indicator, h, not_lt.2 h]
    · simp [glueU, Set.indicator, h, not_le.1 h]
  rw [e]
  exact h1.add h2

/-- **Gluing** two interval solutions of the same trajectory. -/
theorem glue (H1 : MassHyp u U a b) (H2 : MassHyp u V b c) (hab : a ≤ b) (hbc : b ≤ c) :
    MassHyp u (glueU b U V) a c := by
  have hW := memLp_glue H1 H2 hbc
  have hb1 : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hb2 : b ∈ Set.Icc b c := ⟨le_rfl, hbc⟩
  have hbase : ∀ n : ℤ, ∀ t ∈ Set.Icc a c,
      intA u n t - intA u n b = ∫ r in b..t, intG (glueU b U V) n r := by
    intro n t ht
    rcases le_total t b with htb | htb
    · rw [H1.coeff n b hb1 t ⟨ht.1, htb⟩]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_ge htb] at hr
      simp only [intG, glueU, hr.2, ↓reduceIte]
    · rw [H2.coeff n b hb2 t ⟨htb, ht.2⟩]
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun r hr => ?_)
      rw [Set.uIoc_of_le htb] at hr
      simp only [intG, glueU, not_le.2 hr.1, ↓reduceIte]
  refine ⟨?_, hW, ?_, ?_⟩
  · rw [← Set.Icc_union_Icc_eq_Icc hab hbc]
    exact H1.cont.union_of_isClosed H2.cont isClosed_Icc isClosed_Icc
  · rw [← Set.Icc_union_Icc_eq_Icc hab hbc, ae_restrict_union_iff]
    constructor
    · filter_upwards [H1.slice, ae_restrict_mem measurableSet_Icc] with t ht hmem
      simpa only [glueU, hmem.2, ↓reduceIte] using ht
    · filter_upwards [H2.slice, ae_restrict_of_ae (ae_ne_real b),
        ae_restrict_mem measurableSet_Icc] with t ht hne hmem
      have hlt : ¬ t ≤ b := not_le.2 (lt_of_le_of_ne hmem.1 (Ne.symm hne))
      simpa only [glueU, hlt, ↓reduceIte] using ht
  · intro n s hs t ht
    have hbac : b ∈ Set.Icc a c := ⟨hab, hbc⟩
    have h1 := hbase n t ht
    have h2 := hbase n s hs
    rw [show intA u n t - intA u n s = (intA u n t - intA u n b) - (intA u n s - intA u n b) by ring,
      h1, h2, intervalIntegral.integral_interval_sub_left (intervalIntegrable_intG hW n hbac ht)
        (intervalIntegrable_intG hW n hbac hs)]

end MassHyp

/-- Coefficients of the slab-local Duhamel integral `duhH`. -/
theorem carrierCoe38_duhH {F : ℝ × PhysicalCircle → ℂ} {δ : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod spatialMeasure))
    {t : ℝ} (ht : t ∈ Set.Icc 0 δ) (n : ℤ) :
    carrierCoe38 (-1) (duhH F t) n =
      ∫ r in (0 : ℝ)..t, freePhase (t - r) n * (-Complex.I * physicalFourier (fun x => F (r, x)) n) := by
  have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 δ := Set.uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht
  have hi : IntervalIntegrable
      (fun r => freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x))))) volume 0 t :=
    (IntegrableOn.mono_set (integrable_duhamel_slab hF t) hsub).intervalIntegrable
  rw [duhH, carrierCoe38_intervalIntegral (-1) hi]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_integrable_slice hF] with r hr hmem
  rw [carrierCoe38_freeProp, carrierCoe38_negIMul,
    carrierCoe38_fnToHm1 (hr (hsub (Set.uIoc_subset_uIcc hmem)))]

/-- **Local existence as interval solutions**, forward and backward, with a lifespan depending only
on a bound for the datum. -/
theorem local_massHyp_exists (M : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ a0 : PhysicalL2, ‖a0‖ ≤ M →
    (∃ (v : ℝ → PhysicalL2) (W : ℝ × PhysicalCircle → ℂ), MassHyp v W 0 δ ∧ v 0 = a0) ∧
    (∃ (v : ℝ → PhysicalL2) (W : ℝ × PhysicalCircle → ℂ), MassHyp v W (-δ) 0 ∧ v 0 = a0) := by
  obtain ⟨K, C, hK, hC, hloc⟩ := local_solution
  obtain ⟨δ, hδ, hδ1, hsmall⟩ := lifespan_exists hK hC M
  have fwd : ∀ a0 : PhysicalL2, ‖a0‖ ≤ M →
      ∃ (v : ℝ → PhysicalL2) (W : ℝ × PhysicalCircle → ℂ), MassHyp v W 0 δ ∧ v 0 = a0 := by
    intro a0 ha0
    obtain ⟨v, W, hv, hv0, hW, hsl, hD⟩ := hloc δ hδ hδ1 a0 (hsmall a0 ha0)
    have hW' : MemLp W 4 (slabM 0 δ) := by
      rw [slabMeasure_eq] at hW; exact hW
    refine ⟨v, W, MassHyp.of_base hv.continuousOn hW' hsl fun n t ht => ?_, hv0⟩
    have hF : Integrable (cubF W) (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod
        spatialMeasure) := integrable_cubic_slabM hW'
    refine (coeff_duhamel_iff (u := v) (U := W) n t).1 ?_
    have h := congrArg (fun z => carrierCoe38 (-1) z n) (hD t ht)
    rw [coe38_add, carrierCoe38_duhH hF ht, carrierCoe38_freeProp_l2ToHm1] at h
    rw [hv0]
    exact h
  refine ⟨δ, hδ, fun a0 ha0 => ⟨fwd a0 ha0, ?_⟩⟩
  obtain ⟨v, W, H, hv0⟩ := fwd (conjL2 a0) (by rw [norm_conjL2]; exact ha0)
  have H' := H.rev
  rw [neg_zero] at H'
  refine ⟨revL2 v, revU W, H', ?_⟩
  simp only [revL2, neg_zero, hv0, conjL2_conjL2]

/-- The constant trajectory is an interval solution on `[0,0]`. -/
theorem massHyp_point (a0 : PhysicalL2) :
    MassHyp (fun _ => a0) (fun _ => 0) 0 0 := by
  have hz : (volume : Measure ℝ).restrict (Set.Icc 0 0) = 0 := by
    rw [Measure.restrict_eq_zero]; simp
  refine ⟨continuousOn_const, MemLp.zero, ?_, ?_⟩
  · rw [hz]; simp
  · intro n s hs t ht
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst hs0 ht0
    simp

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
