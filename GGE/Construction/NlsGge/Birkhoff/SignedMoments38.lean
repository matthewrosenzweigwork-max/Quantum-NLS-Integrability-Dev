import NlsGge.Spectral.ChargeJensenSobolev38

/-! # SIGNED-MOMENTS (`F:rem:signed`, v2 l.1822-1829), file 1: the odd local charge, formal part (`B`-free)

The odd signed spectral moment `C_{2j+1} = (2/π)∫(2λ)^{2j+1} v` has the local polynomial representative
`Im ∫₀¹ (-1)^{j+1} u p_{2j+2}` (`oddLocalCharge38`; `formalOddChargeIntegrand38 j = (-1)^{j+1} u p_{2j+2}`).
Its weight is `2j+3`, its gauge is `0`; the degree-two component is `(-1)^j u ∂^{2j+1} ū`
(`formalOddQuadraticMainTerm38`) and the nonlinear remainder has `≥ 4` field factors and derivative count `≤ 2j-1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.HierarchyRiccati.Core MeasureTheory
open scoped ContDiff

/-- The signed formal density `(-1)^(j+1) u p_(2j+2)`, before integration. -/
def formalOddChargeIntegrand38 (j : ℕ) : Poly :=
  MvPolynomial.C ((-1 : ℤ) ^ (j + 1)) * MvPolynomial.X (false, 0) * p (2 * j + 2)

/-- The quadratic main term `(-1)^j u ∂^{2j+1} ū` of the odd formal charge. -/
def formalOddQuadraticMainTerm38 (j : ℕ) : Poly :=
  MvPolynomial.C ((-1 : ℤ) ^ j) * MvPolynomial.X (false, 0) * MvPolynomial.X (true, 2 * j + 1)

/-- The remainder after subtracting the quadratic component. -/
def formalOddNonlinearRemainder38 (j : ℕ) : Poly :=
  formalOddChargeIntegrand38 j - formalOddQuadraticMainTerm38 j

theorem formalOddChargeIntegrand38_degreeTwoComponent (j : ℕ) :
    MvPolynomial.homogeneousComponent 2 (formalOddChargeIntegrand38 j) =
      formalOddQuadraticMainTerm38 j := by
  unfold formalOddChargeIntegrand38 formalOddQuadraticMainTerm38
  rw [mul_assoc, MvPolynomial.homogeneousComponent_C_mul,
    homogeneousComponent_succ_mul_X,
    p_linear_homogeneous_component (2 * j + 2) (by omega)]
  have hindex : 2 * j + 2 - 1 = 2 * j + 1 := by omega
  rw [hindex]
  have hsign : (-1 : ℤ) ^ (j + 1) = -((-1 : ℤ) ^ j) := by
    rw [pow_succ]
    ring
  rw [hsign]
  simp [mul_assoc]

theorem formalOddChargeIntegrand38_support_bidegree (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m ∈ (formalOddChargeIntegrand38 j).support) :
    riccatiJetBidegreeAfterComponents m = (2 * j + 3, 0) := by
  classical
  have hscalar : (-1 : ℤ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold formalOddChargeIntegrand38 at hm
  rw [mul_assoc, MvPolynomial.C_mul'] at hm
  rw [MvPolynomial.support_smul_eq hscalar, MvPolynomial.support_X_mul] at hm
  rcases Finset.mem_map.mp hm with ⟨n, hn, hmap⟩
  have hmEq : Finsupp.single (false, 0) 1 + n = m := by simpa using hmap
  have hp := riccati_p_has_bidegree_after_components (2 * j + 2) (by omega)
  have hnb := hp n hn
  have hnWeight : riccatiJetWeightHomAfterComponents n = 2 * j + 2 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.fst hnb
  have hnGauge : riccatiJetGaugeHomAfterComponents n = 1 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.snd hnb
  rw [← hmEq]
  apply Prod.ext
  · change riccatiJetWeightHomAfterComponents
        (Finsupp.single (false, 0) 1 + n) = 2 * j + 3
    rw [map_add, riccatiJetWeightHomAfterComponents_single, hnWeight]
    omega
  · change riccatiJetGaugeHomAfterComponents
        (Finsupp.single (false, 0) 1 + n) = 0
    rw [map_add, riccatiJetGaugeHomAfterComponents_single, hnGauge]
    norm_num

theorem formalOdd_coefficient_degreeTwo (j : ℕ) (m : Jet →₀ ℕ) (hm : m.degree = 2) :
    (formalOddChargeIntegrand38 j).coeff m = (formalOddQuadraticMainTerm38 j).coeff m := by
  have h := congrArg (fun P : Poly => P.coeff m)
    (formalOddChargeIntegrand38_degreeTwoComponent j)
  rw [MvPolynomial.coeff_homogeneousComponent] at h
  simpa [hm] using h

theorem formalOddNonlinearRemainder38_support_subset_charge (j : ℕ) :
    (formalOddNonlinearRemainder38 j).support ⊆ (formalOddChargeIntegrand38 j).support := by
  classical
  intro m hm
  have hmUnion := MvPolynomial.support_sub Jet (formalOddChargeIntegrand38 j)
    (formalOddQuadraticMainTerm38 j) hm
  rcases Finset.mem_union.mp hmUnion with hdensity | hmain
  · exact hdensity
  · have hmainHom : (formalOddQuadraticMainTerm38 j).IsHomogeneous 2 := by
      rw [← formalOddChargeIntegrand38_degreeTwoComponent j]
      exact MvPolynomial.homogeneousComponent_isHomogeneous 2 (formalOddChargeIntegrand38 j)
    have hsum : 2 = ∑ v ∈ m.support, m v := hmainHom.degree_eq_sum_deg_support hmain
    have hmDegree : m.degree = 2 := by
      rw [Finsupp.degree_apply]
      exact hsum.symm
    have hcoeff := formalOdd_coefficient_degreeTwo j m hmDegree
    have hmainCoeff : (formalOddQuadraticMainTerm38 j).coeff m ≠ 0 :=
      Finsupp.mem_support_iff.mp hmain
    have hdensityCoeff : (formalOddChargeIntegrand38 j).coeff m ≠ 0 := by
      simpa [hcoeff] using hmainCoeff
    exact Finsupp.mem_support_iff.mpr hdensityCoeff

theorem formalOddNonlinearRemainder38_support_bidegree (j : ℕ)
    (m : Jet →₀ ℕ) (hm : m ∈ (formalOddNonlinearRemainder38 j).support) :
    riccatiJetBidegreeAfterComponents m = (2 * j + 3, 0) :=
  formalOddChargeIntegrand38_support_bidegree j m
    (formalOddNonlinearRemainder38_support_subset_charge j hm)

theorem formalOddNonlinearRemainder38_coeff_degreeTwo_eq_zero
    (j : ℕ) (m : Jet →₀ ℕ) (hm : m.degree = 2) :
    (formalOddNonlinearRemainder38 j).coeff m = 0 := by
  rw [formalOddNonlinearRemainder38, MvPolynomial.coeff_sub,
    formalOdd_coefficient_degreeTwo j m hm, sub_self]

/-- Every exponent in the odd nonlinear remainder has at least four field factors and derivative count
`≤ 2j-1`. -/
theorem formalOddNonlinearRemainder38_support_order_bounds
    (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m ∈ (formalOddNonlinearRemainder38 j).support) :
    4 ≤ m.degree ∧ riccatiJetDerivativeOrderSumNativeRecovery m ≤ 2 * j - 1 := by
  have hbidegree := formalOddNonlinearRemainder38_support_bidegree j m hm
  have hweight : riccatiJetWeightHomAfterComponents m = 2 * j + 3 :=
    congrArg Prod.fst hbidegree
  have hgauge : riccatiJetGaugeHomAfterComponents m = 0 :=
    congrArg Prod.snd hbidegree
  have heven := riccatiJetGauge_zero_implies_degree_evenNativeRecovery m hgauge
  have hdegree_ne_two : m.degree ≠ 2 := by
    intro hdegree
    have hnonzero : (formalOddNonlinearRemainder38 j).coeff m ≠ 0 :=
      Finsupp.mem_support_iff.mp hm
    exact hnonzero (formalOddNonlinearRemainder38_coeff_degreeTwo_eq_zero j m hdegree)
  have hdegree_pos : 0 < m.degree := by
    by_contra hnot
    have hzero : m.degree = 0 := by omega
    have hmzero : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hzero
    subst m
    simp [riccatiJetWeightHomAfterComponents] at hweight
  have hdegree_four : 4 ≤ m.degree := by
    rcases heven with ⟨k, hk⟩
    omega
  rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery] at hweight
  exact ⟨hdegree_four, by omega⟩

/-- The odd remainder is normalized, uniformly in the field, to a polynomial of jet order `≤ j` with the same
factor counts and bidegree. -/
theorem exists_formalOddRemainder_normalized38 (j : ℕ) :
    ∃ P : Poly, HasJetOrderAtMostNativeRecovery (j + 1) P ∧
      (∀ m ∈ P.support, 4 ≤ m.degree ∧ riccatiJetBidegreeAfterComponents m = (2 * j + 3, 0)) ∧
      ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1),
        (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalOddNonlinearRemainder38 j)) =
          ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P := by
  classical
  have h : ∀ m : Jet →₀ ℕ, ∃ P : Poly,
      m ∈ (formalOddNonlinearRemainder38 j).support →
        (HasJetOrderAtMostNativeRecovery (j + 1) P ∧
          HasJetFactorDegreeOnSupportUniformRecovery28Seventh P m.degree ∧
          HasRiccatiJetBidegreeAfterComponents P (riccatiJetBidegreeAfterComponents m) ∧
          ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1),
            (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x
              (MvPolynomial.monomial m ((formalOddNonlinearRemainder38 j).coeff m))) =
            ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P) := by
    intro m
    by_cases hm : m ∈ (formalOddNonlinearRemainder38 j).support
    · have horder := formalOddNonlinearRemainder38_support_order_bounds j m hm
      have hcount : riccatiJetDerivativeOrderWeightNativeRecovery m ≤ 2 * (j + 1) - 2 := by
        have := horder.2
        simp only [riccatiJetDerivativeOrderWeightNativeRecovery,
          riccatiJetDerivativeOrderSumNativeRecovery, Finsupp.weight_apply, smul_eq_mul] at this ⊢
        omega
      obtain ⟨P, h1, h2, h3, h4⟩ :=
        riccatiJetMonomial_periodic_normalize_uniformNativeRecovery28Fifth (j + 1) m
          ((formalOddNonlinearRemainder38 j).coeff m) hcount
      exact ⟨P, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, fun h' => absurd h' hm⟩
  choose Pm hPm using h
  set s := (formalOddNonlinearRemainder38 j).support with hs
  refine ⟨∑ m ∈ s, Pm m, ?_, ?_, ?_⟩
  · exact hasJetOrderAtMost_finset_sumNativeRecovery s Pm (fun m hm => (hPm m hm).1)
  · intro n hn
    have hnmem : n ∈ Finset.biUnion s (fun m => (Pm m).support) := MvPolynomial.support_sum hn
    obtain ⟨m, hm, hnm⟩ := Finset.mem_biUnion.mp hnmem
    have hsource := formalOddNonlinearRemainder38_support_order_bounds j m hm
    have hfactor := (hPm m hm).2.1 n hnm
    have hbi := (hPm m hm).2.2.1 n hnm
    rw [formalOddNonlinearRemainder38_support_bidegree j m hm] at hbi
    exact ⟨by rw [hfactor]; exact hsource.1, hbi⟩
  · intro u hu hper
    calc (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalOddNonlinearRemainder38 j))
        = ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x
            (∑ m ∈ s, MvPolynomial.monomial m ((formalOddNonlinearRemainder38 j).coeff m)) := by
          have hsumPoly : formalOddNonlinearRemainder38 j =
              ∑ m ∈ s, MvPolynomial.monomial m ((formalOddNonlinearRemainder38 j).coeff m) := by
            simp only [s]; exact MvPolynomial.as_sum (formalOddNonlinearRemainder38 j)
          exact congrArg (fun P : Poly => ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P) hsumPoly
      _ = ∑ m ∈ s, ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x
            (MvPolynomial.monomial m ((formalOddNonlinearRemainder38 j).coeff m)) :=
          riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu s _
      _ = ∑ m ∈ s, ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Pm m) :=
          Finset.sum_congr rfl fun m hm => (hPm m hm).2.2.2 u hu hper
      _ = _ := (riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu s Pm).symm

/-- The normalized odd remainder polynomial. -/
def oddNormRem38 (j : ℕ) : Poly := Classical.choose (exists_formalOddRemainder_normalized38 j)

theorem oddNormRem38_order (j : ℕ) : HasJetOrderAtMostNativeRecovery (j + 1) (oddNormRem38 j) :=
  (Classical.choose_spec (exists_formalOddRemainder_normalized38 j)).1

theorem oddNormRem38_support (j : ℕ) (m : Jet →₀ ℕ) (hm : m ∈ (oddNormRem38 j).support) :
    4 ≤ m.degree ∧ riccatiJetBidegreeAfterComponents m = (2 * j + 3, 0) :=
  (Classical.choose_spec (exists_formalOddRemainder_normalized38 j)).2.1 m hm

theorem oddNormRem38_integral (j : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalOddNonlinearRemainder38 j)) =
      ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (oddNormRem38 j) :=
  (Classical.choose_spec (exists_formalOddRemainder_normalized38 j)).2.2 u hu hper

theorem oddNormRem38_orderSum (j : ℕ) (q : Jet →₀ ℕ) (hq : q ∈ (oddNormRem38 j).support) :
    riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * j - 1 := by
  obtain ⟨h4, hb⟩ := oddNormRem38_support j q hq
  have hweight : riccatiJetWeightHomAfterComponents q = 2 * j + 3 := congrArg Prod.fst hb
  rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery] at hweight
  omega

theorem oddNormRem38_degree (j : ℕ) (q : Jet →₀ ℕ) (hq : q ∈ (oddNormRem38 j).support) :
    q.degree ≤ 2 * j + 3 := by
  obtain ⟨h4, hb⟩ := oddNormRem38_support j q hq
  have hweight : riccatiJetWeightHomAfterComponents q = 2 * j + 3 := congrArg Prod.fst hb
  rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery] at hweight
  omega

theorem oddNormRem38_order' (j : ℕ) (q : Jet →₀ ℕ) (hq : q ∈ (oddNormRem38 j).support) :
    ∀ v ∈ q.support, v.2 ≤ j := by
  intro v hv
  have := oddNormRem38_order j q hq v hv
  omega

/-- At most two top slots at Sobolev order `M-1` for `M ≥ j+2` (in fact none). -/
theorem oddNormRem38_top (M j : ℕ) (hM : j + 2 ≤ M) (q : Jet →₀ ℕ)
    (hq : q ∈ (oddNormRem38 j).support) :
    ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = M - 1)).card ≤ 2 := by
  have hfilt : (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = M - 1) =
      (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 + 1 = M) := by
    apply Finset.filter_congr
    intro σ _
    omega
  rw [hfilt]
  have hlow := oddNormRem38_order' j q hq
  have hmult : riccatiTopJetSlotMultiplicityMinimumRecovery30Third M q = 0 := by
    unfold riccatiTopJetSlotMultiplicityMinimumRecovery30Third
    apply Finset.sum_eq_zero
    intro v hv
    by_cases htop : v.2 + 1 = M
    · have := hlow v hv
      omega
    · simp [htop]
  rw [riccatiActualMonomialSlotFinset_topCardRecovery31Fourth, hmult]
  omega

end NlsGge.Birkhoff
end
