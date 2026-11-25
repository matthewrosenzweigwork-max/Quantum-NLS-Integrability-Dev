import NlsGge.Birkhoff.SignedMoments38c

/-! # SIGNED-MOMENTS.04 (`F:rem:signed`), file 4: continuity of the odd local charge on `H^{m-1}` (`B`-free)

The odd local charge `C_{2j+1} = oddLocalCharge38 U j` has the extension `oddChargeSobolev38 m j` to `H^{m-1}`
(`j + 2 ≤ m`), the sum of the Fourier quadratic form `-Σ (2πn)^{2j+1}|y_n|²` and the realized monomials of the
normalized remainder (continuous multilinear forms with at most two `L²` slots; complex coefficient `-i a_q`
because `Im z = Re(-i z)`). It agrees with `oddLocalCharge38` on smooth fields (`oddChargeSobolev38_smooth`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
  Filter Topology
open scoped ContDiff ENNReal

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-! ## The Fourier quadratic form -/

/-- `-Σ_n (2πn)^{2j+1} |y_n|²` on `H^r` (quadratic part of the odd local charge). -/
def oddQuad38 (r : ℝ) (j : ℕ) (y : SobolevHilbert r) : ℝ :=
  -∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) *
    ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2

theorem oddQuad_weight_le38 (k j : ℕ) (hj : j + 1 ≤ k) (n : ℤ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    1 + max 0 (σ * (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1)) ≤
      (1 + (2 * Real.pi) ^ (2 * j + 1)) * sobolevModeWeight (k : ℝ) n := by
  rw [sobolevModeWeight_nat38]
  have h1 : (1 : ℝ) ≤ (1 + (n : ℝ) ^ 2) ^ k := one_le_pow₀ (by nlinarith [sq_nonneg (n : ℝ)])
  have hn : |(n : ℝ)| ≤ 1 + (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(n : ℝ)| - 1), sq_abs (n : ℝ)]
  have hpow : |(n : ℝ)| ^ (2 * j + 1) ≤ (1 + (n : ℝ) ^ 2) ^ k := by
    calc |(n : ℝ)| ^ (2 * j + 1) = (|(n : ℝ)| ^ 2) ^ j * |(n : ℝ)| := by rw [pow_succ, pow_mul]
      _ ≤ (1 + (n : ℝ) ^ 2) ^ j * (1 + (n : ℝ) ^ 2) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by rw [sq_abs]; linarith) _) hn
            (abs_nonneg _) (by positivity)
      _ = (1 + (n : ℝ) ^ 2) ^ (j + 1) := (pow_succ _ _).symm
      _ ≤ (1 + (n : ℝ) ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith [sq_nonneg (n : ℝ)]) hj
  have hmax : max 0 (σ * (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1)) ≤
      (2 * Real.pi) ^ (2 * j + 1) * (1 + (n : ℝ) ^ 2) ^ k := by
    refine max_le (by positivity) ?_
    calc σ * (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) ≤ |σ * (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1)| :=
          le_abs_self _
      _ = (2 * Real.pi) ^ (2 * j + 1) * |(n : ℝ)| ^ (2 * j + 1) := by
          rcases hσ with rfl | rfl <;>
            simp [abs_mul, abs_pow, abs_of_pos Real.pi_pos, mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  nlinarith

theorem continuous_oddQuad38 (k j : ℕ) (hj : j + 1 ≤ k) : Continuous (oddQuad38 (k : ℝ) j) := by
  set w := sobolevModeWeight (k : ℝ) with hw
  set a : ℤ → ℝ := fun n => (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) with ha
  set vp : ℤ → ℝ := fun n => 1 + max 0 (a n) with hvp
  set vm : ℤ → ℝ := fun n => 1 + max 0 (-a n) with hvm
  have hvppos : ∀ n : ℤ, 0 < vp n := fun n => by simp only [hvp]; have := le_max_left 0 (a n); linarith
  have hvmpos : ∀ n : ℤ, 0 < vm n := fun n => by simp only [hvm]; have := le_max_left 0 (-a n); linarith
  have : Fact (∀ n : ℤ, 0 < vp n) := ⟨hvppos⟩
  have : Fact (∀ n : ℤ, 0 < vm n) := ⟨hvmpos⟩
  have hC : 0 ≤ 1 + (2 * Real.pi) ^ (2 * j + 1) := by positivity
  let Lp := weightedRealComparisonContinuous w vp _ hC (fun n => by
    simpa [hvp, ha, one_mul] using oddQuad_weight_le38 k j hj n (σ := 1) (Or.inl rfl))
  let Lm := weightedRealComparisonContinuous w vm _ hC (fun n => by
    simpa [hvm, ha, neg_mul, one_mul] using oddQuad_weight_le38 k j hj n (σ := -1) (Or.inr rfl))
  have heq : oddQuad38 (k : ℝ) j = fun y => -(‖Lp y‖ ^ 2 - ‖Lm y‖ ^ 2) := by
    funext y
    have h1 := weightedHilbert_hasSum vp (show WeightedHilbert vp from Lp y)
    have h2 := weightedHilbert_hasSum vm (show WeightedHilbert vm from Lm y)
    have h3 := h1.sub h2
    refine (h3.tsum_eq).symm ▸ ?_
    unfold oddQuad38
    congr 1
    refine tsum_congr (fun n => ?_)
    show _ = vp n * ‖(show WeightedHilbert w from y) n‖ ^ 2 - vm n * ‖(show WeightedHilbert w from y) n‖ ^ 2
    simp only [hvp, hvm]
    have : max 0 (a n) - max 0 (-a n) = a n := by
      rcases le_total 0 (a n) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    simp only [ha] at this ⊢
    nlinarith [this, sq_nonneg ‖(show WeightedHilbert w from y) n‖]
  rw [heq]
  exact ((Lp.continuous.norm.pow 2).sub (Lm.continuous.norm.pow 2)).neg

/-! ## Monomial forms with a complex coefficient -/

/-- As `riccatiMonomialSobolevCMM38`, with a complex coefficient: `Re (c ∫ ∏ slots)`. -/
def riccatiMonomialSobolevCMMc38 (s : ℕ) (q : Jet →₀ ℕ) (c : ℂ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin (monomialSlotCount38 q) => SobolevCarrier38 (s : ℝ)) ℝ :=
  postcomposeCML38 (realCoefficient38 c)
    (postcomposeCML38
      (integrateProductLp38 (highCount38 (monomialSlotTop38 s q))
        (monomialSlot_highCount_le_two38 s q htop))
      (mixedProduct38 (E := SobolevCarrier38 (s : ℝ)) (monomialSlotTop38 s q)
        (monomialSlot_highCount_le_two38 s q htop) (monomialSlotMap38 s q)))

theorem riccatiMonomialSobolevCMMc38_apply (s : ℕ) (q : Jet →₀ ℕ) (c : ℂ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2)
    (y : Fin (monomialSlotCount38 q) → SobolevCarrier38 (s : ℝ)) :
    riccatiMonomialSobolevCMMc38 s q c htop y =
      (c * ∫ t, ∏ i, (monomialSlotMap38 s q i (y i) : PhysicalCircle → ℂ) t
        ∂spatialMeasure).re := by
  change (c * integrateProductLp38 _ _ (mixedProduct38 (E := SobolevCarrier38 (s : ℝ))
    (monomialSlotTop38 s q) (monomialSlot_highCount_le_two38 s q htop)
    (monomialSlotMap38 s q) y)).re = _
  rw [integrateProductLp_eq_integral38]
  rw [integral_congr_ae (mixedProduct_ae38 _ (monomialSlotTop38 s q)
    (monomialSlot_highCount_le_two38 s q htop) (monomialSlotMap38 s q) y)]

/-- Smooth-field identity: the diagonal is `Re (c ∫₀¹ ∏_{v} (∂^k u)^{n_v} (conjugated))`. -/
theorem riccatiMonomialSobolevCMMc38_diag_smooth (s : ℕ) (q : Jet →₀ ℕ) (c : ℂ)
    (htop : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = s)).card ≤ 2)
    (hord : ∀ v ∈ q.support, v.2 ≤ s) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (x : SobolevHilbert (s : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight (s : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    riccatiMonomialSobolevCMMc38 s q c htop (fun _ => toCarrier38 (s : ℝ) x) =
      (c * ∫ t in (0 : ℝ)..1, q.prod (fun v n => riccatiJetFunction u v t ^ n)).re := by
  classical
  set G : Fin (monomialSlotCount38 q) → PhysicalCircle → ℂ := fun i t =>
    conjugateIf38 (monomialSlotJet38 q i).1
      (AddCircle.liftIoc 1 0 (iteratedDeriv (monomialSlotJet38 q i).2 u) t) with hG
  have hall : ∀ᵐ t ∂spatialMeasure, ∀ i,
      (monomialSlotMap38 s q i (toCarrier38 (s : ℝ) x) : PhysicalCircle → ℂ) t = G i t :=
    ae_all_iff.2 (fun i => monomialSlotMap38_smooth_ae s q hord u hu hper x hsource i)
  have hint : (∫ t, ∏ i, (monomialSlotMap38 s q i (toCarrier38 (s : ℝ) x) :
      PhysicalCircle → ℂ) t ∂spatialMeasure) = ∫ t, ∏ i, G i t ∂spatialMeasure := by
    apply integral_congr_ae
    filter_upwards [hall] with t ht
    exact Finset.prod_congr rfl (fun i _ => ht i)
  have hprod : ∀ r ∈ Set.uIcc (0 : ℝ) 1,
      (∏ i, G i (r : PhysicalCircle)) =
        q.prod (fun v n => riccatiJetFunction u v r ^ n) := by
    intro r hr
    rw [Set.uIcc_of_le zero_le_one] at hr
    have hpt : ∀ i, G i (r : PhysicalCircle) = riccatiJetFunction u (monomialSlotJet38 q i) r := by
      intro i
      rw [hG, riccatiJetFunction_eq_conjugateIf38]
      simp only
      rw [liftIoc_unit_eq38 _
        (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper _) hr]
    simp_rw [hpt]
    rw [← riccatiActualMonomialSlotFinset_prodRecovery31Fourth,
      ← Finset.prod_coe_sort (riccatiActualMonomialSlotFinsetRecovery31Fourth q),
      ← Equiv.prod_comp (monomialSlotEquiv38 q)]
    rfl
  rw [riccatiMonomialSobolevCMMc38_apply, hint,
    ← NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar (fun t => ∏ i, G i t),
    intervalIntegral.integral_congr hprod]

theorem integral_monomial_eq38 (u : ℝ → ℂ) (q : Jet →₀ ℕ) (a : ℤ) :
    (∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (MvPolynomial.monomial q a)) =
      (a : ℂ) * ∫ t in (0 : ℝ)..1, q.prod (fun v n => riccatiJetFunction u v t ^ n) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  simp [riccatiJetEvaluation, polynomialEvaluation]

/-! ## The extension to `H^{m-1}` -/

/-- Realized monomial of the normalized odd remainder (`j + 2 ≤ m`), coefficient `-i a_q`; zero otherwise. -/
def oddRemainderValue38 (M j : ℕ) (q : Jet →₀ ℕ) (y : SobolevCarrier38 ((M - 1 : ℕ) : ℝ)) : ℝ :=
  if h : j + 2 ≤ M ∧ q ∈ (oddNormRem38 j).support then
    riccatiMonomialSobolevCMMc38 (M - 1) q (-Complex.I * (((oddNormRem38 j).coeff q : ℤ) : ℂ))
      (oddNormRem38_top M j h.1 q h.2) (fun _ => y)
  else 0

theorem continuous_oddRemainderValue38 (M j : ℕ) (q : Jet →₀ ℕ) :
    Continuous (oddRemainderValue38 M j q) := by
  unfold oddRemainderValue38
  by_cases h : j + 2 ≤ M ∧ q ∈ (oddNormRem38 j).support
  · simp only [h, and_self, dite_true]
    exact (riccatiMonomialSobolevCMMc38 _ _ _ _).cont.comp (continuous_pi fun _ => continuous_id)
  · simp only [h, dite_false]
    exact continuous_const

/-- The continuous extension of the odd local charge `C_{2j+1}` to `H^{m-1}` (for `j + 2 ≤ m`). -/
def oddChargeSobolev38 (m j : ℕ) (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) : ℝ :=
  oddQuad38 _ j y + ∑ q ∈ (oddNormRem38 j).support, oddRemainderValue38 m j q (toCarrier38 _ y)

/-- **SIGNED-MOMENTS.04 (odd case).** The odd local charge is a continuous functional on `H^{m-1}`, `j + 2 ≤ m`. -/
theorem continuous_oddChargeSobolev38 (m j : ℕ) (hmj : j + 2 ≤ m) :
    Continuous (oddChargeSobolev38 m j) := by
  unfold oddChargeSobolev38
  refine (continuous_oddQuad38 (m - 1) j (by omega)).add ?_
  exact continuous_finsetSum _ (fun q _ =>
    (continuous_oddRemainderValue38 m j q).comp (continuous_toCarrier38 _))

/-- On the Sobolev element of a smooth period-one field the extension is the odd local charge. -/
theorem oddChargeSobolev38_smooth (m j : ℕ) (hmj : j + 2 ≤ m)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (x : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper)) n) :
    oddChargeSobolev38 m j x = oddLocalCharge38 U j := by
  classical
  have hquad : oddQuad38 ((m - 1 : ℕ) : ℝ) j x =
      (∫ t in (0 : ℝ)..1, riccatiJetEvaluation U t (formalOddQuadraticMainTerm38 j)).im := by
    rw [(formalOddQuad_integral_im38 U hU hper j).2]
    unfold oddQuad38
    congr 1
    refine tsum_congr (fun n => ?_)
    rw [hsource n]
    rfl
  have hterm : ∀ q ∈ (oddNormRem38 j).support,
      oddRemainderValue38 m j q (toCarrier38 _ x) =
        (∫ t in (0 : ℝ)..1, riccatiJetEvaluation U t
          (MvPolynomial.monomial q ((oddNormRem38 j).coeff q))).im := by
    intro q hq
    have h : j + 2 ≤ m ∧ q ∈ (oddNormRem38 j).support := ⟨hmj, hq⟩
    simp only [oddRemainderValue38, h, and_self, dite_true]
    rw [riccatiMonomialSobolevCMMc38_diag_smooth (m - 1) q _ _
      (by
        intro v hv
        have := oddNormRem38_order' j q hq v hv
        omega) U hU hper x hsource, integral_monomial_eq38]
    set P := ∫ t in (0 : ℝ)..1, q.prod (fun v n => riccatiJetFunction U v t ^ n)
    simp [Complex.mul_re, Complex.mul_im]
  have hrem : (∑ q ∈ (oddNormRem38 j).support, oddRemainderValue38 m j q (toCarrier38 _ x)) =
      (∫ t in (0 : ℝ)..1, riccatiJetEvaluation U t (oddNormRem38 j)).im := by
    rw [Finset.sum_congr rfl hterm, ← Complex.im_sum,
      ← riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond U hU,
      ← MvPolynomial.as_sum]
  have hsplit : (∫ t in (0 : ℝ)..1, riccatiJetEvaluation U t (formalOddChargeIntegrand38 j)) =
      (∫ t in (0 : ℝ)..1, riccatiJetEvaluation U t (formalOddQuadraticMainTerm38 j)) +
        ∫ t in (0 : ℝ)..1, riccatiJetEvaluation U t (formalOddNonlinearRemainder38 j) := by
    rw [← intervalIntegral.integral_add
      ((riccatiJetEvaluation_continuousNativeRecovery U hU _).intervalIntegrable _ _)
      ((riccatiJetEvaluation_continuousNativeRecovery U hU _).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [formalOddNonlinearRemainder38, riccatiJetEvaluation, polynomialEvaluation, map_sub]
    ring
  unfold oddChargeSobolev38 oddLocalCharge38
  rw [hquad, hrem, hsplit, oddNormRem38_integral j U hU hper, Complex.add_im]

end NlsGge.Birkhoff
end
