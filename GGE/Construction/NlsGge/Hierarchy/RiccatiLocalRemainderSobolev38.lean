import NlsGge.Hierarchy.RiccatiMonomialSobolevCMM38
import NlsGge.Hierarchy.RiccatiQuadraticLeadingIBP38
import NlsGge.Hierarchy.RiccatiFormalChargeRemainderUniformNormalizationRecovery29Fourth
import NlsGge.Hierarchy.RiccatiNormalizedRemainderDerivativeCountAndTopSlotsRecovery33Second
import NlsGge.Hierarchy.RiccatiJetEvaluationFiniteIntervalSumRecoverySecond
import NlsGge.Sobolev38.FinitePolynomial38
import Mathlib.Tactic

/-! Batch 38, F03 (`B:lem:local`, paper/v2.tex lines 616-625): the finite-order
local remainder as a continuous real polynomial on `H^{M-1}` with degree at
most `2M+2`, agreeing on smooth fields with
`Σ_{j ≤ M} β_j (Re Q_{2j}^{loc}(u) - ‖∂^j u‖²)`.

`Q_{2j}^{loc}(u) = ∫₀¹ (-1)^{j+1} u p_{2j+1}` is the source local charge
(lines 956-959). Its identification with the spectral `Q_{2j}` (E06.06),
the vanishing of its imaginary part, and the Parseval form
`‖∂^j u‖² = Σ_n (2πn)^{2j} |û(n)|²` are separate obligations. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Sobolev38
open MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The actual normalized nonlinear remainder of the `j`-th charge. -/
abbrev normalizedRemainder38 (j : ℕ) : Poly :=
  formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j

theorem normalizedRemainder38_top (M j : ℕ) (hM : 2 ≤ M) (hjM : j ≤ M)
    (q : Jet →₀ ℕ) (hq : q ∈ (normalizedRemainder38 j).support) :
    ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = M - 1)).card ≤ 2 := by
  have h := formalChargeRemainderNormalized_topSlotCard_le_twoRecovery33Second M j hM hjM q hq
  have hfilt : (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = M - 1) =
      (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 + 1 = M) := by
    apply Finset.filter_congr
    intro σ _
    omega
  rw [hfilt]
  exact h

theorem normalizedRemainder38_order (M j : ℕ) (hjM : j ≤ M)
    (q : Jet →₀ ℕ) (hq : q ∈ (normalizedRemainder38 j).support) :
    ∀ v ∈ q.support, v.2 ≤ M - 1 := by
  intro v hv
  have h := (formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j).1 q hq v hv
  omega

theorem normalizedRemainder38_degree (M j : ℕ) (hjM : j ≤ M)
    (q : Jet →₀ ℕ) (hq : q ∈ (normalizedRemainder38 j).support) :
    q.degree ≤ 2 * M + 2 := by
  have h := (formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j).2.2.2 q hq
  omega

/-- The realized monomial form for `j ≤ M` and supported `q`; zero otherwise. -/
def localRemainderMonomialValue38 (M j : ℕ) (q : Jet →₀ ℕ)
    (y : SobolevCarrier38 ((M - 1 : ℕ) : ℝ)) : ℝ :=
  if h : 2 ≤ M ∧ j ≤ M ∧ q ∈ (normalizedRemainder38 j).support then
    riccatiMonomialSobolevCMM38 (M - 1) q ((normalizedRemainder38 j).coeff q)
      (normalizedRemainder38_top M j h.1 h.2.1 q h.2.2) (fun _ => y)
  else 0

/-- F03: the finite-order local remainder on the Sobolev carrier `H^{M-1}`.
Arbitrary real coefficients `β` are allowed (the source fixes `β_j > 0`). -/
def localRemainderSobolev38 (M : ℕ) (β : ℕ → ℝ)
    (y : SobolevCarrier38 ((M - 1 : ℕ) : ℝ)) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), β j *
    ∑ q ∈ (normalizedRemainder38 j).support, localRemainderMonomialValue38 M j q y

theorem continuous_localRemainderMonomialValue38 (M j : ℕ) (q : Jet →₀ ℕ) :
    Continuous (localRemainderMonomialValue38 M j q) := by
  unfold localRemainderMonomialValue38
  by_cases h : 2 ≤ M ∧ j ≤ M ∧ q ∈ (normalizedRemainder38 j).support
  · simp only [h, and_self, dite_true]
    exact (riccatiMonomialSobolevCMM38 _ _ _ _).cont.comp
      (continuous_pi fun _ => continuous_id)
  · simp only [h, dite_false]
    exact continuous_const

/-- F03 continuity on `H^{M-1}`. -/
theorem continuous_localRemainderSobolev38 (M : ℕ) (β : ℕ → ℝ) :
    Continuous (localRemainderSobolev38 M β) := by
  unfold localRemainderSobolev38
  refine continuous_finsetSum _ (fun j _ => continuous_const.mul ?_)
  exact continuous_finsetSum _ (fun q _ => continuous_localRemainderMonomialValue38 M j q)

/-- Each realized monomial is the diagonal of a real continuous multilinear
form of degree at most `2M+2` (the "continuous real polynomial" structure). -/
theorem localRemainderMonomialValue38_polynomial (M j : ℕ) (q : Jet →₀ ℕ) :
    ∃ n : ℕ, n ≤ 2 * M + 2 ∧
      ∃ L : ContinuousMultilinearMap ℝ
          (fun _ : Fin n => SobolevCarrier38 ((M - 1 : ℕ) : ℝ)) ℝ,
        ∀ y, localRemainderMonomialValue38 M j q y = L (fun _ => y) := by
  by_cases h : 2 ≤ M ∧ j ≤ M ∧ q ∈ (normalizedRemainder38 j).support
  · refine ⟨monomialSlotCount38 q, ?_, riccatiMonomialSobolevCMM38 (M - 1) q
      ((normalizedRemainder38 j).coeff q) (normalizedRemainder38_top M j h.1 h.2.1 q h.2.2),
      ?_⟩
    · rw [monomialSlotCount38_eq_degree]
      exact normalizedRemainder38_degree M j h.2.1 q h.2.2
    · intro y
      simp [localRemainderMonomialValue38, h]
  · refine ⟨0, by omega, 0, ?_⟩
    intro y
    rw [localRemainderMonomialValue38, dite_eq_right_iff.mpr (fun h' => absurd h' h)]
    rfl

theorem localRemainderMonomialValue38_bound (M j : ℕ) (q : Jet →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |localRemainderMonomialValue38 M j q y| ≤
      C * (1 + ‖y‖ ^ (2 * M + 2)) := by
  obtain ⟨n, hn, L, hL⟩ := localRemainderMonomialValue38_polynomial M j q
  refine ⟨‖L‖, norm_nonneg _, fun y => ?_⟩
  rw [hL]
  have h := L.le_opNorm (fun _ => y)
  rw [Real.norm_eq_abs, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (normPower_le_one_add38 (norm_nonneg y) hn) (norm_nonneg _))

/-- F03 polynomial bound `|V(y)| ≤ C (1 + ‖y‖^{2M+2})`, constant independent
of `y`. -/
theorem localRemainderSobolev38_bound (M : ℕ) (β : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |localRemainderSobolev38 M β y| ≤
      C * (1 + ‖y‖ ^ (2 * M + 2)) := by
  classical
  choose C hC0 hC using fun (j : ℕ) (q : Jet →₀ ℕ) =>
    localRemainderMonomialValue38_bound M j q
  refine ⟨∑ j ∈ Finset.range (M + 1), |β j| *
      ∑ q ∈ (normalizedRemainder38 j).support, C j q, ?_, fun y => ?_⟩
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg (fun q _ => hC0 j q)))
  · unfold localRemainderSobolev38
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => hC j q y)

/-- F03 "bounded on bounded subsets". -/
theorem localRemainderSobolev38_isBounded_image (M : ℕ) (β : ℕ → ℝ)
    (S : Set (SobolevCarrier38 ((M - 1 : ℕ) : ℝ))) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (localRemainderSobolev38 M β '' S) := by
  obtain ⟨C, hC0, hC⟩ := localRemainderSobolev38_bound M β
  obtain ⟨R, _hR, hnorm⟩ := hS.exists_pos_norm_le
  apply isBounded_iff_forall_norm_le.2
  refine ⟨C * (1 + R ^ (2 * M + 2)), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [Real.norm_eq_abs]
  refine (hC y).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  gcongr
  exact hnorm y hy

/-- Smooth identity for one charge: the realized monomials of the normalized
remainder sum to the real part of its period integral. -/
theorem localRemainderCharge38_smooth (M j : ℕ) (hM : 2 ≤ M) (hjM : j ≤ M)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((M - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    (∑ q ∈ (normalizedRemainder38 j).support,
        localRemainderMonomialValue38 M j q (toCarrier38 _ x)) =
      (∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (normalizedRemainder38 j)).re := by
  classical
  have hterm : ∀ q ∈ (normalizedRemainder38 j).support,
      localRemainderMonomialValue38 M j q (toCarrier38 _ x) =
        (∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t
          (MvPolynomial.monomial q ((normalizedRemainder38 j).coeff q))).re := by
    intro q hq
    have h : 2 ≤ M ∧ j ≤ M ∧ q ∈ (normalizedRemainder38 j).support := ⟨hM, hjM, hq⟩
    simp only [localRemainderMonomialValue38, h, and_self, dite_true]
    exact riccatiMonomialSobolevCMM38_diag_smooth (M - 1) q _ _
      (normalizedRemainder38_order M j hjM q hq) u hu hper x hsource
  rw [Finset.sum_congr rfl hterm, ← Complex.re_sum,
    ← riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu,
    ← MvPolynomial.as_sum]

/-- F03 smooth-field agreement: on the Sobolev element of a smooth period-one
field, the realized remainder equals
`Σ_{j ≤ M} β_j (Re ∫₀¹ (-1)^{j+1} u p_{2j+1} - ∫₀¹ |u^{(j)}|²)`. -/
theorem localRemainderSobolev38_smooth (M : ℕ) (hM : 2 ≤ M) (β : ℕ → ℝ)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((M - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    localRemainderSobolev38 M β (toCarrier38 _ x) =
      ∑ j ∈ Finset.range (M + 1), β j *
        ((∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (formalChargeIntegrand j)).re -
          ∫ t in (0 : ℝ)..1, ‖iteratedDeriv j u t‖ ^ 2) := by
  unfold localRemainderSobolev38
  apply Finset.sum_congr rfl
  intro j hj
  have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 1
  rw [localRemainderCharge38_smooth M j hM hjM u hu hper x hsource,
    formalChargeIntegrand_integral_quadratic_plus_uniformRemainderNativeRecovery29Fourth
      j u hu hper,
    formalChargeQuadraticMainTerm_integral_eq38 j u hu hper,
    intervalIntegral.integral_ofReal, Complex.add_re, Complex.ofReal_re]
  ring

end NlsGge.HierarchyRiccati.Core

end
