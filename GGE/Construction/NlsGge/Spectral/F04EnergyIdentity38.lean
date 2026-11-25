import NlsGge.Spectral.SobolevToL2Map38
import NlsGge.Spectral.TraceFormulaHk38
import NlsGge.Spectral.ActualSpectralRemainderE02_38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # Q5: the F04.06 energy identities on `H^m` (v2 B:lem:spectral, B:eq:energyidentities)

* `weightedMoment_split38`: `(2/π)∫ W_m(2λ) v = Σ_n a_{m,n} I_n + R_m` on `H^m` (unconditional).
* `energyIdentity_spectral38`: `E_m = Σ a_{m,n} I_n + R_m`, conditional on the R3c hypothesis at `k = m`.
* `energyIdentity_fourier38`: `E_m = Σ a_{m,n} |û(n)|² + V_m` (algebra of the charges, unconditional).

The second identity mixes the charges `chargeSobolev38 (m+1) j` (on `H^m`) and `chargeSobolev38 m j`
(on `H^{m-1}`).  For `j ≤ m - 1` this is `chargeSobolev38_cross_m`.  For `j = m` the nonlinear part of the
charge is a continuous polynomial on `H^{m-1}` (`normalizedRemainder38_order`), and the two realizations
agree by density of Fourier truncations (`chargeSobolev38_trunc`); the quadratic parts are compared directly. -/

/-- `E_m` on `H^m` via the continuous charges. -/
def energySobolev38 (m : ℕ) (β : ℕ → ℝ) (y : SobolevHilbert (m : ℝ)) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), β j * chargeSobolev38 (m + 1) j y

/-! ## Gap decomposition of an integral -/

/-- An integrable function vanishing where `v = 0` integrates gap by gap. -/
theorem gap_hasSum_integral38 (u : PhysicalL2) (f : ℝ → ℝ) (hf : Integrable f)
    (hz : ∀ x, actualGapHeightE02_38 u x = 0 → f x = 0) :
    HasSum (fun n : ℤ => ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), f x)
      (∫ x, f x) := by
  set s : ℤ → Set ℝ := fun n => actualGapLevelSetE02_38 u n with hsdef
  have hs : ∀ n, s n = Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    fun n => (actualGapLevelSet_eq_Icc_E02_38 u n).2
  have hm : ∀ n, MeasurableSet (s n) := fun n => by rw [hs n]; exact measurableSet_Icc
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hxn hxm => hnm ?_
    have e1 : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := hxn
    have e2 : actualQuasimomentumRealPartE02_38 u x = (m:ℝ) * Real.pi := hxm
    have : (n:ℝ) = m := mul_right_cancel₀ Real.pi_pos.ne' (e1.symm.trans e2)
    exact_mod_cast this
  have hoff : ∫ x in ⋃ n, s n, f x = ∫ x, f x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hz x ?_
    by_contra hv
    obtain ⟨m, hm'⟩ := realPart_int_mul_pi_of_gapHeight_ne_zero_E02_38 u x hv
    exact hx (Set.mem_iUnion.mpr ⟨m, hm'⟩)
  have hU := hasSum_integral_iUnion hm hd hf.integrableOn
  rw [hoff] at hU
  convert hU using 1
  funext n
  have hab : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
    obtain ⟨y, hy⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
    have hy' : y ∈ s n := hy
    rw [hs n] at hy'; exact le_trans hy'.1 hy'.2
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, ← hs n]

/-! ## Expansion of the weighted moment -/

theorem finiteWeight_mul_height38 (m : ℕ) (β : ℕ → ℝ) (u : PhysicalL2) :
    (fun t : ℝ => finiteWeightE02_38 m β (2*t) * actualGapHeightE02_38 u t) =
      fun t => ∑ j ∈ Finset.range (m + 1), β j * ((2*t)^(2*j) * actualGapHeightE02_38 u t) := by
  funext t
  simp only [finiteWeightE02_38, Finset.sum_mul, mul_assoc]

/-- Linearity: `(2/π)∫ W_m(2t) v = Σ_j β_j (2/π)∫ (2t)^{2j} v`, given each moment is integrable. -/
theorem weightedMoment_expand38 (m : ℕ) (β : ℕ → ℝ) (u : PhysicalL2)
    (hI : ∀ j ≤ m, Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t)) :
    Integrable (fun t : ℝ => finiteWeightE02_38 m β (2*t) * actualGapHeightE02_38 u t) ∧
    (2/Real.pi) * ∫ t : ℝ, finiteWeightE02_38 m β (2*t) * actualGapHeightE02_38 u t =
      ∑ j ∈ Finset.range (m + 1), β j * ((2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t) := by
  rw [finiteWeight_mul_height38]
  have hIj : ∀ j ∈ Finset.range (m + 1),
      Integrable (fun t : ℝ => β j * ((2*t)^(2*j) * actualGapHeightE02_38 u t)) :=
    fun j hj => (hI j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul _
  refine ⟨integrable_finsetSum _ hIj, ?_⟩
  rw [integral_finsetSum _ hIj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

/-! ## (i) The split of the weighted moment -/

/-- (i) unconditional: `(2/π)∫ W_m(2λ) v = Σ_n a_{m,n} I_n + R_m` on `H^m`. -/
theorem weightedMoment_split38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (u : PhysicalL2) (hu : SobolevSquareSummable (m:ℝ) (physicalFourier u)) :
    Summable (fun n : ℤ => finiteWeightE02_38 m β (2*Real.pi*n) * actualGapActionAllE02_38 u n) ∧
    (2/Real.pi) * ∫ t, finiteWeightE02_38 m β (2*t) * actualGapHeightE02_38 u t =
      (∑' n : ℤ, finiteWeightE02_38 m β (2*Real.pi*n) * actualGapActionAllE02_38 u n) +
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) u n := by
  have hpi := Real.pi_pos
  obtain ⟨hW, hconv, A, hA, hd⟩ := finiteWeight_hyp_E02_38 m hm β hβ
  have hu' : SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u) :=
    sobolevSquareSummable_restrict _ _ (by exact_mod_cast Nat.sub_le m 1) _ hu
  have hRem : RemainderHypE02_38 (finiteWeightE02_38 m β) (m - 1) A u :=
    ⟨hW, hconv, by omega, hA, hd, hu'⟩
  obtain ⟨hgi, -, hS⟩ := gapRemainder_summable_E02_38 _ (m - 1) A u hRem
  have hmom : ∀ j ≤ m, Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := (actualGapHeight_integral_eq_normSq_E02_38 u
        (sobolevSquareSummable_restrict 1 (m:ℝ) (by exact_mod_cast (by omega : 1 ≤ m)) _ hu)).1
      simpa using this
    · exact actualMoment_integrable_of_sobolev38 j hj0 u
        (sobolevSquareSummable_restrict _ _ (by exact_mod_cast hj) _ hu)
  obtain ⟨hhi, -⟩ := weightedMoment_expand38 m β u hmom
  set W := finiteWeightE02_38 m β with hWdef
  set q : ℝ → ℝ := fun x => W (2 * actualQuasimomentumRealPartE02_38 u x) *
    actualGapHeightE02_38 u x with hqdef
  have hqi : Integrable q := by
    refine (hhi.sub hgi).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, remainderIntegrandE02_38, hqdef]
    ring
  have hz : ∀ x, actualGapHeightE02_38 u x = 0 → q x = 0 := by
    intro x hx
    simp [hqdef, hx]
  have hq_sum := gap_hasSum_integral38 u q hqi hz
  have hterm : ∀ n : ℤ, (2/Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), q x =
      W (2*Real.pi*n) * actualGapActionAllE02_38 u n := by
    intro n
    have hab : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
      obtain ⟨y, hy⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
      have hy' : y ∈ actualGapLevelSetE02_38 u n := hy
      rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2] at hy'; exact le_trans hy'.1 hy'.2
    have hcongr : ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), q x =
        ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
          W (2*Real.pi*n) * actualGapHeightE02_38 u x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hab] at hx
      have hx' : x ∈ actualGapLevelSetE02_38 u n := by
        rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2]; exact hx
      have hpx : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := hx'
      simp only [hqdef, hpx]
      rw [show 2 * ((n:ℝ) * Real.pi) = 2 * Real.pi * n by ring]
    rw [hcongr, intervalIntegral.integral_const_mul]
    unfold actualGapActionAllE02_38
    ring
  have hSa : HasSum (fun n : ℤ => W (2*Real.pi*n) * actualGapActionAllE02_38 u n)
      ((2/Real.pi) * ∫ x, q x) := by
    convert hq_sum.mul_left (2/Real.pi) using 1
    funext n; exact (hterm n).symm
  refine ⟨hSa.summable, ?_⟩
  rw [hSa.tsum_eq, hS.tsum_eq]
  have hsplit : ∫ t, W (2*t) * actualGapHeightE02_38 u t =
      (∫ x, remainderIntegrandE02_38 W u x) + ∫ x, q x := by
    rw [← integral_add hgi hqi]
    congr 1
    funext x
    simp only [remainderIntegrandE02_38, hqdef]
    ring
  rw [hsplit]
  ring

/-! ## (ii) The first energy identity -/

/-- F04.06 first identity, conditional on R3c at `k = m`. -/
theorem energyIdentity_spectral38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (hR3c : NonlinRiccatiSmoothBound38 m) (y : SobolevHilbert (m : ℝ)) :
    energySobolev38 m β y =
      (∑' n : ℤ, finiteWeightE02_38 m β (2*Real.pi*n) *
        actualGapActionAllE02_38 (sobolevToL2_38 m y) n) +
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 m y) n := by
  set u := sobolevToL2_38 m y with hudef
  have hsob : SobolevSquareSummable (m : ℝ) (physicalFourier u) := sobolevToL2_38_sobolev m y
  have hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n := fun n => (sobolevToL2_38_fourier m y n).symm
  obtain ⟨-, hsplit⟩ := weightedMoment_split38 m hm β hβ u hsob
  have hmom : ∀ j ≤ m, Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) ∧
      (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t =
        chargeSobolev38 (m + 1) j y := by
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | rfl
    · exact actualTraceFormula_lower_E02_38 (m + 1) u y hy j (by omega)
    · exact actualTraceFormula_Hk38 j (by omega) hR3c u y hy
  obtain ⟨-, hexp⟩ := weightedMoment_expand38 m β u (fun j hj => (hmom j hj).1)
  rw [← hsplit, hexp]
  unfold energySobolev38
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(hmom j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2]

/-! ## (iii) The second energy identity: algebra of the charges -/

/-- The nonlinear (monomial) part of `chargeSobolev38`. -/
def monSum38 (M j : ℕ) (y : SobolevHilbert ((M - 1 : ℕ) : ℝ)) : ℝ :=
  ∑ q ∈ (normalizedRemainder38 j).support, localRemainderMonomialValue38 M j q (toCarrier38 _ y)

theorem chargeSobolev38_eq_quad_add_mon38 (M j : ℕ) (y : SobolevHilbert ((M - 1 : ℕ) : ℝ)) :
    chargeSobolev38 M j y = chargeQuad38 _ j y + monSum38 M j y := rfl

theorem continuous_monSum38 (M j : ℕ) : Continuous (monSum38 M j) :=
  continuous_finsetSum _ (fun q _ =>
    (continuous_localRemainderMonomialValue38 M j q).comp (continuous_toCarrier38 _))

theorem chargeQuad38_congr (r r' : ℝ) (j : ℕ) (y : SobolevHilbert r) (y' : SobolevHilbert r')
    (h : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight r) from y) n =
      (show WeightedHilbert (sobolevModeWeight r') from y') n) :
    chargeQuad38 r j y = chargeQuad38 r' j y' := by
  unfold chargeQuad38
  exact tsum_congr fun n => by rw [h n]

/-- The top case `j = m` of the cross-`m` comparison of the nonlinear charge parts, by density of
Fourier truncations (both sides are continuous, and agree on truncations by `chargeSobolev38_trunc`). -/
theorem monSum38_cross_top (m : ℕ) (hm : 2 ≤ m)
    (y : SobolevHilbert ((m + 1 - 1 : ℕ) : ℝ)) (y' : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hyy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m + 1 - 1 : ℕ) : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) :
    monSum38 (m + 1) m y = monSum38 m m y' := by
  have hT := tendsto_truncSobolev38 ((m + 1 - 1 : ℕ) : ℝ) y
  have hT' := tendsto_truncSobolev38 ((m - 1 : ℕ) : ℝ) y'
  have h1 := ((continuous_monSum38 (m + 1) m).tendsto y).comp hT
  have h2 := ((continuous_monSum38 m m).tendsto y').comp hT'
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp]
  have e1 := chargeSobolev38_trunc (m + 1) m (by omega) (by omega) N y
  have e2 := chargeSobolev38_trunc m m hm le_rfl N y'
  have hplane : chargeSobolev38 (m + 1) m (truncSobolev38 _ N y) =
      chargeSobolev38 m m (truncSobolev38 _ N y') := by
    rw [e1, e2]
    congr 3
    funext i
    exact hyy _
  have hq : chargeQuad38 _ m (truncSobolev38 ((m + 1 - 1 : ℕ) : ℝ) N y) =
      chargeQuad38 _ m (truncSobolev38 ((m - 1 : ℕ) : ℝ) N y') :=
    chargeQuad38_congr _ _ m _ _ fun n => by
      simp only [truncSobolev38_apply, hyy n]
  rw [chargeSobolev38_eq_quad_add_mon38, chargeSobolev38_eq_quad_add_mon38, hq] at hplane
  linarith

/-- Cross-`m` comparison of the nonlinear charge parts for every `j ≤ m`: `chargeSobolev38_cross_m`
for `j ≤ m - 1`, density for `j = m`. -/
theorem monSum38_cross (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j ≤ m)
    (y : SobolevHilbert ((m + 1 - 1 : ℕ) : ℝ)) (y' : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hyy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m + 1 - 1 : ℕ) : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) :
    monSum38 (m + 1) j y = monSum38 m j y' := by
  rcases lt_or_eq_of_le hj with hlt | rfl
  · have h := chargeSobolev38_cross_m m (m + 1) j hm (by omega) (by omega) y y' hyy
    rw [chargeSobolev38_eq_quad_add_mon38, chargeSobolev38_eq_quad_add_mon38,
      chargeQuad38_congr _ _ j y y' hyy] at h
    linarith
  · exact monSum38_cross_top j hm y y' hyy

theorem summable_chargeQuad_term38 (m j : ℕ) (hj : j ≤ m) (y : SobolevHilbert (m : ℝ)) :
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ (2 * j) *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) := by
  have hS := (weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y)).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by rw [pow_mul]; positivity) (sq_nonneg _))
    (fun n => ?_) (hS.mul_left (1 + (2 * Real.pi) ^ (2 * j)))
  have h := chargeQuad_weight_le38 m j hj n
  calc (2 * Real.pi * (n : ℝ)) ^ (2 * j) * ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2
      ≤ (1 + (2 * Real.pi * (n : ℝ)) ^ (2 * j)) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ ≤ ((1 + (2 * Real.pi) ^ (2 * j)) * sobolevModeWeight (m : ℝ) n) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = _ := by ring

/-- F04.06 second identity (unconditional; algebra of the charges). -/
theorem energyIdentity_fourier38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (y : SobolevHilbert (m : ℝ)) (y' : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hyy : ∀ n, (show WeightedHilbert (sobolevModeWeight (m:ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m-1:ℕ):ℝ)) from y') n) :
    energySobolev38 m β y =
      (∑' n : ℤ, finiteHierarchyRate38 m β n * ‖(show WeightedHilbert (sobolevModeWeight (m:ℝ)) from y) n‖^2) +
      localRemainderSobolev38 m β (toCarrier38 _ y') := by
  have hcs : ∀ j ∈ Finset.range (m + 1), Summable (fun n : ℤ => β j *
      ((2 * Real.pi * (n : ℝ)) ^ (2 * j) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2)) :=
    fun j hj => (summable_chargeQuad_term38 m j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) y).mul_left _
  have hfun : (fun n : ℤ => finiteHierarchyRate38 m β n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) = fun n : ℤ =>
        ∑ j ∈ Finset.range (m + 1), β j * ((2 * Real.pi * (n : ℝ)) ^ (2 * j) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) := by
    funext n
    simp only [finiteHierarchyRate38, finiteHierarchyW38, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, Summable.tsum_finsetSum hcs]
  unfold energySobolev38 localRemainderSobolev38
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [tsum_mul_left, chargeSobolev38_eq_quad_add_mon38, ← mul_add]
  congr 1
  rw [monSum38_cross m hm j hjm y y' hyy]
  rfl

end NlsGge.SpectralFoundations
end
