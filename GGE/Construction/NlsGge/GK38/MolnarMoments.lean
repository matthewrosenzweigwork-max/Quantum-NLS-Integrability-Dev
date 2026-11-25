import NlsGge.Spectral.NonlinRiccatiAllK38b

/-!
# Mo1: gap-by-gap moment sums for the Molnár package and for H0

Piece Mo1 of the E01 plan (`campaign/E01_PLAN.md` §6.12; rev. 3 note G1 N5): a re-statement
and adapter of `gap_hasSum_integral38` (`Spectral/F04EnergyIdentity38.lean`) in the form the Mo
package and H0 (`F04AtOne`) consume.  Nothing here is a new analytic input: every statement is the
repository's trace formula `actualTraceFormula_Hk_all38` (all `k ≥ 1`), its lower-order companion
`actualTraceFormula_lower_E02_38`, and the mass identity `actualGapHeight_integral_eq_normSq_E02_38`,
cut into the gaps `g_n = [λ_n^-, λ_n^+]` on which `v = actualGapHeightE02_38 u` lives.

Normalization (repository, matching v2): `I_n(u) = actualGapActionAllE02_38 u n
= (2/π) ∫_{g_n} v`, and the moment `M_{2k}(u) = (2/π) ∫_ℝ (2t)^{2k} v(t) dt` equals the charge
`Q_{2k} = chargeSobolev38 (k+1) k y`.  Source: Molnár arXiv:1403.1369, level-one trace formula
(2) `Σ I_n = ½‖φ‖²₀` (v2 normalization: `‖u‖²`), Theorem 4 (trace formula, quoted there from [9])
`Σ_n J_{n,k} = -(2i)^{1-k} H_k` and its corollary `Σ_n J_{n,2m+1} = 4^{-m}∫|φ^{(m)}|² + ⋯`, with
`J_{n,2m+1} ∼ (λ_n^±)^{2m} I_n`; Molnár uses the nonlinear-Fourier normalization (his `H_k`, `J_{n,k}`),
the repository's `v`-moment is the equivalent form, which is what is used here.  Molnár's use of the
identity: Lemma 14/Prop. 12 and the proofs of Theorem 2 (i), (ii) (Sections 4-5) sum `Σ_{|n|>N} ⟨2nπ⟩^{2m} I_n
≤ 8^m Σ J_{n,2m+1}` etc.

Statements:
* `gapMoment_hasSum38`: abstract adapter (any integrable `f` vanishing off `{v ≠ 0}`).
* `momentSum_eq_charge`: Mo1 of the plan: for `k ≥ 1`, `Σ_n (2/π)∫_{g_n} (2x)^{2k} v = Q_{2k}`.
* `momentSum_zero_eq_normSq`: the same at `k = 0`: `Σ_n I_n = ‖u‖²` on `H¹`.
* `weightedMomentSum_eq_energy38`: for `1 ≤ m`, the weighted version with `W_m`
  (`finiteWeightE02_38 m β`), total `energySobolev38 m β y`; valid at `m = 1` (what H0 needs).
* `gapMoment_eq_weight_mul_action_add_remainder`, `weightedMomentSum_split38`: the termwise
  identity `(2/π)∫_{g_n} W(2x) v = W(2πn) I_n + R_n` with the repository's remainder term
  `gapRemainderTermE02_38`, and the `HasSum` of `W(2πn) I_n + R_n` to the energy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Topology Interval

namespace NlsGge.GK38

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.Sobolev38
  NlsGge.HierarchyRiccati.Core

noncomputable section

/-- The gap `g_n` is a nonempty compact interval, so `λ_n^- ≤ λ_n^+`. -/
private theorem gapLower_le_upper_mo1 (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
  obtain ⟨y, hy⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
  have hy' : y ∈ actualGapLevelSetE02_38 u n := hy
  rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2] at hy'
  exact le_trans hy'.1 hy'.2

/-- Gap-by-gap form of an integral against the gap height: for `f` integrable and vanishing
where `v = 0`, `Σ_n (2/π) ∫_{g_n} f = (2/π) ∫ f`. (`gap_hasSum_integral38` times `2/π`.) -/
theorem gapMoment_hasSum38 (u : PhysicalL2) (f : ℝ → ℝ) (hf : Integrable f)
    (hz : ∀ x, actualGapHeightE02_38 u x = 0 → f x = 0) :
    HasSum (fun n : ℤ => (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), f x)
      ((2 / Real.pi) * ∫ x, f x) :=
  (gap_hasSum_integral38 u f hf hz).mul_left (2 / Real.pi)

/-- **Mo1.** For `k ≥ 1` and `u ∈ H^k`: the `2k`-moments over the gaps sum to the charge
`Q_{2k}` (trace formula, Molnár arXiv:1403.1369). -/
theorem momentSum_eq_charge (k : ℕ) (hk : 1 ≤ k) (u : PhysicalL2)
    (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) :
    HasSum (fun n : ℤ => (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (2 * x) ^ (2 * k) * actualGapHeightE02_38 u x) (chargeSobolev38 (k + 1) k y) := by
  obtain ⟨hI, hQ⟩ := actualTraceFormula_Hk_all38 k hk u y hy
  rw [← hQ]
  exact gapMoment_hasSum38 u _ hI (fun x hx => by simp [hx])

/-- The case `k = 0`: `Σ_n (2/π) ∫_{g_n} v = ‖u‖²` for `u ∈ H¹`. (Same as
`actualGapAction_hasSum_E02_38`, restated in the moment form of `momentSum_eq_charge`.) -/
theorem momentSum_zero_eq_normSq (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    HasSum (fun n : ℤ => (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (2 * x) ^ (2 * 0) * actualGapHeightE02_38 u x) (‖u‖ ^ 2) := by
  obtain ⟨hI, hQ⟩ := actualGapHeight_integral_eq_normSq_E02_38 u hu
  have h := gapMoment_hasSum38 u (actualGapHeightE02_38 u) hI (fun x hx => hx)
  rw [hQ] at h
  simpa using h

/-- The moments `(2t)^{2j} v` are integrable on `H^m` for `j ≤ m`, and equal the charges:
`j = 0` is the mass identity, `0 < j < m` is `actualTraceFormula_lower_E02_38`, `j = m` is
`actualTraceFormula_Hk_all38`.  (Packaged for `y ∈ H^m`, `m ≥ 1`.) -/
theorem moment_integrable_charge38 (m : ℕ) (hm : 1 ≤ m) (u : PhysicalL2)
    (y : SobolevHilbert ((m + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) (j : ℕ) (hj : j ≤ m) :
    Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) ∧
    (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t =
      chargeSobolev38 (m + 1) j y := by
  rcases lt_or_eq_of_le hj with hlt | rfl
  · exact actualTraceFormula_lower_E02_38 (m + 1) u y hy j (by omega)
  · exact actualTraceFormula_Hk_all38 j hm u y hy

/-- **Weighted moment sum on `H^m`, `m ≥ 1` (including `m = 1`).** With `u = sobolevToL2_38 m y`,
`Σ_n (2/π) ∫_{g_n} W_m(2x) v = E_m(y) = Σ_j β_j Q_{2j}`.  No positivity of `β` is needed. -/
theorem weightedMomentSum_eq_energy38 (m : ℕ) (hm : 1 ≤ m) (β : ℕ → ℝ)
    (y : SobolevHilbert (m : ℝ)) :
    HasSum (fun n : ℤ => (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 (sobolevToL2_38 m y) n)..
        (actualGapUpperAllE02_38 (sobolevToL2_38 m y) n),
        finiteWeightE02_38 m β (2 * x) * actualGapHeightE02_38 (sobolevToL2_38 m y) x)
      (energySobolev38 m β y) := by
  set u := sobolevToL2_38 m y with hudef
  have hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n := fun n => (sobolevToL2_38_fourier m y n).symm
  have hmom := moment_integrable_charge38 m hm u y hy
  obtain ⟨hhi, hexp⟩ := weightedMoment_expand38 m β u (fun j hj => (hmom j hj).1)
  have h := gapMoment_hasSum38 u _ hhi (fun x hx => by simp [hx])
  rw [hexp] at h
  convert h using 1
  unfold energySobolev38
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(hmom j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2]

/-- Termwise decomposition of a weighted gap moment:
`(2/π)∫_{g_n} W(2x) v = W(2πn) I_n + R_n`, with `R_n = gapRemainderTermE02_38 W u n`.
Needs only integrability of `v` and of `W(2·) v` (both hold on `H¹`, resp. `H^m`). -/
theorem gapMoment_eq_weight_mul_action_add_remainder (W : ℝ → ℝ) (u : PhysicalL2) (n : ℤ)
    (hv : Integrable (actualGapHeightE02_38 u))
    (hW : Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 u t)) :
    (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        W (2 * x) * actualGapHeightE02_38 u x =
      W (2 * Real.pi * n) * actualGapActionAllE02_38 u n + gapRemainderTermE02_38 W u n := by
  have h1 : IntervalIntegrable (fun x => W (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    hW.intervalIntegrable
  have h2 : IntervalIntegrable (fun x => W (2 * Real.pi * n) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (hv.const_mul _).intervalIntegrable
  unfold gapRemainderTermE02_38 actualGapActionAllE02_38
  have : ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        W (2 * x) * actualGapHeightE02_38 u x =
      (∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x) +
      W (2 * Real.pi * n) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        actualGapHeightE02_38 u x := by
    have h3 : IntervalIntegrable (fun x => (W (2 * x) - W (2 * Real.pi * n)) *
        actualGapHeightE02_38 u x) volume
        (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
      simpa only [sub_mul] using h1.sub h2
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h3 h2]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [this]
  ring

/-- **Split form for H0.** For `m ≥ 1`, `y ∈ H^m`: `Σ_n (W_m(2πn) I_n + R_n) = E_m(y)` as a
`HasSum` (no summability of the two pieces separately is asserted: that is H0's job). -/
theorem weightedMomentSum_split38 (m : ℕ) (hm : 1 ≤ m) (β : ℕ → ℝ)
    (y : SobolevHilbert (m : ℝ)) :
    HasSum (fun n : ℤ => finiteWeightE02_38 m β (2 * Real.pi * n) *
        actualGapActionAllE02_38 (sobolevToL2_38 m y) n +
      gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 m y) n)
      (energySobolev38 m β y) := by
  set u := sobolevToL2_38 m y with hudef
  have hsob : SobolevSquareSummable (m : ℝ) (physicalFourier u) := sobolevToL2_38_sobolev m y
  have hv := (actualGapHeight_integral_eq_normSq_E02_38 u
    (sobolevSquareSummable_restrict 1 (m : ℝ) (by exact_mod_cast hm) _ hsob)).1
  have hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n := fun n => (sobolevToL2_38_fourier m y n).symm
  have hmom := moment_integrable_charge38 m hm u y hy
  obtain ⟨hhi, -⟩ := weightedMoment_expand38 m β u (fun j hj => (hmom j hj).1)
  have h := weightedMomentSum_eq_energy38 m hm β y
  convert h using 1
  funext n
  exact (gapMoment_eq_weight_mul_action_add_remainder _ u n hv hhi).symm

/-! ## Regression probes -/

/-- Probe (positivity): the charges `Q_{2k}`, `k ≥ 1`, are nonnegative, and the gap moments are
summable. Obtained only through the gap-by-gap `HasSum`, since each gap integral of
`(2x)^{2k} v ≥ 0` is `≥ 0`. -/
theorem probe_charge_nonneg (k : ℕ) (hk : 1 ≤ k) (u : PhysicalL2)
    (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) :
    0 ≤ chargeSobolev38 (k + 1) k y := by
  refine (momentSum_eq_charge k hk u y hy).nonneg fun n => ?_
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg
    (gapLower_le_upper_mo1 u n) fun x _ => mul_nonneg ?_ (actualGapHeightE02_38_nonneg u x))
  rw [pow_mul]; positivity

/-- Probe (`m = 1`, the H0 case): with `W ≡ 1` (`β = (1, 0)`), the weighted sum of
`weightedMomentSum_eq_energy38` is `Σ I_n`, and by uniqueness of limits the charge `Q_0` at
level `H¹` (`chargeSobolev38 2 0`) equals `‖u‖²`: the mass identity recovered from two independent
routes (trace-formula packaging vs. `actualGapAction_hasSum_E02_38`). -/
theorem probe_charge_zero_eq_normSq (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    chargeSobolev38 2 0 y = ‖sobolevToL2_38 1 y‖ ^ 2 := by
  set β : ℕ → ℝ := fun j => if j = 0 then 1 else 0 with hβ
  have h1 := weightedMomentSum_eq_energy38 1 le_rfl β y
  have h0 := momentSum_zero_eq_normSq (sobolevToL2_38 1 y)
    (by simpa using sobolevToL2_38_sobolev 1 y)
  have hW : ∀ x : ℝ, finiteWeightE02_38 1 β (2 * x) = (2 * x) ^ (2 * 0) := by
    intro x; simp [finiteWeightE02_38, hβ]
  have hE : energySobolev38 1 β y = chargeSobolev38 2 0 y := by
    simp [energySobolev38, hβ]
  simp only [hW] at h1
  rw [hE] at h1
  exact h1.unique h0

end

end NlsGge.GK38
