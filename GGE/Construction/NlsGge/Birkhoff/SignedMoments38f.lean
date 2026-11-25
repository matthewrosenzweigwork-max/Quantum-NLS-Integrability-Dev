import NlsGge.Birkhoff.SignedMoments38e
import NlsGge.Birkhoff.F11Claim38f

/-! # SIGNED-MOMENTS (`F:rem:signed`), file 6: the signed charge functionals on fields (`B`-free)

* `oddChargeFn38 m j : L² → ℝ` is `oddChargeSobolev38 m j` evaluated on the Fourier carrier of `u` (cleaned to the
  value at `0` off `H^{m-1}`), exactly as `chargeFn38` (NEW-F11) for the even charges.
* `signedChargeFn38 m k` is the signed local moment `C_k` (`k` even: `Q_k = chargeFn38 m (k/2)`; `k` odd: `oddChargeFn38`),
  for `k ≤ 2m - 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal Real ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The odd local charge functional `C_{2j+1}` on fields (cleaned off `H^{m-1}`). -/
def oddChargeFn38 (m j : ℕ) (u : PhysicalL2) : ℝ :=
  oddChargeSobolev38 m j (ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u))

/-- **SIGNED-MOMENTS.01/.04 (field level).** The signed local hierarchy moment `C_k` on `L²`:
`C_{2j} = Q_{2j}` (`chargeFn38`), `C_{2j+1} = oddChargeFn38`. -/
def signedChargeFn38 (m k : ℕ) (u : PhysicalL2) : ℝ :=
  if k % 2 = 0 then chargeFn38 m (k / 2) u else oddChargeFn38 m (k / 2) u

theorem signedChargeFn38_even (m j : ℕ) (u : PhysicalL2) :
    signedChargeFn38 m (2 * j) u = chargeFn38 m j u := by
  unfold signedChargeFn38
  simp

theorem signedChargeFn38_odd (m j : ℕ) (u : PhysicalL2) :
    signedChargeFn38 m (2 * j + 1) u = oddChargeFn38 m j u := by
  unfold signedChargeFn38
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [h1, h2]

theorem measurable_oddChargeFn38 (m j : ℕ) (hmj : j + 2 ≤ m) : Measurable (oddChargeFn38 m j) := by
  let _ : MeasurableSpace (SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  let _ : MeasurableSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  exact (continuous_oddChargeSobolev38 m j hmj).measurable.comp
    ((continuous_ofCarrier38 _).measurable.comp (measurable_physC38 (m - 1)))

theorem measurable_signedChargeFn38 (m k : ℕ) (hm : 2 ≤ m) (hk : k ≤ 2 * m - 2) :
    Measurable (signedChargeFn38 m k) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [show signedChargeFn38 m (2 * j) = chargeFn38 m j from funext (signedChargeFn38_even m j)]
    exact measurable_chargeFn38 m j (by omega)
  · rw [show signedChargeFn38 m (2 * j + 1) = oddChargeFn38 m j from funext (signedChargeFn38_odd m j)]
    exact measurable_oddChargeFn38 m j (by omega)

/-- `y ↦ C_{2j+1}(𝓕⁻¹ y)` is continuous on the Birkhoff carrier `h^{m-1}`. -/
theorem continuous_oddChargeFn_physOfCarrier38 (m j : ℕ) (hmj : j + 2 ≤ m) :
    Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      oddChargeFn38 m j (physOfCarrier38 ((m - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) y)) := by
  have : (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      oddChargeFn38 m j (physOfCarrier38 ((m - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) y)) =
      (oddChargeSobolev38 m j) ∘ (ofCarrier38 _) ∘ (reflCF11_38 ((m - 1 : ℕ) : ℝ)) :=
    funext fun y => by
      simp only [Function.comp, oddChargeFn38, physC38_physOfCarrier38]
  rw [this]
  exact (continuous_oddChargeSobolev38 m j hmj).comp
    ((continuous_ofCarrier38 _).comp (continuous_reflCF11_38 _))

theorem continuous_signedChargeFn_physOfCarrier38 (m k : ℕ) (hm : 2 ≤ m) (hk : k ≤ 2 * m - 2) :
    Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      signedChargeFn38 m k (physOfCarrier38 ((m - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) y)) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simp only [signedChargeFn38_even]
    exact continuous_chargeFn_physOfCarrier38 m j (by omega)
  · simp only [signedChargeFn38_odd]
    exact continuous_oddChargeFn_physOfCarrier38 m j (by omega)

/-- **SIGNED-MOMENTS.02 (field level).** `C_{2j+1}² ≤ Q_{2j} Q_{2j+2}`. -/
theorem oddChargeFn_cs38 (m j : ℕ) (hmj : j + 2 ≤ m) (u : PhysicalL2) :
    oddChargeFn38 m j u ^ 2 ≤ chargeFn38 m j u * chargeFn38 m (j + 1) u :=
  oddChargeSobolev_cs38 m j hmj _

/-- **SIGNED-MOMENTS.03 (field level).** `|C_{2j+1}| ≤ (Q_{2j} + Q_{2j+2})/2`. -/
theorem oddChargeFn_amgm38 (m j : ℕ) (hmj : j + 2 ≤ m) (u : PhysicalL2) :
    |oddChargeFn38 m j u| ≤ (chargeFn38 m j u + chargeFn38 m (j + 1) u) / 2 :=
  oddChargeSobolev_amgm38 m j hmj _

/-- Every admissible signed moment is dominated by the sum of the even charges. -/
theorem signedChargeFn_abs_le38 (m k : ℕ) (hm : 2 ≤ m) (hk : k ≤ 2 * m - 2) (u : PhysicalL2) :
    |signedChargeFn38 m k u| ≤ ∑ j ∈ Finset.range m, chargeFn38 m j u := by
  have hQ : ∀ j ∈ Finset.range m, 0 ≤ chargeFn38 m j u := fun j hj =>
    chargeFn38_nonneg m j hm (by have := Finset.mem_range.1 hj; omega) u
  have hsingle : ∀ j, j ≤ m - 1 → chargeFn38 m j u ≤ ∑ i ∈ Finset.range m, chargeFn38 m i u := fun j hj =>
    Finset.single_le_sum hQ (Finset.mem_range.2 (by omega))
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simp only [signedChargeFn38_even]
    rw [abs_of_nonneg (chargeFn38_nonneg m j hm (by omega) u)]
    exact hsingle j (by omega)
  · simp only [signedChargeFn38_odd]
    have h := oddChargeFn_amgm38 m j (by omega) u
    have h1 := hsingle j (by omega)
    have h2 := hsingle (j + 1) (by omega)
    have h0 := chargeFn38_nonneg m j hm (by omega) u
    have h3 := chargeFn38_nonneg m (j + 1) hm (by omega) u
    have h4 : chargeFn38 m j u + chargeFn38 m (j + 1) u ≤ ∑ i ∈ Finset.range m, chargeFn38 m i u := by
      have : chargeFn38 m j u + chargeFn38 m (j + 1) u =
          ∑ i ∈ ({j, j + 1} : Finset ℕ), chargeFn38 m i u := by
        rw [Finset.sum_pair (by omega)]
      rw [this]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega)
        (fun i hi _ => hQ i hi)
    linarith

/-- Identification on smooth fields (**SIGNED-MOMENTS.01/.04**): for a field `u = [U]` with smooth period-one
representative `U` lying in every `H^k`, the signed charge functional is the local polynomial charge and the
spectral moment `(2/π)∫(2λ)^k v(λ;u) dλ` (`k ≤ 2m-2`). -/
theorem signedChargeFn38_smooth (m k : ℕ) (hm : 2 ≤ m) (hk : k ≤ 2 * m - 2)
    (u : PhysicalL2) (hall : ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u))
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (hUu : smoothL2_38 U hU hper = u) :
    signedChargeFn38 m k u = signedSpectralMoment38 u k := by
  have hmem : (fun n => physicalFourier u n) ∈ seqSobolev38 (((m - 1 : ℕ) : ℝ)) :=
    (mem_seqSobolev38_iff _ _).2 (hall (m - 1))
  set x : SobolevHilbert ((m - 1 : ℕ) : ℝ) := ofCarrier38 ((m - 1 : ℕ) : ℝ) (physC38 (m - 1) u)
    with hx
  have hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper)) n := by
    intro n
    have e : (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper) : PhysicalL2) = u :=
      hUu
    rw [e]
    have : x = carrierMk38 ((m - 1 : ℕ) : ℝ) _ hmem := by
      rw [hx]; exact physC38_of_mem (m - 1) u hmem
    rw [this]
    rfl
  subst hUu
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [signedChargeFn38_even]
    have h2 := chargeSobolev38_smooth_spectral m j hm (by omega) U hU hper x hsource
    rw [show chargeFn38 m j (smoothL2_38 U hU hper) = chargeSobolev38 m j x from rfl, h2]
    rfl
  · rw [signedChargeFn38_odd]
    have h1 := oddChargeSobolev38_smooth m j (by omega) U hU hper x hsource
    rw [show oddChargeFn38 m j (smoothL2_38 U hU hper) = oddChargeSobolev38 m j x from rfl, h1]
    exact ((signedSpectral_moments38 U hU hper (j + 1)).2 j le_rfl).symm

end NlsGge.Birkhoff
end
