import NlsGge.Ramer.General.RamerGeneral
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.Spectral.ActualSpectralRemainderE02_38

/-!
# G5 (ii): the F05 instance of the general Ramer theorem (v2 l.680)

`S_m := RamerSetting.ofSobolevRates (a m ·) _ (m-1) _` with
* `w_n = ⟨n⟩^{2(m-1)}` (`sobolevModeWeight (m-1)`), so `S_m.E ≃ₗᵢ h^{m-1}` coordinatewise
  (`F05Equiv`);
* `q_n = a_{m,n} = W_m(2πn) = finiteHierarchyRate38 m β n = finiteWeightE02_38 m β (2πn)`
  (the latter identification is `rfl`: `a_eq_finiteWeight`).

Required inputs of the `RamerSetting` constructor, all proved:
* `0 < a_{m,n}` for every `n` (`rate_pos38`, from `β_0 > 0`, `β_m > 0`, `β_j ≥ 0`);
* `Σ ⟨n⟩^{2(m-1)} / a_{m,n} < ∞` (`summable_tailRatio38`, from `a_{m,n} ≥ c ⟨n⟩^{2m}`,
  `rate_lower_bracket38`).
No further Hilbert–Schmidt or trace condition is demanded: the Hilbert–Schmidt property of
`incl : H → E` is *derived* (`RamerSetting.incl_hs`) from exactly this summability.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer
open NlsGge.Ramer.General.RamerSetting NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38
open NlsGge.SpectralFoundations

/-! ### The inputs -/

section Inputs

variable (m : ℕ) (β : ℕ → ℝ)

/-- The F05/F04 rate `a_{m,n} = W_m(2πn)` is the F06 rate `finiteHierarchyRate38`
(definitional). -/
theorem a_eq_finiteWeight (n : ℤ) :
    finiteHierarchyRate38 m β n = finiteWeightE02_38 m β (2 * Real.pi * n) := rfl

/-- F04's hypotheses `2 ≤ m`, `β_j > 0` give the F06 hypotheses (`β_j ≥ 0`, `β_0 > 0`,
`β_m > 0`). -/
theorem hyps_of_pos (hβ : ∀ j ≤ m, 0 < β j) :
    (∀ i ≤ m, 0 ≤ β i) ∧ 0 < β 0 ∧ 0 < β m :=
  ⟨fun i hi => (hβ i hi).le, hβ 0 (Nat.zero_le _), hβ m le_rfl⟩

variable (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m)
include hm hβ h0 hM

/-- (i) positivity `a_{m,n} > 0`. -/
theorem F05_rate_pos (n : ℤ) : 0 < finiteWeightE02_38 m β (2 * Real.pi * n) :=
  rate_pos38 m β (by omega) hβ h0 hM n

/-- (ii) `Σ ⟨n⟩^{2(m-1)} / a_{m,n} < ∞`. -/
theorem F05_summable :
    Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * ((m - 1 : ℕ) : ℝ)) /
      finiteWeightE02_38 m β (2 * Real.pi * n)) :=
  summable_tailRatio38 m β hm hβ h0 hM

end Inputs

/-! ### The setting -/

/-- **The F05 setting `S_m`**: `w_n = ⟨n⟩^{2(m-1)}`, `q_n = a_{m,n} = W_m(2πn)`. -/
def F05Setting (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0)
    (hM : 0 < β m) : RamerSetting :=
  RamerSetting.ofSobolevRates (finiteHierarchyRate38 m β)
    (rate_pos38 m β (by omega) hβ h0 hM) ((m - 1 : ℕ) : ℝ) (summable_tailRatio38 m β hm hβ h0 hM)

section Setting

variable (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0)
  (hM : 0 < β m)

theorem F05Setting_q (n : ℤ) :
    (F05Setting m β hm hβ h0 hM).q n = finiteWeightE02_38 m β (2 * Real.pi * n) := rfl

/-- `S_m.H = h^m` as a set, with norm² `2 Σ a_{m,n} |h_n|²`. -/
theorem F05Setting_cmWeight (n : ℤ) :
    (F05Setting m β hm hβ h0 hM).cmWeight n = 2 * finiteWeightE02_38 m β (2 * Real.pi * n) := rfl

/-- The coordinate preserving isometry `h^{m-1} = SobolevHilbert (m-1) ≃ₗᵢ[ℝ] S_m.E`. -/
def F05Equiv : SobolevHilbert ((m - 1 : ℕ) : ℝ) ≃ₗᵢ[ℝ] (F05Setting m β hm hβ h0 hM).E :=
  RamerSetting.ofSobolevRatesEquiv _ _ _ _

theorem coord_F05Equiv (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) (n : ℤ) :
    (F05Setting m β hm hβ h0 hM).coord n (F05Equiv m β hm hβ h0 hM x) =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n :=
  coord_ofWeightsEquiv _ _ _ _ x n

/-- `S_m.γ` is the project's F06 Gaussian `γ_m` (`gammaM38`), definitionally. -/
theorem F05Setting_γ : (F05Setting m β hm hβ h0 hM).γ = gammaM38 m β := rfl

theorem F05_memE_iff (z : ℤ → ℂ) :
    (F05Setting m β hm hβ h0 hM).memE z ↔
      Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) :=
  memE_ofWeights_iff _ _ _ _ (summable_tailRatio38 m β hm hβ h0 hM) z

/-- The realization of `S_m` agrees with F06's `gaussianRealization38` under `F05Equiv`. -/
theorem F05Equiv_realization (z : ℤ → ℂ) :
    F05Equiv m β hm hβ h0 hM (gaussianRealization38 m z) = (F05Setting m β hm hβ h0 hM).R z := by
  set S := F05Setting m β hm hβ h0 hM with hS
  by_cases hz : Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)
  · have hz' : S.memE z := (F05_memE_iff m β hm hβ h0 hM z).2 hz
    apply S.E_ext; intro n
    rw [coord_F05Equiv, S.coord_R hz']
    exact seqRealization_apply38 _ z hz n
  · have hz' : ¬ S.memE z := fun h => hz ((F05_memE_iff m β hm hβ h0 hM z).1 h)
    rw [S.R_of_not_memE hz']
    have : gaussianRealization38 m z = 0 := by
      simp [gaussianRealization38, seqRealization38, hz]
    rw [this]; exact (F05Equiv m β hm hβ h0 hM).map_zero

/-- `S_m.γE` is F06's `H^{m-1}` Gaussian law transported by `F05Equiv`. -/
theorem F05Setting_γE :
    (F05Setting m β hm hβ h0 hM).γE =
      ((gammaM38 m β).map (gaussianRealization38 m)).map (F05Equiv m β hm hβ h0 hM) := by
  unfold RamerSetting.γE
  rw [Measure.map_map (F05Equiv m β hm hβ h0 hM).continuous.measurable
    (measurable_gaussianRealization38)]
  congr 1
  funext z
  exact (F05Equiv_realization m β hm hβ h0 hM z).symm

/-- `incl : S_m.H → S_m.E` is coordinate preserving, i.e. it is the inclusion `h^m ⊂ h^{m-1}`
under `F05Equiv`. -/
theorem F05Equiv_symm_incl_coord (h : (F05Setting m β hm hβ h0 hM).H) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
        (F05Equiv m β hm hβ h0 hM).symm ((F05Setting m β hm hβ h0 hM).incl h)) n =
      (F05Setting m β hm hβ h0 hM).hcoord h n := by
  have h1 := coord_F05Equiv m β hm hβ h0 hM
    ((F05Equiv m β hm hβ h0 hM).symm ((F05Setting m β hm hβ h0 hM).incl h)) n
  rw [LinearIsometryEquiv.apply_symm_apply, RamerSetting.coord_incl] at h1
  exact h1.symm


/-! ### The `SobolevCarrier38` form of the bridge -/

/-- The same bridge with the project's coherent carrier `SobolevCarrier38 (m-1)`. -/
def F05EquivCarrier : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) ≃ₗᵢ[ℝ]
    (F05Setting m β hm hβ h0 hM).E where
  toFun x := F05Equiv m β hm hβ h0 hM (ofCarrier38 _ x)
  invFun y := toCarrier38 _ ((F05Equiv m β hm hβ h0 hM).symm y)
  map_add' x y := (F05Equiv m β hm hβ h0 hM).map_add (ofCarrier38 _ x) (ofCarrier38 _ y)
  map_smul' r x := (F05Equiv m β hm hβ h0 hM).map_smul r (ofCarrier38 _ x)
  left_inv x := (F05Equiv m β hm hβ h0 hM).symm_apply_apply (ofCarrier38 _ x)
  right_inv y := (F05Equiv m β hm hβ h0 hM).apply_symm_apply y
  norm_map' x := (F05Equiv m β hm hβ h0 hM).norm_map (ofCarrier38 _ x)

end Setting

/-! ### The instance of Ramer's theorem -/

section Instance

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0)
  (hM : 0 < β m)

/-- **Ramer's theorem for the F05 setting** (`S_m.E ≃ h^{m-1}`, `q_n = a_{m,n}`, `H = h^m`):
`RamerSetting.ramer_general` specialized to `S_m = F05Setting`. -/
theorem ramer_F05_instance
    (T : (F05Setting m β hm hβ h0 hM).E ≃ₜ (F05Setting m β hm hβ h0 hM).E)
    (K K' : (F05Setting m β hm hβ h0 hM).E → (F05Setting m β hm hβ h0 hM).H)
    (hT : ∀ x, T x = x + (F05Setting m β hm hβ h0 hM).incl (K x))
    (hTs : ∀ y, T.symm y = y + (F05Setting m β hm hβ h0 hM).incl (K' y))
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K') :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : (F05Setting m β hm hβ h0 hM).E, ∃ r > 0,
        ∃ (G : (F05Setting m β hm hβ h0 hM).E → (F05Setting m β hm hβ h0 hM).H)
          (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          (F05Setting m β hm hβ h0 hM).IsClosedDiv
            (fun z => G ((F05Setting m β hm hβ h0 hM).R z)) η) ∧
      (∀ (x₀ : (F05Setting m β hm hβ h0 hM).E) (r : ℝ)
          (G : (F05Setting m β hm hβ h0 hM).E → (F05Setting m β hm hβ h0 hM).H)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          (F05Setting m β hm hβ h0 hM).IsClosedDiv
            (fun z => G ((F05Setting m β hm hβ h0 hM).R z)) η →
          ∀ᵐ z ∂(F05Setting m β hm hβ h0 hM).γ,
            (F05Setting m β hm hβ h0 hM).R z ∈ ball x₀ r → δK z = η z) ∧
      let J : (F05Setting m β hm hβ h0 hM).E → ℝ := fun x =>
        |det2 ((F05Setting m β hm hβ h0 hM).hsDerivH K x)| *
          Real.exp (-(δK ((F05Setting m β hm hβ h0 hM).coordE x)) - ‖K x‖ ^ 2 / 2)
      (F05Setting m β hm hβ h0 hM).γE.map T.symm =
          (F05Setting m β hm hβ h0 hM).γE.withDensity (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J (F05Setting m β hm hβ h0 hM).γE ∧
      ∫ x, J x ∂(F05Setting m β hm hβ h0 hM).γE = 1 ∧
      TendstoInMeasure (F05Setting m β hm hβ h0 hM).γ
        (fun N z => finiteRamerDensity
          (fun v => v + (F05Setting m β hm hβ h0 hM).truncField K N v)
          ((F05Setting m β hm hβ h0 hM).headPt N z))
        atTop (fun z => J ((F05Setting m β hm hβ h0 hM).R z)) :=
  (F05Setting m β hm hβ h0 hM).ramer_general T K K' hT hTs hK hK'

end Instance

end NlsGge.Ramer.General
