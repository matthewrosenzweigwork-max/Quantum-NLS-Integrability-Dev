import QuantumNLS.AuditGapsS01Analytic
import QuantumNLS.UnitPhaseTransfer
import QuantumNLS.CartesianOccupationTransfer
import QuantumNLS.HierarchyFlow
import QuantumNLS.Def033AdjacentR24m

/-!
# AuditGapsS01Level: level-`M` estimates for R-10EE6421 `lem:audit-gaps`

PRINTED SOURCE: `source-text/chapters/core/weighted_actions_and_same_gauge_dynamics.tex`, lines 261-294
(`lem:audit-gaps`, `\ReportID{R-10EE6421}`), printed proof lines 270-294.

This module transports the abstract `ℓ²` estimates of `AuditGapsS01Analytic` to the actual objects of the
campaign at ONE particle number `M`, for an ARBITRARY complete basis `b`, unit-phase gauge `g` and vector
`ψ` (no use of any dynamic-gauge, hierarchy or DEF-033 claim here; those enter only in the final module).

* the printed step "The exact diagonal multiplier makes its square
  `E_{p_{N,u}}[1_{m_a ≥ 1} |e^{it(Λ_N(m-e_a+e_b)-Λ_N(m)-δ)} - 1|²]`" is the conjugation of
  `UnitPhaseTransfer.physical` (the gauged pullback of the unit partial shift `W^q`) and of the actual
  quantum flow `HierarchyFlow.quantumFlow` by the literal gauged coefficient isometry
  `CartesianOccupationTransfer.coordinates b g`, in which the flow is the diagonal propagator
  `e^{-itΛ}` (`Uc_e`) and `W^q` the unit shift `auxiliary` (`aux_e_mem`, `aux_e_notMem`);
* `level_gap_mass`: the Born mass of the set `{m_a ≥ 1, |Λ(m-e_a+e_b) - Λ(m) - δ| ≥ η}` is at most
  `8 ε₀² / k₀`, given the dynamic residuals of the phase symbol on `-1 ≤ s ≤ 1` and the static residual,
  both `≤ ε₀`;
* `level_conc`: "The omitted donor boundary has probability tending to zero by action concentration",
  as the mass of `{m_a = 0}` bounded by the strong Cartesian symbol residual at `a = b` (the diagonal
  `E^q_{N,aa}` multiplies the coefficient of `m` by `m_a / N`);
* `originalBorn_apply_real`, `born_gap_le`, `born_conc_le`: the same bounds as statements about the original
  Born measure `Def033CoreR24m.originalBorn` at particle number `N + 1`.

No acceptance claim.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
open MeasureTheory

namespace QuantumNLS.AuditGapsS01Level
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
open QuantumNLS.BetheSpectralCharges QuantumNLS.HierarchyFlow
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def033CoreR24m
open QuantumNLS.Occupation (Arr DonorOK shiftArr)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The joint time vector of one active charge order `r`: `t_r = s`, all other components `0`. -/
def tv (r : ℕ) (s : ℝ) : ℕ → ℝ := fun i => if i = r then s else 0

theorem jointSymbol_tv {M : ℕ} (κ : ℝ) (r : ℕ) (s : ℝ) (m : MArr M) :
    jointSymbol L M κ {r} (tv r s) m = s * eigenvalue L M (κ / M) r m := by
  simp [jointSymbol, tv]

/-! ### The gauged coordinates of the flow -/

theorem coords_apply {M : ℕ} (b : BetheBasis L M) (g : Gauge) (ψ : HN L M) (m : MArr M) :
    CartesianOccupationTransfer.coordinates b g ψ (marrArr M m) =
      conj (g M m).val * ⟪b m, ψ⟫_ℂ := by
  show (occupationCoefficient (gaugedBasis b g) ψ) (marrArr M m) = _
  rw [occupationCoefficient_apply, gaugedBasis_apply, inner_smul_left]

theorem norm_coords {M : ℕ} (b : BetheBasis L M) (g : Gauge) (ψ : HN L M) (m : MArr M) :
    ‖CartesianOccupationTransfer.coordinates b g ψ (marrArr M m)‖ = ‖⟪b m, ψ⟫_ℂ‖ := by
  rw [coords_apply, norm_mul, Complex.norm_conj, (g M m).property, one_mul]

theorem coords_flow {M : ℕ} (b : BetheBasis L M) (g : Gauge) (r : ℕ) (s : ℝ) (ψ : HN L M)
    (m : MArr M) :
    CartesianOccupationTransfer.coordinates b g (quantumFlow b κ {r} (tv r s) ψ) (marrArr M m) =
      DiagonalMultiplier.phase (fun k => eigenvalue L M (κ / M) r ((marrArr M).symm k)) s
          (marrArr M m) *
        CartesianOccupationTransfer.coordinates b g ψ (marrArr M m) := by
  rw [coords_apply, coords_apply, quantumFlow_coord]
  simp only [DiagonalMultiplier.phase, Finset.sum_singleton, tv, if_true, Equiv.symm_apply_apply]
  ring

/-- The quantum flow of order `r` in the gauged coordinates. -/
def Uc {M : ℕ} (b : BetheBasis L M) (g : Gauge) (κ : ℝ) (r : ℕ) (s : ℝ) :
    OccupationHilbert.H M →L[ℂ] OccupationHilbert.H M :=
  ((CartesianOccupationTransfer.coordinates b g).symm.trans
    ((quantumFlow b κ {r} (tv r s)).trans
      (CartesianOccupationTransfer.coordinates b g))).toContinuousLinearEquiv.toContinuousLinearMap

theorem Uc_coords {M : ℕ} (b : BetheBasis L M) (g : Gauge) (κ : ℝ) (r : ℕ) (s : ℝ) (ψ : HN L M) :
    Uc b g κ r s (CartesianOccupationTransfer.coordinates b g ψ) =
      CartesianOccupationTransfer.coordinates b g (quantumFlow b κ {r} (tv r s) ψ) := by
  simp [Uc]

theorem Uc_e {M : ℕ} (b : BetheBasis L M) (g : Gauge) (κ : ℝ) (r : ℕ) (s : ℝ) (k : Arr M) :
    Uc b g κ r s (DiagonalMultiplier.e k) =
      DiagonalMultiplier.phase (fun k => eigenvalue L M (κ / M) r ((marrArr M).symm k)) s k •
        DiagonalMultiplier.e k := by
  ext j
  obtain ⟨m, rfl⟩ := (marrArr M).surjective j
  have h1 := Uc_coords b g κ r s ((CartesianOccupationTransfer.coordinates b g).symm
    (DiagonalMultiplier.e k))
  rw [LinearIsometryEquiv.apply_symm_apply] at h1
  rw [h1, coords_flow, LinearIsometryEquiv.apply_symm_apply]
  by_cases hk : marrArr M m = k
  · subst hk
    simp
  · simp [DiagonalMultiplier.e_apply, hk]

theorem flow_zero {M : ℕ} (b : BetheBasis L M) (g : Gauge) (κ : ℝ) (r : ℕ) (ψ : HN L M) :
    quantumFlow b κ {r} (tv r 0) ψ = ψ := by
  apply (CartesianOccupationTransfer.coordinates b g).injective
  ext j
  obtain ⟨m, rfl⟩ := (marrArr M).surjective j
  rw [coords_flow]
  simp [DiagonalMultiplier.phase]

/-! ### The unit shift in the coordinates -/

/-- The admissible donor domain `m_a ≥ 1`. -/
def Dset (M : ℕ) (a : ℤ) : Set (Arr M) := {m | DonorOK a m.1}

/-- The partial shift `m ↦ m - e_a + e_c` on occupied donors (identity elsewhere, unused there). -/
def sig (M : ℕ) (a c : ℤ) (m : Arr M) : Arr M :=
  if hd : DonorOK a m.1 then shiftArr a c m hd else m

theorem sig_injOn (M : ℕ) (a c : ℤ) : Set.InjOn (sig M a c) (Dset M a) := by
  intro m hm m' hm' h
  have hm1 : DonorOK a m.1 := hm
  have hm2 : DonorOK a m'.1 := hm'
  simp only [sig, dif_pos hm1, dif_pos hm2] at h
  exact Subtype.ext (Occupation.shift_injOn hm1 hm2 (congrArg Subtype.val h))

theorem aux_e_mem (M : ℕ) (a c : ℤ) (m : Arr M) (hm : m ∈ Dset M a) :
    UnitPhaseTransfer.auxiliary M a c (DiagonalMultiplier.e m) =
      (1 : ℂ) • DiagonalMultiplier.e (sig M a c m) := by
  have hm1 : DonorOK a m.1 := hm
  unfold DiagonalMultiplier.e
  rw [UnitPhaseTransfer.auxiliary_basis, dif_pos hm1, one_smul]
  simp [sig, dif_pos hm1]

theorem aux_e_notMem (M : ℕ) (a c : ℤ) (m : Arr M) (hm : m ∉ Dset M a) :
    UnitPhaseTransfer.auxiliary M a c (DiagonalMultiplier.e m) = 0 := by
  have hm1 : ¬ DonorOK a m.1 := hm
  unfold DiagonalMultiplier.e
  rw [UnitPhaseTransfer.auxiliary_basis, dif_neg hm1]

/-- The diagonal Cartesian transfer `E_{N,aa}` multiplies the `m`-coefficient by `m_a / N`. -/
theorem E_diag_e {M : ℕ} (a : ℤ) (k : Arr M) :
    OccupationHilbert.E M a a (DiagonalMultiplier.e k) =
      ((((k.1 a : ℕ) : ℝ) / M : ℝ) : ℂ) • DiagonalMultiplier.e k := by
  unfold DiagonalMultiplier.e
  rw [OccupationHilbert.E_single]
  by_cases hd : DonorOK a k.1
  · rw [dif_pos hd]
    have hs : shiftArr a a k hd = k := Subtype.ext (Occupation.shift_self hd)
    rw [hs, Occupation.coef_diag, ← lp.single_smul]
    simp
  · rw [dif_neg hd]
    have h0 : k.1 a = 0 := by
      have : ¬ 1 ≤ k.1 a := hd
      omega
    simp [h0]

/-! ### Level estimates -/

/-- **Level gap mass.** The Born-type mass `∑ ‖⟪b m, ψ⟫‖²` of the occupied-donor labels whose adjacent
difference is at least `η` away from `δ` is at most `8 ε₀² / k₀`, when the phase symbol residuals of
the flowed vector on `-1 ≤ s ≤ 1` and of `ψ` itself are at most `ε₀`, the dynamic symbol being
`e^{isδ}` times the static one. `k₀` is any positive lower bound of the kernel `k` on `|y| ≥ η`. -/
theorem level_gap_mass {M : ℕ} (b : BetheBasis L M) (g : Gauge) (r : ℕ) (a c : ℤ) (ψ : HN L M)
    (τ : ℂ) (δ ε₀ η k₀ : ℝ) (hk₀ : 0 < k₀)
    (hk : ∀ y : ℝ, η ≤ |y| → k₀ ≤ AuditGapsS01Analytic.kk y)
    (hdyn : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      ‖UnitPhaseTransfer.physical b g a c (quantumFlow b κ {r} (tv r s) ψ) -
          (DiagonalMultiplier.rot (s * δ) * τ) • quantumFlow b κ {r} (tv r s) ψ‖ ≤ ε₀)
    (hstat : ‖UnitPhaseTransfer.physical b g a c ψ - τ • ψ‖ ≤ ε₀) :
    ∑' m : MArr M, {m : MArr M | ∃ h : DonorOK a (marrArr M m).1,
        η ≤ |adjacentDifference L κ M r a c m h - δ|}.indicator
      (fun m => ‖⟪b m, ψ⟫_ℂ‖ ^ 2) m ≤ 8 * ε₀ ^ 2 / k₀ := by
  set x := CartesianOccupationTransfer.coordinates b g ψ with hx
  let Λ : Arr M → ℝ := fun k => eigenvalue L M (κ / M) r ((marrArr M).symm k)
  set S : Set (MArr M) := {m : MArr M | ∃ h : DonorOK a (marrArr M m).1,
        η ≤ |adjacentDifference L κ M r a c m h - δ|} with hS
  let Zb : Set (Arr M) := {k | (marrArr M).symm k ∈ S}
  have hU : ∀ s k, Uc b g κ r s (DiagonalMultiplier.e k) =
      DiagonalMultiplier.phase Λ s k • DiagonalMultiplier.e k := fun s k => Uc_e b g κ r s k
  have hT : ∀ k ∈ Dset M a, UnitPhaseTransfer.auxiliary M a c (DiagonalMultiplier.e k) =
      (fun _ : Arr M => (1 : ℂ)) k • DiagonalMultiplier.e (sig M a c k) :=
    fun k hk' => aux_e_mem M a c k hk'
  have hT0 : ∀ k, k ∉ Dset M a → UnitPhaseTransfer.auxiliary M a c (DiagonalMultiplier.e k) = 0 :=
    fun k hk' => aux_e_notMem M a c k hk'
  have hdyn' : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      ‖UnitPhaseTransfer.auxiliary M a c (Uc b g κ r s x) -
          (DiagonalMultiplier.rot (s * δ) * τ) • Uc b g κ r s x‖ ≤ ε₀ := by
    intro s hs
    have h := hdyn s hs
    rw [hx, Uc_coords, ← UnitPhaseTransfer.physical_coordinates, ← map_smul, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact h
  have hstat' : ‖UnitPhaseTransfer.auxiliary M a c x - τ • x‖ ≤ ε₀ := by
    rw [hx, ← UnitPhaseTransfer.physical_coordinates, ← map_smul, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact hstat
  have hZb : ∀ k ∈ Zb, k ∈ Dset M a ∧ η ≤ |Λ (sig M a c k) - Λ k - δ| := by
    intro k hk'
    obtain ⟨m, rfl⟩ := (marrArr M).surjective k
    have hm : m ∈ S := by simpa [Zb] using hk'
    obtain ⟨h, hη⟩ := hm
    refine ⟨h, ?_⟩
    have hs : sig M a c (marrArr M m) = shiftArr a c (marrArr M m) h := dif_pos h
    show η ≤ |eigenvalue L M (κ / M) r ((marrArr M).symm (sig M a c (marrArr M m))) -
      eigenvalue L M (κ / M) r ((marrArr M).symm (marrArr M m)) - δ|
    rw [hs, Equiv.symm_apply_apply]
    exact hη
  have key := AuditGapsS01Analytic.bad_mass Λ (fun s => Uc b g κ r s) (sig M a c) (Dset M a)
    (fun _ => (1 : ℂ)) (UnitPhaseTransfer.auxiliary M a c) hU (sig_injOn M a c) hT hT0
    (fun _ _ => norm_one) x τ δ ε₀ hdyn' hstat' η k₀ hk₀ hk Zb hZb
  have hsum : ∑' m : MArr M, S.indicator (fun m => ‖⟪b m, ψ⟫_ℂ‖ ^ 2) m =
      ∑' k : Arr M, Zb.indicator (fun k => ‖x k‖ ^ 2) k := by
    rw [← (marrArr M).tsum_eq]
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ S
    · have hmz : marrArr M m ∈ Zb := by simpa [Zb] using hm
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hmz, hx, norm_coords]
    · have hmz : marrArr M m ∉ Zb := by simpa [Zb] using hm
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hmz]
  rw [hsum]
  exact key

/-- **Level concentration.** The mass of the empty-donor labels `{m_a = 0}` is at most `ε₁² / ‖c‖²`,
where `ε₁` bounds the strong Cartesian residual `‖E^q_{N,aa} ψ - c ψ‖`. -/
theorem level_conc {M : ℕ} (b : BetheBasis L M) (g : Gauge) (a : ℤ) (ψ : HN L M) (c : ℂ) (ε₁ : ℝ)
    (h : ‖CartesianOccupationTransfer.physical b g a a ψ - c • ψ‖ ≤ ε₁) :
    ‖c‖ ^ 2 * ∑' m : MArr M, {m : MArr M | ¬ DonorOK a (marrArr M m).1}.indicator
      (fun m => ‖⟪b m, ψ⟫_ℂ‖ ^ 2) m ≤ ε₁ ^ 2 := by
  set x := CartesianOccupationTransfer.coordinates b g ψ with hx
  let S : Set (MArr M) := {m : MArr M | ¬ DonorOK a (marrArr M m).1}
  let Z : Set (Arr M) := {k | ¬ DonorOK a k.1}
  have hZ : ∀ k ∈ Z, (fun k : Arr M => ((((k.1 a : ℕ) : ℝ) / M : ℝ) : ℂ)) k = 0 := by
    intro k hk
    have hk1 : ¬ DonorOK a k.1 := hk
    have h0 : k.1 a = 0 := by
      have : ¬ 1 ≤ k.1 a := hk1
      omega
    simp [h0]
  have hE : ∀ k : Arr M, OccupationHilbert.E M a a (DiagonalMultiplier.e k) =
      (fun k : Arr M => ((((k.1 a : ℕ) : ℝ) / M : ℝ) : ℂ)) k • DiagonalMultiplier.e k :=
    fun k => E_diag_e a k
  have hh : ‖OccupationHilbert.E M a a x - c • x‖ ≤ ε₁ := by
    rw [hx, ← CartesianOccupationTransfer.physical_coordinates, ← map_smul, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact h
  have key := AuditGapsS01Analytic.diag_conc (OccupationHilbert.E M a a)
    (fun k : Arr M => ((((k.1 a : ℕ) : ℝ) / M : ℝ) : ℂ)) hE Z hZ c x ε₁ hh
  have hsum : ∑' m : MArr M, S.indicator (fun m => ‖⟪b m, ψ⟫_ℂ‖ ^ 2) m =
      ∑' k : Arr M, Z.indicator (fun k => ‖x k‖ ^ 2) k := by
    rw [← (marrArr M).tsum_eq]
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ S
    · have hmz : marrArr M m ∈ Z := hm
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hmz, hx, norm_coords]
    · have hmz : marrArr M m ∉ Z := hm
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hmz]
  rw [hsum]
  exact key

/-! ### The original Born measure -/

theorem originalBorn_apply_real {hκ : 0 < κ} (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
    (N : ℕ) (S : Set (MArr (N + 1))) :
    originalBorn hκ u hu N S = ENNReal.ofReal (∑' m, S.indicator
      (bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ)
        u) m) := by
  unfold originalBorn QuantumNLS.EmpiricalRapidity.bornMeasure
  rw [PMF.toMeasure_apply_eq_tsum]
  have hsum := (summable_bornLaw
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ)
    u).indicator S
  rw [ENNReal.ofReal_tsum_of_nonneg (fun m => Set.indicator_nonneg
    (fun _ _ => bornLaw_nonneg _ u _) m) hsum]
  refine tsum_congr fun m => ?_
  by_cases hm : m ∈ S <;> simp [Set.indicator, hm, bornPMF_apply]

/-- The Born-measure form of `level_gap_mass` at particle number `N + 1` for the product preparation. -/
theorem born_gap_le {hκ : 0 < κ} (g : Gauge) (N : ℕ) (r : ℕ) (a c : ℤ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
    (τ : ℂ) (δ ε₀ η k₀ : ℝ) (hk₀ : 0 < k₀)
    (hk : ∀ y : ℝ, η ≤ |y| → k₀ ≤ AuditGapsS01Analytic.kk y)
    (hdyn : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      ‖UnitPhaseTransfer.physical
          (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) g a c
          (quantumFlow (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1)
            (by omega) hκ) κ {r} (tv r s) (productVec L (N + 1) u)) -
          (DiagonalMultiplier.rot (s * δ) * τ) •
            quantumFlow (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1)
              (by omega) hκ) κ {r} (tv r s) (productVec L (N + 1) u)‖ ≤ ε₀)
    (hstat : ‖UnitPhaseTransfer.physical
          (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) g a c
          (productVec L (N + 1) u) - τ • productVec L (N + 1) u‖ ≤ ε₀) :
    originalBorn hκ u hu N {m | ∃ h : DonorOK a (marrArr (N + 1) m).1,
        η ≤ |adjacentDifference L κ (N + 1) r a c m h - δ|} ≤ ENNReal.ofReal (8 * ε₀ ^ 2 / k₀) := by
  rw [originalBorn_apply_real]
  exact ENNReal.ofReal_le_ofReal (level_gap_mass
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) g r a c
    (productVec L (N + 1) u) τ δ ε₀ η k₀ hk₀ hk hdyn hstat)

/-- The Born-measure form of `level_conc` at particle number `N + 1` for the product preparation. -/
theorem born_conc_le {hκ : 0 < κ} (g : Gauge) (N : ℕ) (a : ℤ)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (c : ℂ) (hc : c ≠ 0) (ε₁ : ℝ)
    (h : ‖CartesianOccupationTransfer.physical
          (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) g a a
          (productVec L (N + 1) u) - c • productVec L (N + 1) u‖ ≤ ε₁) :
    originalBorn hκ u hu N {m | ¬ DonorOK a (marrArr (N + 1) m).1} ≤
      ENNReal.ofReal (ε₁ ^ 2 / ‖c‖ ^ 2) := by
  rw [originalBorn_apply_real]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < ‖c‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  exact level_conc
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ) g a
    (productVec L (N + 1) u) c ε₁ h

end QuantumNLS.AuditGapsS01Level

#print axioms QuantumNLS.AuditGapsS01Level.coords_flow
#print axioms QuantumNLS.AuditGapsS01Level.Uc_e
#print axioms QuantumNLS.AuditGapsS01Level.flow_zero
#print axioms QuantumNLS.AuditGapsS01Level.E_diag_e
#print axioms QuantumNLS.AuditGapsS01Level.level_gap_mass
#print axioms QuantumNLS.AuditGapsS01Level.level_conc
#print axioms QuantumNLS.AuditGapsS01Level.originalBorn_apply_real
#print axioms QuantumNLS.AuditGapsS01Level.born_gap_le
#print axioms QuantumNLS.AuditGapsS01Level.born_conc_le
