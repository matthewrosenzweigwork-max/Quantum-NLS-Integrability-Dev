import QuantumNLS.RootIndexedMasses
import QuantumNLS.Prop026Bound
import QuantumNLS.LabelWeakJointLimit
import QuantumNLS.Prop009ProbeDev

/-! R-E6DFC650, ROOT_occupation_limit.tex:14: the deterministic half (the printed
"deterministic sequence argument" and its uniform consequence).  The weak joint limit of
the pairs (q_j, n_j) is the read-only PROP-002 module `LabelWeakJointLimit`
(`weak_joint_limit_DEF043`, DEF-043 binding `Prop026Bound.scalarCuts` of the physical
measure); the indexed masses are the read-only `RootIndexedMasses` (R-950BFB30) /
`RootIndexedPhase` (R-2EAD2BB6) data.  New here: the identification of the second
marginal of the graph measure with the indexed masses, the l1 upgrade, and the uniform
form over a weak neighbourhood.  No hypothesis beyond those of the printed theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.RootOccupationDet
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.BetheLabels (MArr arrRoots labelsEquivArr correctedInt)
open PhysicalTensor (L2T)

/-! ### 1. Scheffe: pointwise convergence of probability vectors gives l1 convergence -/

theorem scheffe_l1 (a : ℕ → ℤ → ℝ) (b : ℤ → ℝ) (ha0 : ∀ k n, 0 ≤ a k n) (hb0 : ∀ n, 0 ≤ b n)
    (hsa : ∀ k, HasSum (a k) 1) (hsb : HasSum b 1)
    (hpt : ∀ n, Tendsto (fun k => a k n) atTop (nhds (b n))) :
    Tendsto (fun k => ∑' n, |a k n - b n|) atTop (nhds 0) := by
  have hmin : Tendsto (fun k => ∑' n, min (a k n) (b n)) atTop (nhds (∑' n, b n)) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun k n => min (a k n) (b n))
      (g := b) (bound := b) hsb.summable (fun n => by
        have := (hpt n).min (tendsto_const_nhds (x := b n))
        simpa using this)
      (Eventually.of_forall fun k n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (ha0 k n) (hb0 n))]; exact min_le_right _ _)
    exact this
  rw [hsb.tsum_eq] at hmin
  have e : ∀ k, ∑' n, |a k n - b n| = 2 - 2 * ∑' n, min (a k n) (b n) := by
    intro k
    have hsm : Summable (fun n => min (a k n) (b n)) :=
      Summable.of_nonneg_of_le (fun n => le_min (ha0 k n) (hb0 n)) (fun n => min_le_right _ _)
        hsb.summable
    have h1 : ∀ n, |a k n - b n| = a k n + b n - 2 * min (a k n) (b n) := by
      intro n
      rcases le_total (a k n) (b n) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp_rw [h1]
    rw [((hsa k).summable.add hsb.summable).tsum_sub (hsm.mul_left 2),
      (hsa k).summable.tsum_add hsb.summable,
      (hsa k).tsum_eq, hsb.tsum_eq, tsum_mul_left]
    ring
  simp_rw [e]
  have := (hmin.const_mul 2).const_sub 2
  simpa using this

/-! ### 2. Occupation proportions of an on-shell configuration -/

variable {L κ : ℝ} [Fact (0 < L)]

/-- `m_k / N` for the integer labels `n_j` of an on-shell configuration. -/
def occ {N : ℕ} (B : OnShellBethe L κ N) (k : ℤ) : ℝ :=
  (N : ℝ)⁻¹ * ((Finset.univ.filter fun j => B.n j = k).card : ℝ)

theorem occ_nonneg {N : ℕ} (B : OnShellBethe L κ N) (k : ℤ) : 0 ≤ occ B k := by
  unfold occ; positivity

theorem hasSum_occ {N : ℕ} (hN : 0 < N) (B : OnShellBethe L κ N) : HasSum (occ B) 1 := by
  classical
  have hfin : ∀ k ∉ Finset.univ.image B.n, occ B k = 0 := by
    intro k hk
    unfold occ
    have : (Finset.univ.filter fun j => B.n j = k) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      exact hk (Finset.mem_image.2 ⟨j, Finset.mem_univ _, h⟩)
    simp [this]
  have hs : HasSum (occ B) (∑ k ∈ Finset.univ.image B.n, occ B k) :=
    hasSum_sum_of_ne_finset_zero hfin
  convert hs using 1
  unfold occ
  rw [← Finset.mul_sum]
  have h := Finset.card_eq_sum_card_image B.n (Finset.univ : Finset (Fin N))
  have h' : ((N : ℕ) : ℝ) = ∑ a ∈ Finset.univ.image B.n,
      ((Finset.univ.filter fun x => B.n x = a).card : ℝ) := by
    have h2 : (Finset.univ : Finset (Fin N)).card = N := by simp
    rw [h2] at h
    exact_mod_cast h
  rw [← h']
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The occupation of label `k` is the `ℝ × {k}` mass of the joint empirical measure. -/
theorem jointP_slice {N : ℕ} (hN : 0 < N) (B : OnShellBethe L κ N) (k : ℤ) :
    (((jointP B hN) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) : ℝ≥0) : ℝ) = occ B k := by
  have hms : MeasurableSet ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) :=
    MeasurableSet.univ.prod (measurableSet_singleton k)
  have h1 := ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (jointP B hN) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ))
  have h2 : ((jointP B hN : Measure (ℝ × ℤ))) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) =
      (N : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun j => B.n j = k).card : ℝ≥0∞) := by
    change emp (pts B) _ = _
    classical
    rw [emp_apply _ hms]
    congr 3
    ext j
    simp [pts]
  have h3 : (((jointP B hN) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) : ℝ≥0) : ℝ) =
      (((jointP B hN) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) : ℝ≥0∞)).toReal := by
    rw [ENNReal.coe_toReal]
  rw [h3, h1, h2]
  unfold occ
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp

/-- The array bridge: every `m ∈ 𝓜_N` carries an on-shell configuration whose roots are
`arrRoots L (κ/N) m` and whose label counts are the occupations `m_k`. -/
theorem onShell_arr (hL : 0 < L) {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) :
    ∃ B : OnShellBethe L κ N, B.q = arrRoots L (κ / N) m ∧
      ∀ k : ℤ, ((m.1 k : ℕ) : ℝ) = ((Finset.univ.filter fun j => B.n j = k).card : ℝ) := by
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN)
  set ℓ := labelsEquivArr.symm m with hℓ
  have hs : BetheAdmission.Solves L (κ / (N : ℝ)) (correctedInt ℓ)
      (BetheSmooth.roots L (correctedInt ℓ) (κ / (N : ℝ))) :=
    BetheSmooth.roots_solves hL hc _
  have hq : StrictMono (BetheSmooth.roots L (correctedInt ℓ) (κ / (N : ℝ))) :=
    BetheLabels.roots_strictMono_labels hL hc ℓ
  have hbose : RootContraction.BoseBethe L (κ / (N : ℝ)) (correctedInt ℓ)
      (BetheSmooth.roots L (correctedInt ℓ) (κ / (N : ℝ))) := by
    refine (RootContraction.boseBethe_iff_log (L := L) hc hq (correctedInt ℓ)).2 (fun j => ?_)
    have h1 := hs j
    have h2 : RootContraction.Tmap L (κ / (N : ℝ))
        (BetheSmooth.roots L (correctedInt ℓ) (κ / (N : ℝ))) j =
        BetheAdmission.logMap L (κ / (N : ℝ))
          (BetheSmooth.roots L (correctedInt ℓ) (κ / (N : ℝ))) j := by
      rw [BetheAdmission.logMap_erase]; rfl
    rw [h2, h1]
    unfold BetheAdmission.quantumNumbers
    ring
  refine ⟨⟨BetheSmooth.roots L (correctedInt ℓ) (κ / (N : ℝ)), correctedInt ℓ, hq,
    BetheLabels.correctedInt_monotone ℓ, fun j => hbose j⟩, rfl, fun k => ?_⟩
  have h := BetheLabels.labelsEquivArr_apply ℓ k
  rw [hℓ, Equiv.apply_symm_apply] at h
  rw [h]

/-! ### 3. The second marginal of the graph measure is the indexed masses -/

theorem mass_eq_fiber (hκ : 0 < κ) (u : L2T L) {n : ℝ → ℤ}
    (hn : ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u),
      (n t : ℝ) = indexLabel L κ (Prop026Bound.reG hκ u) t) (k : ℤ) :
    (RootIndexedMasses.masses hκ u).1 k =
      ((PhysicalQuantumMeasure.measure hκ u) (n ⁻¹' {k})).toReal := by
  rw [(RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).1 k]
  congr 1
  symm
  apply measure_congr
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hn] with t ht
  rw [Prop026Bound.label_eq] at ht
  have hpi := Real.pi_pos
  have hθ : RootIndexedPhase.theta hκ u t = (n t : ℝ) * Real.pi := ((eq_div_iff hpi.ne').mp ht).symm
  have e1 : RootIndexedPhase.separator hκ u (k - 1) < t ↔
      (((k - 1 : ℤ) : ℝ) + 1 / 2) * Real.pi < RootIndexedPhase.theta hκ u t :=
    (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff t (k - 1)
  have e2 : t < RootIndexedPhase.separator hκ u k ↔
      RootIndexedPhase.theta hκ u t < ((k : ℝ) + 1 / 2) * Real.pi :=
    (PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff t k
  simp only [mem_preimage, mem_singleton_iff, mem_Ioo]
  rw [e1, e2, hθ]
  push_cast
  constructor
  · intro h
    rw [h]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have a1 : (k : ℝ) - 1 / 2 < (n t : ℝ) := by
      by_contra hc
      push Not at hc
      nlinarith
    have a2 : (n t : ℝ) < (k : ℝ) + 1 / 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    have b1 : k - 1 < n t := by
      have : ((k - 1 : ℤ) : ℝ) < (n t : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have b2 : n t < k + 1 := by
      have : (n t : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega

/-! ### 4. Deterministic sequences -/

/-- Printed deterministic sequence argument: if `ν_N ⇀ μ_u` along on-shell configurations
then the occupation vectors converge in `ℓ¹` to the indexed masses. -/
theorem occ_tendsto_seq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u)
    {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} (B : ∀ k, OnShellBethe L κ (N k))
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop) :
    Tendsto (fun k => ∑' n, |occ (B k) n - (RootIndexedMasses.masses hκ u).1 n|)
      atTop (𝓝 0) := by
  set S := Prop026Bound.scalarCuts hκ u hu with hS
  have hμS : (μ : Measure ℝ) = S.μ := hμ
  obtain ⟨⟨n, hnm, hnI⟩, hlim⟩ := weak_joint_limit_DEF043 S hconv hμS hNtop
  have hj := hlim n hnI
  have hcl : ∀ k : ℤ, IsClopen ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) := fun k =>
    isClopen_univ.prod (isClopen_discrete _)
  have hpt : ∀ k : ℤ, Tendsto (fun i => occ (B i) k) atTop
      (𝓝 ((RootIndexedMasses.masses hκ u).1 k)) := by
    intro k
    have hfr : (graphP μ n) (frontier ((univ : Set ℝ) ×ˢ ({k} : Set ℤ))) = 0 := by
      rw [(hcl k).frontier_eq]; simp
    have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hj hfr
    have h2 := (NNReal.tendsto_coe.2 h1)
    have h3 : ∀ i, (((jointP (B i) (hN i)) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) : ℝ≥0) : ℝ) =
        occ (B i) k := fun i => jointP_slice (hN i) (B i) k
    simp_rw [h3] at h2
    convert h2 using 2
    have hms : MeasurableSet ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) :=
      MeasurableSet.univ.prod (measurableSet_singleton k)
    have hmeas : Measurable (fun t : ℝ => (t, n t)) := measurable_id.prodMk hnm
    have e1 := ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (graphP μ n) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ))
    rw [graphP_toMeasure, Measure.map_apply hmeas hms] at e1
    have e2 : (fun t : ℝ => (t, n t)) ⁻¹' ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) = n ⁻¹' {k} := by
      ext t; simp
    rw [e2, hμ] at e1
    have e3 : ((((graphP μ n) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) : ℝ≥0) : ℝ)) =
        (((graphP μ n) ((univ : Set ℝ) ×ˢ ({k} : Set ℤ)) : ℝ≥0∞)).toReal := by
      rw [ENNReal.coe_toReal]
    rw [e3, e1]
    exact mass_eq_fiber hκ u hnI k
  have hcl' := RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  have hsb : HasSum (fun k => (RootIndexedMasses.masses hκ u).1 k) 1 := by
    have := hcl'.2.2.1.hasSum
    rwa [hcl'.2.2.2.1, hu, one_pow] at this
  exact scheffe_l1 (fun i k => occ (B i) k) (fun k => (RootIndexedMasses.masses hκ u).1 k)
    (fun i k => occ_nonneg _ _) hcl'.2.1 (fun i => hasSum_occ (hN i) (B i)) hsb hpt

/-! ### 5. The uniform form over a weak neighbourhood -/

theorem occ_uniform (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
      rootP B hN ∈ U →
        ∑' n, |occ B n - (RootIndexedMasses.masses hκ u).1 n| < ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨V, hV⟩ := (𝓝 μ).exists_antitone_basis
  have hpick : ∀ k : ℕ, ∃ N : ℕ, ∃ hN : 0 < N, k + 1 ≤ N ∧ ∃ B : OnShellBethe L κ N,
      rootP B hN ∈ V k ∧ ε ≤ ∑' n, |occ B n - (RootIndexedMasses.masses hκ u).1 n| := by
    intro k
    obtain ⟨N, hN, hkN, B, hB, hle⟩ := hcon (V k) (hV.1.mem_of_mem trivial) (k + 1)
    exact ⟨N, hN, hkN, B, hB, hle⟩
  choose Nk hNk hkN Bk hBk hle using hpick
  have hconv : Tendsto (fun k => rootP (Bk k) (hNk k)) atTop (𝓝 μ) := hV.tendsto hBk
  have hNtop : Tendsto Nk atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hkN k)) tendsto_id
  have ht := occ_tendsto_seq hκ u hu hμ Bk hconv hNtop
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact absurd (hle k) (not_le.2 hk)

end QuantumNLS.RootOccupationDet
#print axioms QuantumNLS.RootOccupationDet.scheffe_l1
#print axioms QuantumNLS.RootOccupationDet.hasSum_occ
#print axioms QuantumNLS.RootOccupationDet.jointP_slice
#print axioms QuantumNLS.RootOccupationDet.onShell_arr
#print axioms QuantumNLS.RootOccupationDet.mass_eq_fiber
#print axioms QuantumNLS.RootOccupationDet.occ_tendsto_seq
#print axioms QuantumNLS.RootOccupationDet.occ_uniform
