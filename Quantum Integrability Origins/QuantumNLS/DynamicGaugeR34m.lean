import QuantumNLS.DynamicGaugePhysicalR34m
import QuantumNLS.DynamicGaugeMixedR34m

/-! Dynamic comparison for the same retargeted gauge, R-8362E5EB.
The auxiliary pair gauge is used in the proof of the phase convergence. -/

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section

open Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace QuantumNLS.DynamicGaugeR34m

open ReconstructionR33m (w flows TimeBox RD8362E5EBInput)
open ActualModelTargetR53a (HigherFlows)
open Def033HierarchyR24m (Smooth physical)
open DynamicGaugePhysicalR34m DynamicGaugeMixedR34m
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open RetargetEdgeR48b (J residual_inCoefficients inCoefficients_adjoint graded_polar_bounds)
open RetargetWeightsR48b (cartesian cartesian_diag cartesian_adjoint cartesian_residual)
open RetargetCellR48b (pairPhase pair_factor pairPhase_eq_printed phase_reverse)
open DynSeedInputR47b (classicalOrbit quantumOrbit)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed seed lemma keeps the whole full-torus antecedent and
supplies both residuals and the exact grading with a time-independent seed. -/
def R300B8640Input (hκ : 0 < κ) (F : HigherFlows L κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ), a ≠ b →
      DynSeedInputR47b.FullTorus hκ F u R → DynSeedR47b.SeedStatement hκ F u R lo hi a b

/-- Strong symbols on a sequence of physical sectors. Parameterizing the
sector sequence allows transport between `n+1` and the consumer's `1+n`. -/
def StrongSymbolsAt {T : Type*} (particles : ℕ → ℕ) (K : Set T)
    (A : ∀ n, BetheCoefficientTransform.HN L (particles n) →L[ℂ]
      BetheCoefficientTransform.HN L (particles n))
    (z : T → ℂ) (v : T → ∀ n, BetheCoefficientTransform.HN L (particles n)) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ K,
    ‖A n (v t n) - z t • v t n‖ ≤ ε ∧
    ‖(A n).adjoint (v t n) - conj (z t) • v t n‖ ≤ ε

def DynamicComparisonAt (hκ : 0 < κ) (F : HigherFlows L κ) (g : BetheOccupationGauge.Gauge)
    (particles : ℕ → ℕ) (positive : ∀ n, 0 < particles n) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
      (ψ : ∀ n, BetheCoefficientTransform.HN L (particles n)),
      StrongSymbolDef.IsNormClosePrep ψ (fun n => productAt u (particles n)) →
      ∀ a b : ℤ,
        let z := w hκ F u R
        let c := fun t => z t a * conj (z t b)
        let v := fun t n => UAt hκ R t (particles n) (positive n) (ψ n)
        let w₀ := (Def021ChartR41b.chart L κ hκ).Φ (physical u)
        StrongSymbolsAt particles (TimeBox R lo hi)
          (fun n => EAt (L := L) hκ g (particles n) (positive n) a b) c v ∧
        (a ≠ b → 0 < ‖w₀ a‖ ^ 2 → 0 < ‖w₀ b‖ ^ 2 →
          StrongSymbolsAt particles (TimeBox R lo hi)
            (fun n => WAt (L := L) hκ g (particles n) (positive n) a b)
            (fun t => c t / (Real.sqrt (‖z t a‖ ^ 2 * ‖z t b‖ ^ 2) : ℂ)) v)

theorem dynamic_type_eq (hκ : 0 < κ) (F : HigherFlows L κ) (g : BetheOccupationGauge.Gauge) :
    DynamicComparisonAt hκ F g (fun n => 1+n) (fun n => by omega) =
      RD8362E5EBInput hκ F g := rfl

private theorem cartesian_coeff_residuals (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge)
    (n : ℕ) (a b : ℤ) (x : BetheCoefficientTransform.HN L (n+1)) (c : ℂ) :
    let A := DynamicGaugePhysicalR34m.E hκ (physicalGauge q) n a b
    let B := cartesian (q n) a b
    let g := J (basis hκ n) x
    ‖A x - c • x‖ = ‖B g - c • g‖ ∧
      ‖A.adjoint x - conj c • x‖ = ‖B.adjoint g - conj c • g‖ := by
  let D := basis (L := L) hκ n
  let A := DynamicGaugePhysicalR34m.E (L := L) hκ (physicalGauge q) n a b
  have h₁ := residual_inCoefficients D A x c
  have h₂ := residual_inCoefficients D A.adjoint x (conj c)
  have he := E_coordinates (L := L) hκ n q a b
  change RetargetEdgeR48b.inCoefficients D A = _ at he
  rw [he] at h₁
  rw [← inCoefficients_adjoint, he] at h₂
  exact ⟨h₁.symm, h₂.symm⟩

private theorem phase_coeff_residuals (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge)
    (n : ℕ) (a b : ℤ) (x : BetheCoefficientTransform.HN L (n+1)) (c : ℂ) :
    let A := DynamicGaugePhysicalR34m.W hκ (physicalGauge q) n a b
    let B := FiniteCellGauge.W (q n) a b
    let g := J (basis hκ n) x
    ‖A x - c • x‖ = ‖B g - c • g‖ ∧
      ‖A.adjoint x - conj c • x‖ = ‖B.adjoint g - conj c • g‖ := by
  let D := basis (L := L) hκ n
  let A := DynamicGaugePhysicalR34m.W (L := L) hκ (physicalGauge q) n a b
  have h₁ := residual_inCoefficients D A x c
  have h₂ := residual_inCoefficients D A.adjoint x (conj c)
  have he := W_coordinates (L := L) hκ n q a b
  change RetargetEdgeR48b.inCoefficients D A = _ at he
  rw [he] at h₁
  rw [← inCoefficients_adjoint, he] at h₂
  exact ⟨h₁.symm, h₂.symm⟩

private abbrev orbitCoeffs (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ)
    (t : ℕ → ℝ) (n : ℕ) :=
  J (basis hκ n) (U hκ R t n (product u n))

private abbrev initialCoeffs (hκ : 0 < κ) (u : Smooth L) (n : ℕ) :=
  J (basis hκ n) (product u n)

private theorem quantumUnitary_for_orbit (hκ : 0 < κ) (R : Finset ℕ)
    (t : ℕ → ℝ) (n : ℕ) :
    ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n = U hκ R t n := by
  unfold ActualModelQuantumR52a.chargeUnitary U UAt HierarchyFlow.quantumFlow
  unfold ActualModelQuantumR52a.chargeSymbol HierarchyFlow.jointSymbol
  simp only [Nat.cast_add, Nat.cast_one]

private theorem orbit_zero (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ) :
    w hκ F u R 0 = (Def021ChartR41b.chart L κ hκ).Φ (physical u) := by
  let G := ActualModelTargetR53a.hamFlows F R
  have hs (r : ℕ) (v : Smooth L) : Def033HierarchyR24m.smoothStep G r 0 v = v := by
    unfold Def033HierarchyR24m.smoothStep
    split_ifs with hr
    · exact Subtype.ext ((G.ham r hr v.val v.property).1)
    · rfl
  have h : Def033HierarchyR24m.jointSmooth G 0 u = u := by
    unfold Def033HierarchyR24m.jointSmooth
    generalize R.sort (· ≤ ·) = rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      rw [List.foldr_cons]
      change Def033HierarchyR24m.smoothStep G r 0 _ = _
      rw [hs, ih]
  change (Def021ChartR41b.chart L κ hκ).Φ
    (physical (Def033HierarchyR24m.jointSmooth G 0 u)) = _
  rw [h]

private theorem orbitCoeffs_zero (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ) (n : ℕ) :
    orbitCoeffs hκ u R 0 n = initialCoeffs hκ u n := by
  apply lp.ext
  funext m
  obtain ⟨i, rfl⟩ := (BetheCoefficientTransform.marrArr (n+1)).surjective m
  rw [BetheCoefficientTransform.occupationCoefficient_apply,
    BetheCoefficientTransform.occupationCoefficient_apply, HierarchyFlow.quantumFlow_coord]
  simp

private theorem phase_target (hκ : 0 < κ) (F : HigherFlows L κ)
    (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) (a b : ℤ)
    (ha : 0 < ‖w hκ F u R 0 a‖ ^ 2) (hb : 0 < ‖w hκ F u R 0 b‖ ^ 2) :
    let z := w hκ F u R t
    (pairPhase (z a) (z b)).1 =
      z a * conj (z b) / (Real.sqrt (‖z a‖ ^ 2 * ‖z b‖ ^ 2) : ℂ) := by
  let z := w hκ F u R t
  have hm (j : ℤ) : ‖z j‖ = ‖w hκ F u R 0 j‖ := by
    rw [orbit_zero]
    exact orbit_moduli hκ F u R t j
  have ha' : z a ≠ 0 := by
    intro h
    rw [← hm a, h, norm_zero] at ha
    norm_num at ha
  have hb' : z b ≠ 0 := by
    intro h
    rw [← hm b, h, norm_zero] at hb
    norm_num at hb
  change (pairPhase (z a) (z b)).1 = _
  rw [pairPhase_eq_printed _ _ ha' hb']
  unfold FiniteCellFinal.symbol
  rw [norm_mul, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- Fixed count concentrations on the original product, furnished by the
accepted finite-count proposition. The same estimates hold at every time. -/
private theorem count_at_all_times (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (a : ℤ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ t,
      ‖OccupationHilbert.E (n+1) a a (orbitCoeffs hκ u R t n) -
        ((‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ ^ 2 : ℝ) : ℂ) •
          orbitCoeffs hκ u R t n‖ ≤ δ := by
  obtain ⟨S, _, _, hS⟩ := smooth_profile_ball u hu
  let I : Finset ℤ := {a}
  filter_upwards [RetargetStageR48b.eventual_actions (L := L) hκ S I δ hδ] with n hn
  intro t
  rw [count_residual_eq_of_moduli a _ _ (initialCoeffs hκ u n)
    (quantum_moduli hκ R t n (product u n))]
  exact hn (physical u) hS ⟨a, by simp [I]⟩

private theorem static_phase (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (hj : Tendsto j atTop atTop)
    (hq : ∀ S > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ u ∈ UniformStaticR31m.unitBall (L := L) S,
        ∀ p ∈ UniformStaticR31m.eligible hκ (j n) α u,
          UniformStaticR31m.phaseError hκ q n u p ≤ ε)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (a b : ℤ) (hab : a ≠ b)
    (ha : 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ ^ 2)
    (hb : 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      let ζ := pairPhase ((Def021ChartR41b.chart L κ hκ).Φ (physical u) a)
        ((Def021ChartR41b.chart L κ hκ).Φ (physical u) b)
      let g := initialCoeffs hκ u n
      ‖FiniteCellGauge.W (q n) a b g - ζ.1 • g‖ ≤ ε ∧
        ‖(FiniteCellGauge.W (q n) a b).adjoint g - conj ζ.1 • g‖ ≤ ε := by
  let A := UniformStaticR31m.action hκ (physical u) a
  let B := UniformStaticR31m.action hκ (physical u) b
  let α := min A B
  obtain ⟨S, hS, huS, _⟩ := smooth_profile_ball u hu
  have ha' : 0 < A := ha
  have hb' : 0 < B := hb
  have haWin := hj.eventually (RetargetAnglesR48b.eventually_mem_labels a)
  have hbWin := hj.eventually (RetargetAnglesR48b.eventually_mem_labels b)
  filter_upwards [haWin, hbWin, hq S hS α (lt_min ha' hb') ε hε] with n hja hjb hn
  have hel : (a, b) ∈ UniformStaticR31m.eligible hκ (j n) α (physical u) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hja, hjb⟩,
      hab, min_le_left _ _, min_le_right _ _⟩
  let W₀ := DynamicGaugePhysicalR34m.W (L := L) hκ (physicalGauge q) n a b
  let ζ := pairPhase ((Def021ChartR41b.chart L κ hκ).Φ (physical u) a)
    ((Def021ChartR41b.chart L κ hκ).Φ (physical u) b)
  have hz : UniformStaticR31m.phase hκ (physical u) (a,b) = ζ := rfl
  have h := hn (physical u) huS (a,b) hel
  unfold UniformStaticR31m.phaseError UniformStaticR31m.residual at h
  rw [hz, ← W_eq_static] at h
  change ‖W₀ (product u n) - ζ.1 • product u n‖ +
    ‖W₀.adjoint (product u n) - conj ζ.1 • product u n‖ ≤ ε at h
  have he := phase_coeff_residuals hκ q n a b (product u n) ζ.1
  rw [he.1, he.2] at h
  exact ⟨le_trans (le_add_of_nonneg_right (norm_nonneg _)) h,
    le_trans (le_add_of_nonneg_left (norm_nonneg _)) h⟩

private theorem phase_on_box (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (hlo : ∀ r ∈ R, lo r ≤ 0) (hhi : ∀ r ∈ R, 0 ≤ hi r)
    (q : UniformStaticR31m.FullGauge) (a b : ℤ) (hab : a ≠ b)
    (ha : 0 < ‖w hκ F u R 0 a‖ ^ 2) (hb : 0 < ‖w hκ F u R 0 b‖ ^ 2)
    (hstatic : ∀ ε > 0, ∀ᶠ n in atTop,
      let ζ := pairPhase (w hκ F u R 0 a) (w hκ F u R 0 b)
      let g := initialCoeffs hκ u n
      ‖FiniteCellGauge.W (q n) a b g - ζ.1 • g‖ ≤ ε ∧
        ‖(FiniteCellGauge.W (q n) a b).adjoint g - conj ζ.1 • g‖ ≤ ε)
    (hseed : DynSeedR47b.SeedStatement hκ F u R lo hi a b) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : DynSeedInputR47b.TimeBox R lo hi,
      let ζ := pairPhase (w hκ F u R t.val a) (w hκ F u R t.val b)
      let g := orbitCoeffs hκ u R t.val n
      ‖FiniteCellGauge.W (q n) a b g - ζ.1 • g‖ ≤ ε ∧
        ‖(FiniteCellGauge.W (q n) a b).adjoint g - conj ζ.1 • g‖ ≤ ε := by
  let ζ (t : ℕ → ℝ) := pairPhase (w hκ F u R t a) (w hκ F u R t b)
  let ρ := Real.sqrt (‖w hκ F u R 0 a‖ ^ 2 * ‖w hκ F u R 0 b‖ ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (mul_pos ha hb)
  have hm (t : ℕ → ℝ) (j : ℤ) : ‖w hκ F u R t j‖ = ‖w hκ F u R 0 j‖ := by
    rw [orbit_zero]
    exact orbit_moduli hκ F u R t j
  have hf (t : ℕ → ℝ) : (ρ : ℂ) * (ζ t).1 = w hκ F u R t a * conj (w hκ F u R t b) := by
    have h := pair_factor (w hκ F u R t a) (w hκ F u R t b)
    rw [hm t a, hm t b] at h
    exact h
  obtain ⟨C, hg, ht⟩ := hseed
  have hex (n : ℕ) := graded_polar_bounds (basis hκ n) (C n) a b hab (hg n)
  choose c hc using hex
  let p n := DynamicGaugeEdgesR34m.chainGauge a b hab (c n)
  have hpol (n : ℕ) (t : DynSeedInputR47b.TimeBox R lo hi) :
      let g := orbitCoeffs hκ u R t.val n
      let e := DynSeedPolynomialR47b.residual (C n)
        (DynSeedClassicalR47b.symbol hκ a b (classicalOrbit hκ F u R t.val))
        (quantumOrbit hκ u R t.val n)
      ρ * ‖FiniteCellGauge.W (p n) a b g - (ζ t.val).1 • g‖ ≤ e ∧
      ρ * ‖(FiniteCellGauge.W (p n) a b).adjoint g - conj (ζ t.val).1 • g‖ ≤ e := by
    have h := hc n (quantumOrbit hκ u R t.val n) (ζ t.val) ρ hρ.le
    dsimp only at h ⊢
    rw [hf] at h
    have hg' : J (basis hκ n) (quantumOrbit hκ u R t.val n) =
        orbitCoeffs hκ u R t.val n := by
      simp only [quantumOrbit, quantumUnitary_for_orbit, orbitCoeffs, product, productAt]
    have hs' : DynSeedClassicalR47b.symbol hκ a b (classicalOrbit hκ F u R t.val) =
        w hκ F u R t.val a * conj (w hκ F u R t.val b) := rfl
    rw [show p n = DynamicGaugeEdgesR34m.chainGauge a b hab (c n) from rfl,
      DynamicGaugeEdgesR34m.chain_shift, ← hg', hs']
    exact h
  let t₀ : DynSeedInputR47b.TimeBox R lo hi := ⟨0, fun r => by
    by_cases hr : r ∈ R
    · simpa [hr] using And.intro (hlo r hr) (hhi r hr)
    · simp [hr]⟩
  intro ε hε
  let δ := ε / 3
  have hδ : 0 < δ := by positivity
  filter_upwards [hstatic δ hδ, ENNReal.tendsto_nhds_zero.mp ht
    (ENNReal.ofReal (ρ * δ)) (ENNReal.ofReal_pos.mpr (mul_pos hρ hδ))] with n hs hn
  have aux (t : DynSeedInputR47b.TimeBox R lo hi) :
      let g := orbitCoeffs hκ u R t.val n
      ‖FiniteCellGauge.W (p n) a b g - (ζ t.val).1 • g‖ ≤ δ ∧
      ‖(FiniteCellGauge.W (p n) a b).adjoint g - conj (ζ t.val).1 • g‖ ≤ δ := by
    have hn' := (le_iSup (fun t : DynSeedInputR47b.TimeBox R lo hi =>
      ENNReal.ofReal (DynSeedPolynomialR47b.residual (C n)
        (DynSeedClassicalR47b.symbol hκ a b (classicalOrbit hκ F u R t.val))
          (quantumOrbit hκ u R t.val n))) t).trans hn
    have hh := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hρ.le hδ.le)).mp hn'
    exact ⟨le_of_mul_le_mul_left ((hpol n t).1.trans hh) hρ,
      le_of_mul_le_mul_left ((hpol n t).2.trans hh) hρ⟩
  have hzero := aux t₀
  change _ ∧ _ at hzero
  have hz : t₀.val = 0 := rfl
  rw [hz, orbitCoeffs_zero] at hzero
  intro t
  dsimp only at hs ⊢
  have hm' := quantum_moduli hκ R t.val n (product u n)
  constructor
  · have hdiff := DynamicGaugeEdgesR34m.difference_norm_eq_of_moduli (q n) (p n) a b _ _ hm'
    have h₀ := (norm_sub_le_norm_sub_add_norm_sub _ ((ζ 0).1 • initialCoeffs hκ u n) _).trans
      (add_le_add hs.1 ((norm_sub_rev _ _).le.trans hzero.1))
    have ht' := norm_sub_le_norm_sub_add_norm_sub
      (FiniteCellGauge.W (q n) a b (orbitCoeffs hκ u R t.val n))
      (FiniteCellGauge.W (p n) a b (orbitCoeffs hκ u R t.val n))
      ((ζ t.val).1 • orbitCoeffs hκ u R t.val n)
    rw [hdiff] at ht'
    exact ht'.trans ((add_le_add h₀ (aux t).1).trans (by dsimp [δ]; linarith))
  · have hdiff := DynamicGaugeEdgesR34m.adjoint_difference_norm_eq_of_moduli (q n) (p n) a b hab _ _ hm'
    have h₀ := (norm_sub_le_norm_sub_add_norm_sub _ (conj (ζ 0).1 • initialCoeffs hκ u n) _).trans
      (add_le_add hs.2 ((norm_sub_rev _ _).le.trans hzero.2))
    have ht' := norm_sub_le_norm_sub_add_norm_sub
      ((FiniteCellGauge.W (q n) a b).adjoint (orbitCoeffs hκ u R t.val n))
      ((FiniteCellGauge.W (p n) a b).adjoint (orbitCoeffs hκ u R t.val n))
      (conj (ζ t.val).1 • orbitCoeffs hκ u R t.val n)
    rw [hdiff] at ht'
    exact ht'.trans ((add_le_add h₀ (aux t).2).trans (by dsimp [δ]; linarith))

private theorem cartesian_on_box (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (hu : ‖physical u‖ = 1) (R : Finset ℕ) (lo hi : ℕ → ℝ)
    (q : UniformStaticR31m.FullGauge) (a b : ℤ)
    (hphase : a ≠ b → 0 < ‖w hκ F u R 0 a‖ ^ 2 → 0 < ‖w hκ F u R 0 b‖ ^ 2 →
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : DynSeedInputR47b.TimeBox R lo hi,
        let ζ := pairPhase (w hκ F u R t.val a) (w hκ F u R t.val b)
        let g := orbitCoeffs hκ u R t.val n
        ‖FiniteCellGauge.W (q n) a b g - ζ.1 • g‖ ≤ ε ∧
          ‖(FiniteCellGauge.W (q n) a b).adjoint g - conj ζ.1 • g‖ ≤ ε) :
    StrongSymbolsAt (fun n => n+1) (fun t => ∀ r, t r ∈ if r ∈ R then Set.Icc (lo r) (hi r) else {0})
      (fun n => DynamicGaugePhysicalR34m.E hκ (physicalGauge q) n a b)
      (fun t => w hκ F u R t a * conj (w hκ F u R t b))
      (fun t n => U hκ R t n (product u n)) := by
  let z := w hκ F u R
  let A := ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ ^ 2
  let B := ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have hA₁ : A ≤ 1 := by
    have h := RetargetStageR48b.coordinate_le_one hκ (physical u) hu a
    dsimp [A, RetargetStageR48b.coordinate] at h ⊢
    exact pow_le_one₀ (norm_nonneg _) h
  have hB₁ : B ≤ 1 := by
    have h := RetargetStageR48b.coordinate_le_one hκ (physical u) hu b
    dsimp [B, RetargetStageR48b.coordinate] at h ⊢
    exact pow_le_one₀ (norm_nonneg _) h
  have ha (t : ℕ → ℝ) : ‖z t a‖ ^ 2 = A :=
    congrArg (· ^ 2) (orbit_moduli hκ F u R t a)
  have hb (t : ℕ → ℝ) : ‖z t b‖ ^ 2 = B :=
    congrArg (· ^ 2) (orbit_moduli hκ F u R t b)
  have hg (n : ℕ) (t : ℕ → ℝ) : ‖orbitCoeffs hκ u R t n‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    change ‖TensorCarrier.htpow (n+1) (physical u)‖ = 1
    rw [TensorCarrier.norm_htpow, hu, one_pow]
  intro ε hε
  by_cases hab : a = b
  · subst b
    filter_upwards [count_at_all_times hκ u hu R a ε hε] with n hn
    intro t ht
    have hc : z t a * conj (z t a) = (A : ℂ) :=
      (Complex.mul_conj' (z t a)).trans
        ((Complex.ofReal_pow _ _).symm.trans (congrArg Complex.ofReal (ha t)))
    have hfwd : ‖DynamicGaugePhysicalR34m.E hκ (physicalGauge q) n a a
          (U hκ R t n (product u n)) - (A : ℂ) • U hκ R t n (product u n)‖ ≤ ε := by
      rw [(cartesian_coeff_residuals hκ q n a a (U hκ R t n (product u n)) (A : ℂ)).1,
        cartesian_diag]
      exact hn t
    change ‖_ - (z t a * conj (z t a)) • _‖ ≤ ε ∧
      ‖_ - conj (z t a * conj (z t a)) • _‖ ≤ ε
    refine ⟨?_, ?_⟩
    · rw [hc]
      exact hfwd
    · rw [hc, (cartesian_coeff_residuals hκ q n a a (U hκ R t n (product u n)) (A : ℂ)).2,
        Complex.conj_ofReal, cartesian_adjoint, cartesian_diag]
      exact hn t
  · let δ := ε ^ 2 / 16
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hinv : ∀ᶠ n : ℕ in atTop, ((n+1 : ℕ) : ℝ)⁻¹ ≤ δ := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      filter_upwards [h.eventually (gt_mem_nhds hδ)] with n hn
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using hn.le
    have hp : ∀ᶠ n in atTop, ∀ t : DynSeedInputR47b.TimeBox R lo hi,
        let g := orbitCoeffs hκ u R t.val n
        let s := Real.sqrt (A * B)
        let ζ := pairPhase (z t.val a) (z t.val b)
        s * ‖FiniteCellGauge.W (q n) a b g - ζ.1 • g‖ ≤ ε/2 ∧
        s * ‖(FiniteCellGauge.W (q n) a b).adjoint g - conj ζ.1 • g‖ ≤ ε/2 := by
      by_cases hp : 0 < A ∧ 0 < B
      · filter_upwards [hphase hab (by rw [ha 0]; exact hp.1) (by rw [hb 0]; exact hp.2) (ε/2) (half_pos hε)]
          with n hn
        intro t
        have hs : Real.sqrt (A * B) ≤ 1 := by
          apply (Real.sqrt_le_iff).2
          exact ⟨zero_le_one, by simpa using mul_le_mul hA₁ hB₁ hB zero_le_one⟩
        exact ⟨(mul_le_of_le_one_left (norm_nonneg _) hs).trans (hn t).1,
          (mul_le_of_le_one_left (norm_nonneg _) hs).trans (hn t).2⟩
      · apply Eventually.of_forall
        intro n t
        have hzero : A = 0 ∨ B = 0 := by
          by_contra! h
          exact hp ⟨lt_of_le_of_ne hA h.1.symm, lt_of_le_of_ne hB h.2.symm⟩
        have he : Real.sqrt (A * B) = 0 := by rcases hzero with h | h <;> simp [h]
        simpa only [he, zero_mul] using And.intro (half_pos hε).le (half_pos hε).le
    filter_upwards [count_at_all_times hκ u hu R a δ hδ,
      count_at_all_times hκ u hu R b δ hδ, hp, hinv] with n hna hnb hpn hni
    intro t ht
    let tb : DynSeedInputR47b.TimeBox R lo hi := ⟨t, ht⟩
    let ζ := pairPhase (z t a) (z t b)
    let g := orbitCoeffs hκ u R t n
    have hbound : Real.sqrt (2*δ + ((n+1 : ℕ) : ℝ)⁻¹) ≤ ε/2 := by
      apply (Real.sqrt_le_iff).2
      exact ⟨(half_pos hε).le, by dsimp [δ] at hni ⊢; nlinarith⟩
    have hc : (Real.sqrt (A*B) : ℂ) * ζ.1 = z t a * conj (z t b) := by
      have h := pair_factor (z t a) (z t b)
      rw [ha t, hb t] at h
      exact h
    have hrev : conj (z t a * conj (z t b)) = z t b * conj (z t a) := by
      simp [mul_comm]
    have hc' : (Real.sqrt (B*A) : ℂ) * (pairPhase (z t b) (z t a)).1 =
        z t b * conj (z t a) := by
      have h := pair_factor (z t b) (z t a)
      rw [hb t, ha t] at h
      exact h
    have hf := cartesian_residual (q n) (Nat.succ_pos n) a b hab g (hg n t) A B δ
      hA hB hA₁ (hna t) (hnb t) ζ
    have hr := cartesian_residual (q n) (Nat.succ_pos n) b a (Ne.symm hab) g (hg n t) B A δ
      hB hA hB₁ (hnb t) (hna t) (pairPhase (z t b) (z t a))
    dsimp only at hf hr
    rw [hc] at hf
    rw [hc', ← W_adjoint (q n) a b hab, phase_reverse, mul_comm B A] at hr
    have he := cartesian_coeff_residuals hκ q n a b (U hκ R t n (product u n))
      (z t a * conj (z t b))
    refine ⟨?_, ?_⟩
    · rw [he.1]
      exact hf.trans ((add_le_add hbound (hpn tb).1).trans (by linarith))
    · rw [he.2, hrev, cartesian_adjoint]
      exact hr.trans ((add_le_add hbound (hpn tb).2).trans (by linarith))

private theorem change_preparation {T : Type*} (K : Set T)
    (A : ∀ n, BetheCoefficientTransform.HN L (n+1) →L[ℂ] BetheCoefficientTransform.HN L (n+1))
    (z : T → ℂ) (V : T → ∀ n, BetheCoefficientTransform.HN L (n+1) ≃ₗᵢ[ℂ]
      BetheCoefficientTransform.HN L (n+1))
    (x y : ∀ n, BetheCoefficientTransform.HN L (n+1))
    (hA : ∀ n, ‖A n‖ ≤ 1) (hz : ∀ t ∈ K, ‖z t‖ ≤ 1)
    (hxy : Tendsto (fun n => ‖y n - x n‖) atTop (𝓝 0))
    (h : StrongSymbolsAt (fun n => n+1) K A z (fun t n => V t n (x n))) :
    StrongSymbolsAt (fun n => n+1) K A z (fun t n => V t n (y n)) := by
  intro ε hε
  filter_upwards [h (ε/2) (half_pos hε),
    hxy.eventually (gt_mem_nhds (show 0 < ε/4 by positivity))] with n hn hclose
  intro t ht
  have move (B : BetheCoefficientTransform.HN L (n+1) →L[ℂ] BetheCoefficientTransform.HN L (n+1))
      (β : ℂ) (hB : ‖B‖ ≤ 1) (hβ : ‖β‖ ≤ 1)
      (he : ‖B (V t n (x n)) - β • V t n (x n)‖ ≤ ε/2) :
      ‖B (V t n (y n)) - β • V t n (y n)‖ ≤ ε := by
    have hh := StrongSymbolDef.norm_sub_smul_id_apply_le B β (V t n (y n - x n))
    rw [LinearIsometryEquiv.norm_map] at hh
    rw [map_sub] at hh
    let D : BetheCoefficientTransform.HN L (n+1) →L[ℂ] BetheCoefficientTransform.HN L (n+1) :=
      B - β • ContinuousLinearMap.id ℂ (BetheCoefficientTransform.HN L (n+1))
    have hsplit :
        B (V t n (y n)) - β • V t n (y n) =
          B (V t n (x n)) - β • V t n (x n) +
            D (V t n (y n) - V t n (x n)) := by
      dsimp only [D]
      simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub]
      abel
    rw [hsplit]
    have he' := mul_le_mul (show ‖B‖ + ‖β‖ ≤ 2 by linarith) hclose.le (norm_nonneg _) (by norm_num)
    exact (norm_add_le _ _).trans ((add_le_add he (hh.trans he')).trans (by linarith))
  exact ⟨move _ _ (hA n) (hz t ht) (hn t ht).1,
    move _ _ (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hA n)
      (by simpa only [Complex.norm_conj] using hz t ht) (hn t ht).2⟩

/-- Pre-start R-8362E5EB on successor-indexed sectors. The result uses the
gauge witness of the retargeting theorem at every profile, pair and box. -/
theorem dynamic_gauge_successor_ofInput (hκ : 0 < κ)
    (GaugeRetargetingRD51987CAInput : UniformStaticR31m.GaugeRetargetingRD51987CAInput (L := L) hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (DynftFullTorusInput : ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ HierarchyR7B122087Input) u R)
    (R300B8640Input : R300B8640Input hκ (flows hκ HierarchyR7B122087Input)) :
    ∃ (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge),
      Monotone j ∧ Tendsto j atTop atTop ∧
      (∀ S > 0, UniformStaticR31m.UniformError (UniformStaticR31m.unitBall (L := L) S)
        (fun n _ => UniformStaticR31m.pairs (j n)) (UniformStaticR31m.cartesianError hκ q)) ∧
      (∀ S > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ u ∈ UniformStaticR31m.unitBall (L := L) S,
          ∀ p ∈ UniformStaticR31m.eligible hκ (j n) α u,
            UniformStaticR31m.phaseError hκ q n u p ≤ ε ∧
              UniformStaticR31m.missingInitial hκ n u p ≤ ε ∧
              UniformStaticR31m.missingFinal hκ n u p ≤ ε ∧
              UniformStaticR31m.affinityError hκ n u p ≤ ε ∧
              UniformStaticR31m.defectError hκ q n u p ≤ ε) ∧
      UniformStaticR31m.ExteriorExact ∧
      DynamicComparisonAt hκ (flows hκ HierarchyR7B122087Input) (physicalGauge q)
        (fun n => n+1) Nat.succ_pos := by
  obtain ⟨j,q,hj,hjInf,hcart,hphase,hext⟩ := GaugeRetargetingRD51987CAInput
  refine ⟨j,q,hj,hjInf,hcart,hphase,hext,?_⟩
  let F := flows hκ HierarchyR7B122087Input
  intro u hu R lo hi ψ hψ a b
  dsimp only
  let lo' (r : ℕ) := if hr : r ∈ R then min (lo ⟨r,hr⟩) 0 else 0
  let hi' (r : ℕ) := if hr : r ∈ R then max (hi ⟨r,hr⟩) 0 else 0
  have hlo (r) (hr : r ∈ R) : lo' r ≤ 0 := by simp [lo', hr]
  have hhi (r) (hr : r ∈ R) : 0 ≤ hi' r := by simp [hi', hr]
  let z := w hκ F u R
  let z₀ := (Def021ChartR41b.chart L κ hκ).Φ (physical u)
  have hz₀ : z 0 = z₀ := orbit_zero hκ F u R
  let v (t : ℕ → ℝ) (n : ℕ) := U hκ R t n (product u n)
  let canon (t : ℕ → ℝ) (r : ℕ) := if r ∈ R then t r else 0
  have hcanon (t : ℕ → ℝ) (ht : t ∈ TimeBox R lo hi) :
      ∀ r, canon t r ∈ if r ∈ R then Set.Icc (lo' r) (hi' r) else {0} := by
    intro r
    by_cases hr : r ∈ R
    · have h := ht ⟨r,hr⟩
      simpa only [canon, lo', hi', hr, dite_eq_left, ↓reduceIte, Set.mem_Icc] using
        And.intro ((min_le_left (lo ⟨r,hr⟩) 0).trans h.1)
          (h.2.trans (le_max_left (hi ⟨r,hr⟩) 0))
    · simp [canon, hr]
  have hcAgree (t : ℕ → ℝ) (r : ℕ) (hr : r ∈ R) : canon t r = t r := by simp [canon, hr]
  have hzEq (t : ℕ → ℝ) : z (canon t) = z t := by
    change (Def021ChartR41b.chart L κ hκ).Φ
      (physical (Def033HierarchyR24m.jointSmooth (ActualModelTargetR53a.hamFlows F R) (canon t) u)) = _
    rw [joint_inactive F R (canon t) t (hcAgree t)]
  have hvEq (t : ℕ → ℝ) (n : ℕ) : v (canon t) n = v t n := by
    dsimp only [v]
    rw [U_inactive hκ R (canon t) t (hcAgree t) n]
  have hs (S : ℝ) (hS : 0 < S) (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ u ∈ UniformStaticR31m.unitBall (L := L) S,
        ∀ p ∈ UniformStaticR31m.eligible hκ (j n) α u,
          UniformStaticR31m.phaseError hκ q n u p ≤ ε :=
    (hphase S hS α hα ε hε).mono (fun _ hn u hu p hp => (hn u hu p hp).1)
  have hp (hab : a ≠ b) (ha : 0 < ‖z 0 a‖ ^ 2) (hb : 0 < ‖z 0 b‖ ^ 2) :=
    phase_on_box hκ F u R lo' hi' hlo hhi q a b hab ha hb
      (by rw [hz₀] at ha hb; rw [orbit_zero]; exact static_phase hκ j q hjInf hs u hu a b hab ha hb)
      (R300B8640Input u hu R lo' hi' a b hab
        (DynftFullTorusInput u hu R (mixed_finite_ofInput hκ HierarchyR7B122087Input
          RE679E41DInput u hu R)))
  have hCart0 := cartesian_on_box hκ F u hu R lo' hi' q a b hp
  have hCart : StrongSymbolsAt (fun n => n+1) (TimeBox R lo hi)
      (fun n => DynamicGaugePhysicalR34m.E hκ (physicalGauge q) n a b)
      (fun t => z t a * conj (z t b)) v := by
    intro ε hε
    filter_upwards [hCart0 ε hε] with n hn
    intro t ht
    let A := DynamicGaugePhysicalR34m.E (L := L) hκ (physicalGauge q) n a b
    have he := hn (canon t) (hcanon t ht)
    change ‖A (v (canon t) n) - (z (canon t) a * conj (z (canon t) b)) • v (canon t) n‖ ≤ ε ∧
      ‖A.adjoint (v (canon t) n) - conj (z (canon t) a * conj (z (canon t) b)) •
        v (canon t) n‖ ≤ ε at he
    rw [hzEq t, hvEq t n] at he
    exact he
  refine ⟨?_, ?_⟩
  · apply change_preparation _ _ _ (fun t n => U hκ R t n) (product u) ψ
      (fun n => CartesianOccupationTransfer.physical_norm_le _ _ _ _) ?_ hψ.2 hCart
    intro t _
    have ha₁ : ‖z₀ a‖ ≤ 1 := RetargetStageR48b.coordinate_le_one hκ (physical u) hu a
    have hb₁ : ‖z₀ b‖ ≤ 1 := RetargetStageR48b.coordinate_le_one hκ (physical u) hu b
    rw [norm_mul, Complex.norm_conj, show ‖z t a‖ = ‖z₀ a‖ from orbit_moduli hκ F u R t a,
      show ‖z t b‖ = ‖z₀ b‖ from orbit_moduli hκ F u R t b]
    calc
      ‖z₀ a‖ * ‖z₀ b‖ ≤ 1 * ‖z₀ b‖ := mul_le_mul_of_nonneg_right ha₁ (norm_nonneg (z₀ b))
      _ = ‖z₀ b‖ := one_mul _
      _ ≤ 1 := hb₁
  · intro hab ha hb
    have ha' : 0 < ‖z 0 a‖ ^ 2 := by rw [hz₀]; exact ha
    have hb' : 0 < ‖z 0 b‖ ^ 2 := by rw [hz₀]; exact hb
    let η (t : ℕ → ℝ) := z t a * conj (z t b) /
      (Real.sqrt (‖z t a‖ ^ 2 * ‖z t b‖ ^ 2) : ℂ)
    have hη (t : ℕ → ℝ) : (pairPhase (z t a) (z t b)).1 = η t :=
      phase_target hκ F u R t a b ha' hb'
    have hP : StrongSymbolsAt (fun n => n+1) (TimeBox R lo hi)
        (fun n => DynamicGaugePhysicalR34m.W hκ (physicalGauge q) n a b) η v := by
      intro ε hε
      filter_upwards [hp hab ha' hb' ε hε] with n hn
      intro t ht
      let ts : DynSeedInputR47b.TimeBox R lo' hi' := ⟨canon t, hcanon t ht⟩
      have h := hn ts
      change _ ∧ _ at h
      have hq₁ := h.1
      have hq₂ := h.2
      change ‖FiniteCellGauge.W (q n) a b (J (basis hκ n) (v (canon t) n)) -
        (pairPhase (z (canon t) a) (z (canon t) b)).1 • J (basis hκ n) (v (canon t) n)‖ ≤ ε at hq₁
      change ‖(FiniteCellGauge.W (q n) a b).adjoint (J (basis hκ n) (v (canon t) n)) -
        conj (pairPhase (z (canon t) a) (z (canon t) b)).1 • J (basis hκ n) (v (canon t) n)‖ ≤ ε at hq₂
      rw [hzEq t, hvEq t n, hη t] at hq₁ hq₂
      have he := phase_coeff_residuals hκ q n a b (v t n) (η t)
      exact ⟨he.1.le.trans hq₁, he.2.le.trans hq₂⟩
    exact change_preparation _ _ _ (fun t n => U hκ R t n) (product u) ψ
      (fun n => UnitPhaseTransfer.physical_norm_le _ _ _ _)
      (fun t _ => by
        change ‖η t‖ ≤ 1
        rw [← hη t, (pairPhase (z t a) (z t b)).2]) hψ.2 hP

/-- R-8362E5EB with the exact particle indexing of its round 33 consumer. -/
theorem dynamic_gauge_ofInput (hκ : 0 < κ)
    (GaugeRetargetingRD51987CAInput : UniformStaticR31m.GaugeRetargetingRD51987CAInput (L := L) hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (DynftFullTorusInput : ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ HierarchyR7B122087Input) u R)
    (R300B8640Input : R300B8640Input hκ (flows hκ HierarchyR7B122087Input)) :
    ∃ (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge),
      Monotone j ∧ Tendsto j atTop atTop ∧
      (∀ S > 0, UniformStaticR31m.UniformError (UniformStaticR31m.unitBall (L := L) S)
        (fun n _ => UniformStaticR31m.pairs (j n)) (UniformStaticR31m.cartesianError hκ q)) ∧
      (∀ S > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ u ∈ UniformStaticR31m.unitBall (L := L) S,
          ∀ p ∈ UniformStaticR31m.eligible hκ (j n) α u,
            UniformStaticR31m.phaseError hκ q n u p ≤ ε ∧
              UniformStaticR31m.missingInitial hκ n u p ≤ ε ∧
              UniformStaticR31m.missingFinal hκ n u p ≤ ε ∧
              UniformStaticR31m.affinityError hκ n u p ≤ ε ∧
              UniformStaticR31m.defectError hκ q n u p ≤ ε) ∧
      UniformStaticR31m.ExteriorExact ∧
      RD8362E5EBInput hκ (flows hκ HierarchyR7B122087Input) (physicalGauge q) := by
  obtain ⟨j,q,hj,hjInf,hcart,hphase,hext,hdyn⟩ := dynamic_gauge_successor_ofInput hκ
    GaugeRetargetingRD51987CAInput HierarchyR7B122087Input RE679E41DInput
    DynftFullTorusInput R300B8640Input
  refine ⟨j,q,hj,hjInf,hcart,hphase,hext,?_⟩
  have he : (fun n : ℕ => n+1) = fun n => 1+n := funext (fun n => Nat.add_comm n 1)
  have hh : ∃ h : ∀ n, 0 < (fun n : ℕ => n+1) n,
      DynamicComparisonAt hκ (flows hκ HierarchyR7B122087Input) (physicalGauge q)
        (fun n => n+1) h := ⟨Nat.succ_pos, hdyn⟩
  rw [he] at hh
  obtain ⟨hp, h⟩ := hh
  exact h


end QuantumNLS.DynamicGaugeR34m

#print axioms QuantumNLS.DynamicGaugeR34m.dynamic_gauge_ofInput
