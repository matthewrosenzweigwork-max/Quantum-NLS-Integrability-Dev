import QuantumNLS.ActualGapTransferR26
import QuantumNLS.ActualGapMomentsR26
import QuantumNLS.F02TightnessActual

/-!
R-1E0C40B3, CC:F04:actual-gap, root_response/F04.tex:493–577.
The named theorem below has exactly positive L, κ and a unit H¹ profile as hypotheses.
Its response, physical limiting measure and phase inverse are constructed. The original
Born law at κ/N is used for every expectation. `default` permits arbitrary values on m_a=0.
The accepted occupation limit is consumed read-only; no interpretation of DEF-043/044
is made by this new argument. Acceptance waits for the separately assigned r197 audit.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace QuantumNLS.ActualGapR26
open ActualGapDataR26 ActualGapTransferR26 ActualGapMomentsR26
open PhysicalTensor (L2T)
open BetheLabels (MArr)
open F04SelBand (II)
open RootEnergyMomentLaws (law)
open RootOccupationLimit (occVec)
open BornConvergence (TendstoInProbability)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed gap with any prescribed value on the zero-donor event. -/
def gapWithDefault (L κ : ℝ) (a b : ℤ) (default : ∀ N, MArr N → ℝ)
    {N : ℕ} (m : MArr N) : ℝ :=
  if 1 ≤ m.1 a then F02Tightness.gap L κ a b m else default N m

def radius (hκ : 0 < κ) (u : L2T L) (a b : ℤ) : ℝ := min (II hκ u a) (II hκ u b) / 2

def good (hκ : 0 < κ) (u : L2T L) (a b : ℤ) (N : ℕ) : Set (MArr N) :=
  F02Tightness.AN N a b (radius hκ u a b)

def V (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (a b : ℤ)
    (default : ∀ N, MArr N → ℝ) (w : ℝ) : ℕ → ℝ≥0∞ :=
  variance (law hκ u hu) (fun _ => gapWithDefault L κ a b default)
    (fun N m => occVec N m a) (good hκ u a b) w

def EpsSq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (a b : ℤ)
    (default : ∀ N, MArr N → ℝ) (w T : ℝ) : ℕ → ℝ≥0∞ :=
  phaseError (law hκ u hu) (fun _ => gapWithDefault L κ a b default)
    (fun N m => occVec N m a) (fun _ => {m | 1 ≤ m.1 a}) w T

def meanOccupationError (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) : ℝ≥0∞ :=
  F02Tightness.eN (law hκ u hu N) (II hκ u)

/-- The occupation weight always lies in [0,1]. -/
theorem weight_bounds {N : ℕ} (m : MArr N) (a : ℤ) : 0 ≤ occVec N m a ∧ occVec N m a ≤ 1 := by
  have h1 := AdjacentResponse.Ccum_jump m (b := a) (le_refl a)
  have h2 := AdjacentResponse.Ccum_le_N m a
  have hm : m.1 a ≤ N := by omega
  constructor
  · unfold occVec; positivity
  · by_cases hN : N = 0
    · simp [occVec,hN]
    · unfold occVec
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < N)]
      exact_mod_cast hm

theorem donor_on_good (hκ : 0 < κ) (u : L2T L) {a b : ℤ}
    (ha : 0 < II hκ u a) (hb : 0 < II hκ u b) {N : ℕ} {m : MArr N}
    (hm : m ∈ good hκ u a b N) : 1 ≤ m.1 a := by
  have hr : 0 < radius hκ u a b := by unfold radius; positivity
  have hma : radius hκ u a b ≤ occVec N m a := hm.1
  by_contra hh
  have hz : m.1 a = 0 := by omega
  have : occVec N m a = 0 := by simp [occVec,hz]
  rw [this] at hma
  exact (not_le_of_gt hr) hma

/-- Deterministic stability also covers arbitrary zero-donor values. -/
theorem default_sequence (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (D : Data hκ u)
    {a b : ℤ} (hab : a ≠ b) (ha : 0 < II hκ u a) (hb : 0 < II hκ u b)
    (default : ∀ N, MArr N → ℝ) (m : ∀ n : ℕ, MArr (n + 1))
    (he : Tendsto (fun n : ℕ => err D (n + 1) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => gapWithDefault L κ a b default (m n)) atTop (𝓝 (D.omega a b)) := by
  obtain ⟨p,hp,hpm,-⟩ := patch_donor hκ u D m he ha
  refine (deterministic_actual hκ u hu D hab ha hb m he).2.congr' ?_
  filter_upwards [hpm] with n hn
  have hh : 1 ≤ (m n).1 a := hn ▸ hp n
  exact (ite_eq_left hh).symm

/-- Probability convergence and all finite-time weighted estimates for one active pair. -/
theorem pair_conclusions (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 u) (D : Data hκ u)
    {a b : ℤ} (hab : a ≠ b) (ha : 0 < II hκ u a) (hb : 0 < II hκ u b)
    (default : ∀ N, MArr N → ℝ) :
    TendstoInProbability (law hκ u hu) (fun _ => gapWithDefault L κ a b default) (D.omega a b) ∧
    Tendsto (V hκ u hu a b default (D.omega a b)) atTop (𝓝 0) ∧
    (∀ T : ℝ,
      (∀ N : ℕ, EpsSq hκ u hu a b default (D.omega a b) T N ≤
        ENNReal.ofReal (T ^ 2) * V hκ u hu a b default (D.omega a b) N +
          4 * meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b)) ∧
      Tendsto (EpsSq hκ u hu a b default (D.omega a b) T) atTop (𝓝 0)) := by
  have he := err_probability hκ u hu hH D
  have hp : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n => gapWithDefault L κ a b default (N := n + 1)) (D.omega a b) :=
    ActualGapProbabilityR26.in_probability _ (fun n => err D (n + 1)) _ _
      (fun n m => err_nonneg D _ m) he (fun m hm => default_sequence hκ u hu D hab ha hb default m hm)
  have hpall : TendstoInProbability (law hκ u hu)
      (fun _ => gapWithDefault L κ a b default) (D.omega a b) := by
    intro ε hε
    exact (tendsto_add_atTop_iff_nat 1).1 (hp ε hε)
  have hr : 0 < radius hκ u a b := by unfold radius; positivity
  have hbound : ∀ (n : ℕ) (m : MArr (n + 1)), m ∈ good hκ u a b (n + 1) →
      |gapWithDefault L κ a b default m| ≤ F02Tightness.Kab L κ (radius hκ u a b) a b := by
    intro n m hm
    rw [gapWithDefault,ite_eq_left (donor_on_good hκ u ha hb hm)]
    exact F02Tightness.good_bound (Fact.out : 0 < L) hκ (Nat.succ_pos n) hr hab hm
  have hv := variance_limit (fun n => law hκ u hu (n + 1))
    (fun n => gapWithDefault L κ a b default (N := n + 1))
    (fun n m => occVec (n + 1) m a) (fun n => good hκ u a b (n + 1))
    (D.omega a b) (F02Tightness.Kab L κ (radius hκ u a b) a b)
    (fun _ m => (weight_bounds m a).1) (fun _ m => (weight_bounds m a).2) hbound hp
  have hvall : Tendsto (V hκ u hu a b default (D.omega a b)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 hv
  have heall : Tendsto (meanOccupationError hκ u hu) atTop (𝓝 0) :=
    F02TightnessActual.eN_born_tendsto hκ u hu
  have hprob : ∀ N : ℕ, (law hκ u hu N) (good hκ u a b N)ᶜ ≤
      meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b) := by
    intro N
    exact F02Tightness.prob_compl_le (I := II hκ u) _ hr
      (by unfold radius; linarith [min_le_left (II hκ u a) (II hκ u b)])
      (by unfold radius; linarith [min_le_right (II hκ u a) (II hκ u b)])
  refine ⟨hpall,hvall,fun T => ?_⟩
  have htime : ∀ N : ℕ, EpsSq hκ u hu a b default (D.omega a b) T N ≤
      ENNReal.ofReal (T ^ 2) * V hκ u hu a b default (D.omega a b) N +
      4 * meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b) := by
    intro N
    refine (phase_bound (law hκ u hu) (fun _ => gapWithDefault L κ a b default)
      (fun N m => occVec N m a) (good hκ u a b) (fun _ => {m | 1 ≤ m.1 a})
      (D.omega a b) T (fun _ m => (weight_bounds m a).1) (fun _ m => (weight_bounds m a).2) N).trans ?_
    apply add_le_add le_rfl
    have hh : (4 : ℝ≥0∞) * (law hκ u hu N) (good hκ u a b N)ᶜ ≤
        4 * (meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b)) := by
      gcongr
      exact hprob N
    simpa only [mul_div_assoc] using hh
  have ht : Tendsto (fun N : ℕ => ENNReal.ofReal (T ^ 2) * V hκ u hu a b default (D.omega a b) N +
      4 * meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (T ^ 2)) hvall (Or.inr ENNReal.ofReal_ne_top)
    have h2 := ENNReal.Tendsto.const_mul heall (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
    have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne'))
    simpa only [mul_zero,zero_mul,add_zero,div_eq_mul_inv] using h1.add h3
  exact ⟨htime,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) htime⟩

/-- **R-1E0C40B3, CC:F04:actual-gap.** Actual-law cubic-energy gaps, their
oriented frequency cocycle, truncated variance, and compact-time phase error.
All response/bulk data are conclusions, and the zero-donor values are arbitrary. -/
theorem actual_law_cubic_energy_gaps (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 u) :
    ∃ D : Data hκ u,
      (∀ a b : ℤ, 0 < II hκ u a → 0 < II hκ u b →
        IntervalIntegrable D.integrand volume (b : ℝ) a) ∧
      (∀ a : ℤ, D.omega a a = 0) ∧
      (∀ a b : ℤ, D.omega a b = -D.omega b a) ∧
      (∀ a b d : ℤ, 0 < II hκ u a → 0 < II hκ u b → 0 < II hκ u d →
        D.omega a b + D.omega b d = D.omega a d) ∧
      Tendsto (meanOccupationError hκ u hu) atTop (𝓝 0) ∧
      (∀ (default : ∀ N, MArr N → ℝ) (a b : ℤ), a ≠ b → 0 < II hκ u a → 0 < II hκ u b →
        TendstoInProbability (law hκ u hu) (fun _ => gapWithDefault L κ a b default) (D.omega a b) ∧
        Tendsto (V hκ u hu a b default (D.omega a b)) atTop (𝓝 0) ∧
        (∀ T : ℝ,
          (∀ N : ℕ, EpsSq hκ u hu a b default (D.omega a b) T N ≤
            ENNReal.ofReal (T ^ 2) * V hκ u hu a b default (D.omega a b) N +
              4 * meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b)) ∧
          Tendsto (EpsSq hκ u hu a b default (D.omega a b) T) atTop (𝓝 0))) := by
  obtain ⟨D⟩ := data_exists hκ u hu hH
  obtain ⟨m,hm⟩ := ActualGapProbabilityR26.select_sequence
    (fun n => law hκ u hu (n + 1)) (fun n => err D (n + 1))
    (fun _ m => err_nonneg D _ m) (err_probability hκ u hu hH D)
  have hi : ∀ a b : ℤ, 0 < II hκ u a → 0 < II hκ u b →
      IntervalIntegrable D.integrand volume (b : ℝ) a := by
    intro a b ha hb
    by_cases hab : a = b
    · subst b; exact IntervalIntegrable.refl
    · exact (deterministic_actual hκ u hu D hab ha hb m hm).1
  refine ⟨D,hi,?_,?_,?_,F02TightnessActual.eN_born_tendsto hκ u hu,?_⟩
  · intro a; simp [Data.omega]
  · intro a b
    unfold Data.omega
    rw [intervalIntegral.integral_symm (a := (b : ℝ)) (b := (a : ℝ))]
    ring
  · intro a b d ha hb hd
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi b d hb hd) (hi a b ha hb)
    unfold Data.omega
    rw [← mul_add,add_comm (∫ lam in (b : ℝ)..(a : ℝ), D.integrand lam),hh]
  · intro default a b hab ha hb
    exact pair_conclusions hκ u hu hH D hab ha hb default

end QuantumNLS.ActualGapR26
#print axioms QuantumNLS.ActualGapR26.actual_law_cubic_energy_gaps

-- Audit every own/generated declaration in all five new proof modules.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let prefixes := ["QuantumNLS.ActualGapProbabilityR26.", "QuantumNLS.ActualGapDataR26.",
    "QuantumNLS.ActualGapTransferR26.", "QuantumNLS.ActualGapMomentsR26.", "QuantumNLS.ActualGapR26."]
  let mut pending : Array Lean.Name := #[]
  let mut ownCount : Nat := 0
  for (n, _) in env.constants.toList do
    if prefixes.any (fun p => n.toString.startsWith p || n.toString.startsWith ("_private." ++ p)) then
      pending := pending.push n
      ownCount := ownCount + 1
  let mut seen : Std.HashSet Lean.Name := {}
  let mut mods : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some idx := env.getModuleIdxFor? n then
        mods := mods.insert env.header.moduleNames[idx.toNat]!
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Actual gap audit PASS: {ownCount} own/generated constants; {seen.size} transitive constants; standard only."
  let qm := ((mods.toList.filter fun m => m.getRoot == `QuantumNLS).map toString).toArray.qsort (· < ·)
  Lean.logInfo m!"QuantumNLS contributing modules ({qm.size}): {qm}"
