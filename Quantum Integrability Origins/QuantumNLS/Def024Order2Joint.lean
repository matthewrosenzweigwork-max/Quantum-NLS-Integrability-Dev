import QuantumNLS.Def024CubicSmoothFlow
import QuantumNLS.Def024CubicLowComm2
import QuantumNLS.PhysicalCubic

/-!
# DEF-024, orders `r ≤ 2`: the joint flow for every `𝓡 ⊆ {0,1,2}` (opus_tensor, stage D4)

`DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex:147`, `def:report-24`):

"For a fixed finite set of nonnegative orders `𝓡`, the joint classical flow is the composition of
the Hamiltonian flows of `I_{r+1}^{(κ)}`, and the quantum flow is
`U_N(t) = exp(−i Σ_{r∈𝓡} t_r Q_{N,r})`. The correspondence tests a fixed smooth unit initial field
and a fixed compact box of times. Existence and commutation of the higher classical flows are proved
with finite loss."

Read-only inputs (all frozen): the frozen `HierarchyFlow` interface (`IsHamFlow`, `HamFlows`,
`jointClassicalFlow`); the review D1–D3 (`Def024LowFlows`, `Def024LowEquivariance`: orders 0, 1 and
`UniqueHamFlow`); the auxiliary construction `Def024CubicUnique.unique_two` (uniqueness of the order-2 flow in the smooth
class, `κ ≥ 0`) and `Def024CubicLowComm2` (commutation of order 2 with orders 0, 1); Sol r103
`Def024CubicSmoothFlow.isHamFlow` (existence of the order-2 flow, all real times); DEF-023
`PhysicalCubic.physicalCubic` and `L2Flow.flowMap_H1` (agreement of the `L²` Duhamel flow with the
`H¹` flow).

Proved here (no hypothesis beyond `0 < L` (the ambient `Fact`) and `0 ≤ κ`, which contains the
printed range `κ > 0`):
* `group_of_unique`: for EVERY order `r`, an `IsHamFlow` of `Re I_{r+1}` that is unique in the
  smooth class (`UniqueHamFlow`) satisfies the group law `Φ_s ∘ Φ_a = Φ_{s+a}` on smooth periodic
  data (time-shift argument, no further input);
* `flowMap2`, `hamFlows2`: an actual `HamFlows L κ 𝓡` for every `𝓡 ⊆ {0,1,2}`;
  `flowMap2_unique`: each of its flows is `UniqueHamFlow` (PROVED for orders 0, 1, 2, not assumed);
* `flowMap2_comm`: UNCONDITIONAL pairwise commutation of all flows of orders 0, 1, 2, all real
  times, all smooth periodic data, including each flow with itself at different times;
* `jointClassicalFlow_eq`: every `HamFlows` family on `𝓡 ⊆ {0,1,2}` has the same joint flow on
  smooth periodic data; `jointClassicalFlow_012`: for `𝓡 = {0,1,2}` it is
  `x ↦ e^{−it₀} (Φ²_{t₂} u)(x − t₁)`;
* `joint_contDiff_of`, `joint_deriv_bound`: the joint flow is `C^∞` jointly in
  `(t₀, t₁, t₂, x)` and every derivative is bounded on every compact set (in particular on the
  compact DEF-024 box times one period);
* `physicalCubic_eq`, `physicalCubic_eq_of_isHamFlow`: realization **via DEF-023**: for smooth
  periodic data the DEF-023 physical cubic (unique `C(ℝ;L²) ∩ L⁴_loc` Duhamel) solution is, at every
  time, the `L²` class of the order-2 Hamiltonian flow, for every `IsHamFlow` of `Re I_3`;
* `DEF024_order_le_two`: the bundled staged statement for `𝓡 ⊆ {0,1,2}`.

Finite loss for the individual flows is the frozen D2 (orders 0, 1) and Sol r103
`Def024CubicSmoothBounds` (order 2: `C^k_t H^m` from `H^{m+2k}`, `C^k_t C^m_x` from `H^{m+1+2k}`);
not restated. Joint smoothness in the initial datum is NOT claimed: line 147 fixes the initial field
("a fixed smooth unit initial field").
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff
open MeasureTheory

namespace QuantumNLS.Def024Order2Joint

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024LowFlows
  QuantumNLS.Def024LowEquivariance QuantumNLS.Def024CubicUnique QuantumNLS.Def024CubicLowComm2
  QuantumNLS.Def024CubicSmoothData QuantumNLS.DuhamelDuality

/-! ## 1. Group law from uniqueness (every order) -/

section Group

variable {L : ℝ}

open Classical in
/-- The flow `Φ` with the single trajectory through `Φ_a w` replaced by the time-shifted trajectory
`s ↦ Φ_{s+a} w`. -/
def shiftFlow (Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (a : ℝ) (w : ℝ → ℂ) :
    ℝ → (ℝ → ℂ) → (ℝ → ℂ) :=
  fun s z => if z = Φ a w then Φ (s + a) w else Φ s z

theorem shiftFlow_isHamFlow {F : (ℝ → ℂ) → ℝ} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L F Φ) {w : ℝ → ℂ} (hw : SmoothPeriodic L w) (a : ℝ) :
    IsHamFlow L F (shiftFlow Φ a w) := by
  intro z hz
  by_cases h : z = Φ a w
  · subst h
    have e : ∀ s, shiftFlow Φ a w s (Φ a w) = Φ (s + a) w := fun s => by simp [shiftFlow]
    simp only [e]
    obtain ⟨-, hcd, hs⟩ := hΦ w hw
    refine ⟨by rw [zero_add], ?_, fun s => ?_⟩
    · exact hcd.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
    · obtain ⟨hsm, g, hg, hd⟩ := hs (s + a)
      refine ⟨hsm, g, hg, fun x => ?_⟩
      have hh : HasDerivAt (fun s' : ℝ => s' + a) 1 s := (hasDerivAt_id' s).add_const a
      have := (hd x).scomp s hh
      rw [one_smul] at this
      exact this
  · have e : ∀ s, shiftFlow Φ a w s z = Φ s z := fun s => by simp [shiftFlow, h]
    simp only [e]
    exact hΦ z hz

/-- **Group law from uniqueness**, for every Hamiltonian `F` (in particular every order `r`). -/
theorem group_of_unique {F : (ℝ → ℂ) → ℝ} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L F Φ) (hU : UniqueHamFlow L F Φ) {w : ℝ → ℂ} (hw : SmoothPeriodic L w)
    (s a : ℝ) : Φ s (Φ a w) = Φ (s + a) w := by
  have hsm : SmoothPeriodic L (Φ a w) := ((hΦ w hw).2.2 a).1
  have h := hU _ (shiftFlow_isHamFlow hΦ hw a) (Φ a w) hsm s
  have e : shiftFlow Φ a w s (Φ a w) = Φ (s + a) w := by simp [shiftFlow]
  rw [e] at h
  exact h.symm

end Group

/-! ## 2. The flows of orders 0, 1, 2 -/

/-- The order-2 (cubic NLS) Hamiltonian flow of `Re I_3` (Sol r103, frozen). -/
def cubicFlow (L : ℝ) [Fact (0 < L)] (κ : ℝ) : ℝ → (ℝ → ℂ) → (ℝ → ℂ) :=
  QuantumNLS.Def024CubicSmoothFlow.Φ (L := L) κ

/-- The flow map of each order `r ≤ 2` (`0 ↦ e^{−is}`, `1 ↦` translation, `2 ↦` cubic NLS). The
value at `r ≥ 3` is a placeholder (identity) with NO Hamiltonian-flow claim. -/
def flowMap2 (L : ℝ) [Fact (0 < L)] (κ : ℝ) : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0 => phaseFlow
  | 1 => transFlow
  | 2 => cubicFlow L κ
  | _ + 3 => fun _ u => u

variable {L : ℝ} [Fact (0 < L)]

theorem cubicFlow_isHamFlow {κ : ℝ} (hκ : 0 ≤ κ) :
    IsHamFlow L (hamiltonian L κ 2) (cubicFlow L κ) :=
  QuantumNLS.Def024CubicSmoothFlow.isHamFlow κ hκ

theorem cubicFlow_smooth {κ : ℝ} (hκ : 0 ≤ κ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    SmoothPeriodic L (cubicFlow L κ t u) :=
  ((cubicFlow_isHamFlow hκ u hu).2.2 t).1

theorem mem012 {r : ℕ} (hr : r ∈ ({0, 1, 2} : Finset ℕ)) : r = 0 ∨ r = 1 ∨ r = 2 := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hr

/-- **Existence** for orders `0, 1, 2`, all real times. -/
theorem flowMap2_isHamFlow {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ} (hr : r ∈ ({0, 1, 2} : Finset ℕ)) :
    IsHamFlow L (hamiltonian L κ r) (flowMap2 L κ r) := by
  rcases mem012 hr with rfl | rfl | rfl
  · exact phase_isHamFlow κ
  · exact trans_isHamFlow κ
  · exact cubicFlow_isHamFlow hκ

/-- **Uniqueness** in the smooth class for orders `0, 1, 2` (proved, not assumed). -/
theorem flowMap2_unique {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ} (hr : r ∈ ({0, 1, 2} : Finset ℕ)) :
    UniqueHamFlow L (hamiltonian L κ r) (flowMap2 L κ r) := by
  rcases mem012 hr with rfl | rfl | rfl
  · exact (unique_low (L := L) Fact.out κ).1
  · exact (unique_low (L := L) Fact.out κ).2
  · exact unique_two hκ (cubicFlow_isHamFlow hκ)

theorem flowMap2_smooth {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ} (hr : r ∈ ({0, 1, 2} : Finset ℕ))
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) : SmoothPeriodic L (flowMap2 L κ r s u) :=
  ((flowMap2_isHamFlow hκ hr u hu).2.2 s).1

/-- Group law for orders `0, 1, 2`. -/
theorem flowMap2_add {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ} (hr : r ∈ ({0, 1, 2} : Finset ℕ))
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    flowMap2 L κ r s (flowMap2 L κ r a u) = flowMap2 L κ r (s + a) u :=
  group_of_unique (flowMap2_isHamFlow hκ hr) (flowMap2_unique hκ hr) hu s a

/-- **Unconditional pairwise commutation** of the flows of orders `0, 1, 2`. -/
theorem flowMap2_comm {κ : ℝ} (hκ : 0 ≤ κ) {r r' : ℕ} (hr : r ∈ ({0, 1, 2} : Finset ℕ))
    (hr' : r' ∈ ({0, 1, 2} : Finset ℕ)) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    flowMap2 L κ r s (flowMap2 L κ r' a u) = flowMap2 L κ r' a (flowMap2 L κ r s u) := by
  by_cases hrr : r = r'
  · subst hrr
    rw [flowMap2_add hκ hr hu, flowMap2_add hκ hr hu, add_comm]
  · have hΦ2 := cubicFlow_isHamFlow (L := L) hκ
    rcases mem012 hr with rfl | rfl | rfl <;> rcases mem012 hr' with rfl | rfl | rfl
    all_goals first | exact absurd rfl hrr | skip
    · exact phase_trans_comm s a u
    · exact (cubic_comm_phase hκ hΦ2 hu a s).symm
    · exact (phase_trans_comm a s u).symm
    · exact (cubic_comm_trans hκ hΦ2 hu a s).symm
    · exact cubic_comm_phase hκ hΦ2 hu s a
    · exact cubic_comm_trans hκ hΦ2 hu s a

/-- **An actual family of Hamiltonian flows** of `I_{r+1}`, `r ∈ 𝓡`, for every `𝓡 ⊆ {0,1,2}`. -/
def hamFlows2 (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 ≤ κ) (𝓡 : Finset ℕ)
    (h𝓡 : 𝓡 ⊆ {0, 1, 2}) : HamFlows L κ 𝓡 where
  Φ := flowMap2 L κ
  ham := fun _ hr => flowMap2_isHamFlow hκ (h𝓡 hr)

/-- Every `HamFlows` family on `𝓡 ⊆ {0,1,2}` agrees with `hamFlows2` on smooth periodic data. -/
theorem hamFlows2_eq {κ : ℝ} (hκ : 0 ≤ κ) {𝓡 : Finset ℕ} (h𝓡 : 𝓡 ⊆ {0, 1, 2})
    (F : HamFlows L κ 𝓡) {r : ℕ} (hr : r ∈ 𝓡) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    F.Φ r s u = flowMap2 L κ r s u :=
  flowMap2_unique hκ (h𝓡 hr) (F.Φ r) (F.ham r hr) u hu s

/-! ## 3. The joint flow -/

theorem foldr_eq {κ : ℝ} (hκ : 0 ≤ κ) {𝓡 : Finset ℕ} (h𝓡 : 𝓡 ⊆ {0, 1, 2})
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) :
    ∀ (l : List ℕ), (∀ r ∈ l, r ∈ 𝓡) → ∀ {u : ℝ → ℂ}, SmoothPeriodic L u →
      ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u =
          ((l.map fun r => flowMap2 L κ r (t r)).foldr (· ∘ ·) id) u ∧
        SmoothPeriodic L (((l.map fun r => flowMap2 L κ r (t r)).foldr (· ∘ ·) id) u)
  | [], _, _, hu => ⟨rfl, hu⟩
  | r :: l, hl, u, hu => by
    obtain ⟨h1, h2⟩ := foldr_eq hκ h𝓡 F t l (fun r' hr' => hl r' (by simp [hr'])) hu
    have hr : r ∈ 𝓡 := hl r (by simp)
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply]
    rw [h1]
    exact ⟨hamFlows2_eq hκ h𝓡 F hr h2 (t r), flowMap2_smooth hκ (h𝓡 hr) h2 (t r)⟩

/-- **Uniqueness of the joint flow**: all `HamFlows` families on `𝓡 ⊆ {0,1,2}` have the same joint
flow on smooth periodic data, and it preserves the smooth periodic class. -/
theorem jointClassicalFlow_eq {κ : ℝ} (hκ : 0 ≤ κ) {𝓡 : Finset ℕ} (h𝓡 : 𝓡 ⊆ {0, 1, 2})
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    jointClassicalFlow F t u = jointClassicalFlow (hamFlows2 L hκ 𝓡 h𝓡) t u :=
  (foldr_eq hκ h𝓡 F t (𝓡.sort (· ≤ ·)) (fun r hr => by simpa using hr) hu).1

theorem jointClassicalFlow_smooth {κ : ℝ} (hκ : 0 ≤ κ) {𝓡 : Finset ℕ} (h𝓡 : 𝓡 ⊆ {0, 1, 2})
    (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    SmoothPeriodic L (jointClassicalFlow (hamFlows2 L hκ 𝓡 h𝓡) t u) :=
  (foldr_eq hκ h𝓡 (hamFlows2 L hκ 𝓡 h𝓡) t (𝓡.sort (· ≤ ·)) (fun r hr => by simpa using hr) hu).2

theorem sort_012 : (({0, 1, 2} : Finset ℕ).sort (· ≤ ·)) = [0, 1, 2] := by
  rw [Finset.sort_insert (· ≤ ·) (by simp) (by simp), Finset.sort_insert (· ≤ ·) (by simp) (by simp),
    Finset.sort_singleton]

/-- **The joint flow for `𝓡 = {0,1,2}`**, for every `HamFlows` family: `e^{−it₀}(Φ²_{t₂}u)(x − t₁)`. -/
theorem jointClassicalFlow_012 {κ : ℝ} (hκ : 0 ≤ κ) (F : HamFlows L κ {0, 1, 2}) (t : ℕ → ℝ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    jointClassicalFlow F t u =
      fun x => Complex.exp (-Complex.I * t 0) * cubicFlow L κ (t 2) u (x - t 1) := by
  rw [jointClassicalFlow_eq hκ subset_rfl F t hu]
  simp only [jointClassicalFlow, sort_012, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, Function.comp_id]
  rfl

/-- The joint time `(t₀, t₁, t₂)` as a time vector `ℕ → ℝ` (zero-free; only orders `0,1,2` used). -/
def tvec (p : ℝ × ℝ × ℝ) : ℕ → ℝ
  | 0 => p.1
  | 1 => p.2.1
  | _ => p.2.2

theorem joint_contDiff {κ : ℝ} (hκ : 0 ≤ κ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      Complex.exp (-Complex.I * p.1.1) * cubicFlow L κ p.1.2.2 u (p.2 - p.1.2.1)) := by
  have hcub : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cubicFlow L κ q.1 u q.2) :=
    (cubicFlow_isHamFlow hκ u hu).2.1
  have h1 : ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => ((p.1.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)
  have hg : ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.2.2, p.2 - p.1.2.1)) :=
    (contDiff_snd.comp (contDiff_snd.comp contDiff_fst)).prodMk
      (contDiff_snd.sub (contDiff_fst.comp (contDiff_snd.comp contDiff_fst)))
  exact (contDiff_const.mul h1).cexp.mul (hcub.comp hg)

/-- **Joint `C^∞` regularity of the joint flow** in `(t₀, t₁, t₂, x)`, for every `HamFlows` family
on `{0,1,2}` and every fixed smooth periodic initial field. -/
theorem joint_contDiff_of {κ : ℝ} (hκ : 0 ≤ κ) (F : HamFlows L κ {0, 1, 2}) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => jointClassicalFlow F (tvec p.1) u p.2) := by
  have e : (fun p : (ℝ × ℝ × ℝ) × ℝ => jointClassicalFlow F (tvec p.1) u p.2) =
      fun p => Complex.exp (-Complex.I * p.1.1) * cubicFlow L κ p.1.2.2 u (p.2 - p.1.2.1) := by
    funext p
    rw [jointClassicalFlow_012 hκ F (tvec p.1) hu]
    rfl
  rw [e]
  exact joint_contDiff hκ hu

/-- Every derivative of the joint flow, of every order `k`, is bounded on every compact set of
joint times and positions (e.g. the DEF-024 box `∏[−T_r, T_r]` times `[0, L]`). -/
theorem joint_deriv_bound {κ : ℝ} (hκ : 0 ≤ κ) (F : HamFlows L κ {0, 1, 2}) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (k : ℕ) {K : Set ((ℝ × ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ p ∈ K, ‖iteratedFDeriv ℝ k
      (fun p : (ℝ × ℝ × ℝ) × ℝ => jointClassicalFlow F (tvec p.1) u p.2) p‖ ≤ B :=
  hK.exists_bound_of_continuousOn
    ((joint_contDiff_of hκ F hu).continuous_iteratedFDeriv (by simp)).continuousOn

/-! ## 4. Realization via DEF-023 -/

/-- The `L²(𝕋_L)` class of a smooth periodic profile. -/
def toL2 {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : HL L :=
  ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ (field hu)

theorem toL2_congr {u v : ℝ → ℂ} (hu : SmoothPeriodic L u) (hv : SmoothPeriodic L v)
    (h : u = v) : toL2 hu = toL2 hv := by
  subst h; rfl

theorem emb_eq (a : QuantumNLS.Sobolev.h04 L 1) :
    QuantumNLS.H1Bridge.emb a =
      ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
        (QuantumNLS.F04Regularity.S1 a) := rfl

theorem S1_datum {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    QuantumNLS.F04Regularity.S1 (datum hu 1) = field hu := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [QuantumNLS.F04Regularity.S1_apply, series_datum hu 1 y]
    exact (QuantumNLS.WeakDerivatives.liftC_coe _ _ y).symm

theorem S1_trajectory {κ : ℝ} (hκ : 0 ≤ κ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    QuantumNLS.F04Regularity.S1 (trajectory hu (le_refl (1 : ℝ)) κ t) =
      field (cubicFlow_smooth hκ hu t) := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [QuantumNLS.F04Regularity.S1_apply]
    change QuantumNLS.Def024CubicSmoothJoint.profile hu κ t y = _
    rw [show QuantumNLS.Def024CubicSmoothJoint.profile hu κ t = cubicFlow L κ t u from
      (QuantumNLS.Def024CubicSmoothFlow.Φ_of_smooth hu κ t).symm]
    exact (QuantumNLS.WeakDerivatives.liftC_coe _ _ y).symm

/-- **Realization of order 2 via DEF-023**: for every smooth periodic datum and every real time, the
DEF-023 physical cubic evolution (the unique `C(ℝ;L²) ∩ L⁴_loc` Duhamel solution) of its `L²` class
is the `L²` class of the order-2 Hamiltonian flow. -/
theorem physicalCubic_eq {κ : ℝ} (hκ : 0 ≤ κ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    QuantumNLS.PhysicalCubic.physicalCubic hκ (toL2 hu) t = toL2 (cubicFlow_smooth hκ hu t) := by
  have h0 : toL2 hu = QuantumNLS.H1Bridge.emb (datum hu 1) := by
    rw [emb_eq, S1_datum]; rfl
  have h1 : toL2 (cubicFlow_smooth hκ hu t) =
      QuantumNLS.H1Bridge.emb (trajectory hu (le_refl (1 : ℝ)) κ t) := by
    rw [emb_eq, S1_trajectory hκ hu t]; rfl
  rw [h0, h1]
  exact QuantumNLS.L2Flow.flowMap_H1 hκ (datum hu 1) t

/-- The same for EVERY Hamiltonian flow of `Re I_3` (frozen `IsHamFlow`). -/
theorem physicalCubic_eq_of_isHamFlow {κ : ℝ} (hκ : 0 ≤ κ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 2) Φ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    QuantumNLS.PhysicalCubic.physicalCubic hκ (toL2 hu) t = toL2 ((hΦ u hu).2.2 t).1 := by
  have e : Φ t u = cubicFlow L κ t u := unique_two hκ (cubicFlow_isHamFlow hκ) Φ hΦ u hu t
  rw [physicalCubic_eq hκ hu t]
  exact toL2_congr _ _ e.symm

/-! ## 5. Bundled staged statement -/

/-- **DEF-024 for every `𝓡 ⊆ {0,1,2}`** (`κ ≥ 0`, `0 < L`): an actual family of Hamiltonian
flows of `I_{r+1}` (all real times, joint `C^∞` in `(s,x)`, DEF-015 gradient); every family agrees
with it on smooth periodic data (each flow and the joint flow); all pairwise commutations and group
laws hold unconditionally; the joint flow preserves the smooth periodic class. -/
theorem DEF024_order_le_two {κ : ℝ} (hκ : 0 ≤ κ) (𝓡 : Finset ℕ) (h𝓡 : 𝓡 ⊆ {0, 1, 2}) :
    (∀ r ∈ 𝓡, IsHamFlow L (hamiltonian L κ r) ((hamFlows2 L hκ 𝓡 h𝓡).Φ r)) ∧
    (∀ G : HamFlows L κ 𝓡, ∀ r ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s : ℝ,
      G.Φ r s u = (hamFlows2 L hκ 𝓡 h𝓡).Φ r s u) ∧
    (∀ G : HamFlows L κ 𝓡, ∀ t : ℕ → ℝ, ∀ u : ℝ → ℂ, SmoothPeriodic L u →
      jointClassicalFlow G t u = jointClassicalFlow (hamFlows2 L hκ 𝓡 h𝓡) t u) ∧
    (∀ r ∈ 𝓡, ∀ r' ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s a : ℝ,
      (hamFlows2 L hκ 𝓡 h𝓡).Φ r s ((hamFlows2 L hκ 𝓡 h𝓡).Φ r' a u) =
        (hamFlows2 L hκ 𝓡 h𝓡).Φ r' a ((hamFlows2 L hκ 𝓡 h𝓡).Φ r s u)) ∧
    (∀ r ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s a : ℝ,
      (hamFlows2 L hκ 𝓡 h𝓡).Φ r s ((hamFlows2 L hκ 𝓡 h𝓡).Φ r a u) =
        (hamFlows2 L hκ 𝓡 h𝓡).Φ r (s + a) u) ∧
    (∀ t : ℕ → ℝ, ∀ u : ℝ → ℂ, SmoothPeriodic L u →
      SmoothPeriodic L (jointClassicalFlow (hamFlows2 L hκ 𝓡 h𝓡) t u)) :=
  ⟨fun r hr => flowMap2_isHamFlow hκ (h𝓡 hr),
    fun G r hr u hu s => hamFlows2_eq hκ h𝓡 G hr hu s,
    fun G t u hu => jointClassicalFlow_eq hκ h𝓡 G t hu,
    fun r hr r' hr' u hu s a => flowMap2_comm hκ (h𝓡 hr) (h𝓡 hr') hu s a,
    fun r hr u hu s a => flowMap2_add hκ (h𝓡 hr) hu s a,
    fun t u hu => jointClassicalFlow_smooth hκ h𝓡 t hu⟩

#print axioms shiftFlow_isHamFlow
#print axioms group_of_unique
#print axioms flowMap2_isHamFlow
#print axioms flowMap2_unique
#print axioms flowMap2_add
#print axioms flowMap2_comm
#print axioms hamFlows2_eq
#print axioms jointClassicalFlow_eq
#print axioms jointClassicalFlow_smooth
#print axioms jointClassicalFlow_012
#print axioms joint_contDiff_of
#print axioms joint_deriv_bound
#print axioms physicalCubic_eq
#print axioms physicalCubic_eq_of_isHamFlow
#print axioms DEF024_order_le_two

end QuantumNLS.Def024Order2Joint

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024Order2Joint." ||
        n.toString.startsWith "_private.QuantumNLS.Def024Order2Joint." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        if n.toString.endsWith "HeldGP14Tonelli" || n.toString.endsWith "RegularCut" then
          throwError "Held identifier: {n}"
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Def024Order2Joint aggregate audit PASS: {seen.size} transitive constants; standard axioms only."
