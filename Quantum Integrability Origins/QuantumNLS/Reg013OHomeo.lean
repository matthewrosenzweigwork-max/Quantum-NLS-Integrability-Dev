import QuantumNLS.Reg013OOrder

/-! REG-013 (`lem:regularity-induction`, `fractional_moments.tex:610`), opus_tensor stage O5:
the conditional homeomorphism at an order `k < s ≤ k+1`.

For a homeomorphism `Φ : L² → V ⊂ ℓ²` with `|Φ_n(u)|² = I_n(u)` (`ExactModuli`), the restriction
`H^s → V ∩ h^s` is a homeomorphism. Forward continuity is weighted-action continuity at order
`s`. For the inverse, as printed: "first use the already proved order-`k` inverse continuity, and
then use continuity of the order-`s` correction to recover convergence of `Q_s`" (here: action
tails give moment tails by confinement, weak continuity gives `𝓜_{2s}` convergence, the order-`s`
identity and continuity of the correction give `Q_s` convergence, which upgrades the `H^k`
convergence to `H^s`). The base-map hypothesis is kept: the statement quantifies over every such
`Φ`, exactly as in `CondHomeo`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.Reg015Setting QuantumNLS.Reg013OAnalysis QuantumNLS.Reg013OCorrection
open QuantumNLS.Reg013OCells QuantumNLS.Reg013OOrder
namespace QuantumNLS.Reg013OHomeo
variable {L κ : ℝ} [Fact (0 < L)]

theorem seq_ext {a b : Seq} (h : ∀ n, a n = b n) : a = b := lp.ext (funext h)

/-! ### The two maps -/

/-- The forward sequence `(Φ_n(u))_n ∈ h^s`. -/
def fwdSeq (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ) {s : ℝ}
    (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) : h02 L s :=
  h02.ofMem (L := L) (s := s) (x := fun n => (e u.val).val n) (by
    show Summable fun n => sobolevWeight L s n * ‖(e u.val).val n‖^2
    simp_rw [hex u.val]
    exact actions_summable hκ hmcs u)

theorem fwdSeq_val (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ)
    {s : ℝ} (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) (n : ℤ) :
    (fwdSeq hκ e hex hmcs u).val n = (e u.val).val n := rfl

theorem toBase_fwd (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ)
    {s : ℝ} (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) :
    toBase s hs0 (fwdSeq hκ e hex hmcs u) = (e u.val).val :=
  seq_ext fun n => by rw [toBase_apply]; rfl

def fwd (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ) {s : ℝ}
    (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) : Target (L := L) V s hs0 :=
  ⟨fwdSeq hκ e hex hmcs u, by rw [toBase_fwd hκ e hex hs0 hmcs u]; exact (e u.val).2⟩

/-- The inverse at the `L²` level, `Φ⁻¹(z)`. -/
def bwdL2 {V : Set Seq} (e : L2T L ≃ₜ V) {s : ℝ} (hs0 : 0 ≤ s)
    (y : Target (L := L) V s hs0) : L2T L :=
  e.symm ⟨toBase s hs0 y.val, y.2⟩

theorem e_bwdL2 {V : Set Seq} (e : L2T L ≃ₜ V) {s : ℝ} (hs0 : 0 ≤ s)
    (y : Target (L := L) V s hs0) : e (bwdL2 e hs0 y) = ⟨toBase s hs0 y.val, y.2⟩ :=
  e.apply_symm_apply _

theorem masses_bwd (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ)
    {s : ℝ} (hs0 : 0 ≤ s) (y : Target (L := L) V s hs0) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (bwdL2 e hs0 y)).1 n = ‖y.val.val n‖^2 := by
  rw [← hex, e_bwdL2]
  show ‖toBase s hs0 y.val n‖^2 = _
  rw [toBase_apply]

theorem bwd_exists (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ)
    {s : ℝ} (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (y : Target (L := L) V s hs0) :
    ∃ w : H02 L s, w.val = bwdL2 e hs0 y := by
  refine (hmcs _).1.mpr ((hmcs _).2.mpr ?_)
  simp_rw [masses_bwd hκ e hex hs0 y]
  exact y.val.summable

def bwd (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ) {s : ℝ}
    (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (y : Target (L := L) V s hs0) : H02 L s :=
  Classical.choose (bwd_exists hκ e hex hs0 hmcs y)

theorem bwd_val (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ) {s : ℝ}
    (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (y : Target (L := L) V s hs0) :
    (bwd hκ e hex hs0 hmcs y).val = bwdL2 e hs0 y :=
  Classical.choose_spec (bwd_exists hκ e hex hs0 hmcs y)

theorem bwd_fwd (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ) {s : ℝ}
    (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) :
    bwd hκ e hex hs0 hmcs (fwd hκ e hex hs0 hmcs u) = u := by
  apply WField.ext
  rw [bwd_val]
  unfold bwdL2
  have : (⟨toBase s hs0 (fwd hκ e hex hs0 hmcs u).val, (fwd hκ e hex hs0 hmcs u).2⟩ : V) =
      e u.val := Subtype.ext (toBase_fwd hκ e hex hs0 hmcs u)
  rw [this, e.symm_apply_apply]

theorem fwd_bwd (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ) {s : ℝ}
    (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s) (y : Target (L := L) V s hs0) :
    fwd hκ e hex hs0 hmcs (bwd hκ e hex hs0 hmcs y) = y := by
  apply Subtype.ext
  apply PosWeight.WSeq.ext
  funext n
  show (e (bwd hκ e hex hs0 hmcs y).val).val n = y.val.val n
  rw [bwd_val, e_bwdL2]
  show toBase s hs0 y.val n = _
  rw [toBase_apply]

/-! ### Helpers -/

omit [Fact (0 < L)] in
theorem h02_mono_val {s t : ℝ} (h : s ≤ t) (x : h02 L t) : (h02_mono L h x).val = x.val :=
  PosWeight.incl_val _ _ _ _ x

theorem wfield_val_sub {s : ℝ} (u v : H02 L s) : (u - v).val = u.val - v.val := rfl

theorem sq_norm_sub_le (a b : ℂ) : ‖a - b‖^2 ≤ 2 * (‖a‖^2 + ‖b‖^2) := by
  have h := norm_sub_le a b
  have h0 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem tendsto_of_sq {X : Type*} [NormedAddCommGroup X] {f : ℕ → X} {g : X}
    (h : Tendsto (fun j => ‖f j - g‖^2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 g) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)

theorem tails_add {ι : Type*} [DecidableEq ι] (a b : ℕ → ι → ℝ) (ha0 : ∀ j n, 0 ≤ a j n)
    (hb0 : ∀ j n, 0 ≤ b j n) (has : ∀ j, Summable (a j)) (hbs : ∀ j, Summable (b j))
    (hta : ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, a j n ≤ ε)
    (htb : ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, b j n ≤ ε) :
    ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, (a j n + b j n) ≤ ε := by
  intro ε hε
  obtain ⟨F₁, h₁⟩ := hta (ε/2) (by positivity)
  obtain ⟨F₂, h₂⟩ := htb (ε/2) (by positivity)
  refine ⟨F₁ ∪ F₂, ?_⟩
  filter_upwards [h₁, h₂] with j hj1 hj2
  rw [Summable.tsum_add (f := fun n : {n // n ∉ F₁ ∪ F₂} => a j n)
    (g := fun n : {n // n ∉ F₁ ∪ F₂} => b j n)
    ((has j).comp_injective Subtype.val_injective) ((hbs j).comp_injective Subtype.val_injective)]
  have e1 := tail_anti (F := F₁) (G := F₁ ∪ F₂) Finset.subset_union_left (ha0 j) (has j)
  have e2 := tail_anti (F := F₂) (G := F₁ ∪ F₂) Finset.subset_union_right (hb0 j) (hbs j)
  linarith

theorem h02_coord_tendsto {s : ℝ} (hs0 : 0 ≤ s) {zs : ℕ → h02 L s} {z : h02 L s}
    (h : Tendsto zs atTop (𝓝 z)) (n : ℤ) :
    Tendsto (fun j => (zs j).val n) atTop (𝓝 (z.val n)) := by
  have h1 : Tendsto (fun j => toBase (L := L) s hs0 (zs j)) atTop (𝓝 (toBase s hs0 z)) :=
    ((toBase (L := L) s hs0).continuous.tendsto z).comp h
  have h2 := lp_coord_tendsto h1 n
  simpa only [toBase_apply] using h2

/-! ### Continuity of the forward map -/

theorem fwd_continuous (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ)
    {k : ℕ} {s : ℝ} (hks : (k:ℝ) ≤ s) (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s)
    {Jc : Hk L k → ℝ} (hJc : Continuous Jc) (hId : Identity hκ k s Jc) :
    Continuous (fwd hκ e hex hs0 hmcs) := by
  rw [continuous_iff_seqContinuous]
  intro us u h
  apply tendsto_subtype_rng.mpr
  apply tendsto_of_sq
  simp_rw [PosWeight.norm_sq_eq_tsum _ (_ - _), PosWeight.WSeq.val_sub, Pi.sub_apply]
  have hcoord : ∀ n : ℤ, Tendsto (fun j => (e (us j).val).val n) atTop (𝓝 ((e u.val).val n)) := by
    have h1 : Tendsto (fun j => (e (us j).val).val) atTop (𝓝 (e u.val).val) :=
      ((continuous_subtype_val.comp e.continuous).tendsto u.val).comp (val_tendsto hs0 h)
    exact fun n => lp_coord_tendsto h1 n
  refine tsum_tendsto_zero_of_dom
    (fun j n => (def002 L s).w n * ‖(fwd hκ e hex hs0 hmcs (us j)).val.val n -
      (fwd hκ e hex hs0 hmcs u).val.val n‖^2)
    (fun j n => (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j).val).1 n)
    (fun n => (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n)
    (C := 2) (by norm_num)
    (fun j n => mul_nonneg ((def002 L s).pos n).le (sq_nonneg _))
    (fun j n => mul_nonneg (by positivity) (masses_nonneg hκ _ n))
    (fun n => mul_nonneg (by positivity) (masses_nonneg hκ _ n))
    (fun j n => ?_) (fun j => actions_summable hκ hmcs (us j)) (actions_summable hκ hmcs u)
    (fun n => ?_) (action_tails_of_Hs hκ hks hmcs hJc hId h)
  · show (1 + |momentum L n|)^(2*s) * ‖(e (us j).val).val n - (e u.val).val n‖^2 ≤ _
    rw [← hex (us j).val n, ← hex u.val n]
    have := sq_norm_sub_le ((e (us j).val).val n) ((e u.val).val n)
    have hw : 0 ≤ (1 + |momentum L n|)^(2*s) := by positivity
    nlinarith
  · show Tendsto (fun j => (1 + |momentum L n|)^(2*s) *
      ‖(e (us j).val).val n - (e u.val).val n‖^2) atTop (𝓝 0)
    have h2 : Tendsto (fun j => ‖(e (us j).val).val n - (e u.val).val n‖^2) atTop (𝓝 0) := by
      have := (((continuous_norm.tendsto _).comp ((hcoord n).sub_const ((e u.val).val n))).pow 2)
      simpa using this
    simpa using h2.const_mul ((1 + |momentum L n|)^(2*s))

/-! ### Continuity of the inverse map -/

theorem bwd_continuous (hκ : 0 < κ) {V : Set Seq} (e : L2T L ≃ₜ V) (hex : ExactModuli e hκ)
    {k : ℕ} {s : ℝ} (hks : (k:ℝ) ≤ s) (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s)
    (hchk : CondHomeo (L := L) hκ k (Nat.cast_nonneg k))
    {Jc : Hk L k → ℝ} (hJc : Continuous Jc) (hId : Identity hκ k s Jc) :
    Continuous (bwd hκ e hex hs0 hmcs) := by
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  rw [continuous_iff_seqContinuous]
  intro ys y h
  have hz : Tendsto (fun j => (ys j).val) atTop (𝓝 y.val) :=
    (continuous_subtype_val.tendsto y).comp h
  -- Step A: order-`k` inverse continuity
  obtain ⟨Fk, hFk⟩ := hchk V e hex
  have hmono_base : ∀ y' : Target (L := L) V s hs0,
      toBase (k:ℝ) hk0 (h02_mono L hks y'.val) = toBase s hs0 y'.val :=
    fun y' => seq_ext fun n => by rw [toBase_apply, toBase_apply, h02_mono_val]
  let g : Target (L := L) V s hs0 → Target (L := L) V (k:ℝ) hk0 := fun y' =>
    ⟨h02_mono L hks y'.val, by rw [hmono_base]; exact y'.2⟩
  have hg : Continuous g :=
    ((h02_mono L hks).continuous.comp continuous_subtype_val).subtype_mk _
  have hFkinv : ∀ y', (Fk.symm (g y')).val = bwdL2 e hs0 y' := by
    intro y'
    have h1 := hFk (Fk.symm (g y'))
    simp only [Homeomorph.apply_symm_apply] at h1
    have he : e (Fk.symm (g y')).val = ⟨toBase s hs0 y'.val, y'.2⟩ := by
      apply Subtype.ext
      apply seq_ext
      intro n
      rw [← h1 n, toBase_apply]
      show (h02_mono L hks y'.val).val n = _
      rw [h02_mono_val]
    unfold bwdL2
    rw [← he, e.symm_apply_apply]
  have hA : Tendsto (fun j => Fk.symm (g (ys j))) atTop (𝓝 (Fk.symm (g y))) :=
    ((Fk.symm.continuous.comp hg).tendsto y).comp h
  have hv : Tendsto (fun j => bwdL2 e hs0 (ys j)) atTop (𝓝 (bwdL2 e hs0 y)) := by
    have := val_tendsto hk0 hA
    simpa only [Function.comp, hFkinv] using this
  -- notation
  set ws := fun j => bwd hκ e hex hs0 hmcs (ys j) with hws
  set w := bwd hκ e hex hs0 hmcs y with hw
  have hwsv : ∀ j, (ws j).val = bwdL2 e hs0 (ys j) := fun j => bwd_val hκ e hex hs0 hmcs (ys j)
  have hwv : w.val = bwdL2 e hs0 y := bwd_val hκ e hex hs0 hmcs y
  have hvL : Tendsto (fun j => (ws j).val) atTop (𝓝 w.val) := by
    simp_rw [hwsv, hwv]; exact hv
  -- Step B: action tails, from `h^s` convergence of the images
  have hact_tails : ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (ws j).val).1 n ≤ ε := by
    have e1 : ∀ j n, (1 + |momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ (ws j).val).1 n =
        (def002 L s).w n * ‖(ys j).val.val n‖^2 := fun j n => by
      rw [hwsv, masses_bwd hκ e hex hs0, weight_eq]
    simp_rw [e1]
    refine tails_of_tsum_tendsto _ (fun n => (def002 L s).w n * ‖y.val.val n‖^2)
      (fun j => (ys j).val.summable) y.val.summable
      (fun n => (((continuous_norm.tendsto _).comp (h02_coord_tendsto hs0 hz n)).pow 2).const_mul _) ?_
    have hn : Tendsto (fun j => ‖(ys j).val‖^2) atTop (𝓝 (‖y.val‖^2)) :=
      ((continuous_norm.tendsto _).comp hz).pow 2
    simp_rw [PosWeight.norm_sq_eq_tsum] at hn
    exact hn
  -- Step C: moment tails
  obtain ⟨MU, hMU⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hvL)
  have hmom_tails := moment_tails hκ (fun j => (ws j).val) (MU := MU) (fun j => hMU _ ⟨j, rfl⟩) hs0
    (fun j => power_integrable hκ hs0 hmcs (ws j)) (fun j => actions_summable hκ hmcs (ws j))
    hact_tails
  -- Step D: moment convergence
  have hM := integral_tendsto_of_tail _ _ (weak_tendsto hκ hvL) _ (continuous_power s hs0)
    (fun x => Real.rpow_nonneg (abs_nonneg x) _) (fun j => power_integrable hκ hs0 hmcs (ws j))
    (power_integrable hκ hs0 hmcs w) hmom_tails
  -- Step E: `Q_s` convergence via the identity and the continuity of the correction
  have hsum : ∀ v : H02 L s, Summable fun n : ℤ => |momentum L n|^(2*s) * ‖fourierL2 L v.val n‖^2 :=
    fun v => (summable_weight_iff hs0 v.val).mp v.summable
  have hid : ∀ (y' : Target (L := L) V s hs0),
      (∫ x, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (bwdL2 e hs0 y'))) =
        (∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L (bwdL2 e hs0 y') n‖^2) +
          Jc (Fk.symm (g y')) := by
    intro y'
    have h1 := (hId (Fk.symm (g y'))).2
    rw [hFkinv] at h1
    apply h1
    have := hsum (bwd hκ e hex hs0 hmcs y')
    rwa [bwd_val] at this
  have hJ : Tendsto (fun j => Jc (Fk.symm (g (ys j)))) atTop (𝓝 (Jc (Fk.symm (g y)))) :=
    (hJc.tendsto _).comp hA
  have hQ : Tendsto (fun j => ∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L (ws j).val n‖^2)
      atTop (𝓝 (∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L w.val n‖^2)) := by
    simp_rw [hwsv, hwv] at hM ⊢
    simp_rw [hid] at hM
    have := hM.sub hJ
    simpa using this
  -- Step F: `H^s` convergence
  apply tendsto_of_sq
  simp_rw [WField.norm_sq_eq_tsum, wfield_val_sub, map_sub, lp.coeFn_sub, Pi.sub_apply]
  have hcoef : ∀ n : ℤ, Tendsto (fun j => fourierL2 L (ws j).val n) atTop (𝓝 (fourierL2 L w.val n)) :=
    fun n => lp_coord_tendsto (((fourierL2 L).continuous.tendsto _).comp hvL) n
  have hl2 : ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      ‖fourierL2 L (ws j).val n‖^2 ≤ ε := by
    refine tails_of_tsum_tendsto _ (fun n => ‖fourierL2 L w.val n‖^2)
      (fun j => PosWeight.summable_sq_of_lp _) (PosWeight.summable_sq_of_lp _)
      (fun n => ((continuous_norm.tendsto _).comp (hcoef n)).pow 2) ?_
    have hn : Tendsto (fun j => ‖fourierL2 L (ws j).val‖^2) atTop (𝓝 (‖fourierL2 L w.val‖^2)) :=
      ((continuous_norm.tendsto _).comp (((fourierL2 L).continuous.tendsto _).comp hvL)).pow 2
    simp_rw [lp_norm_sq_tsum] at hn
    exact hn
  have hqt : ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      |momentum L n|^(2*s) * ‖fourierL2 L (ws j).val n‖^2 ≤ ε :=
    tails_of_tsum_tendsto _ _ (fun j => hsum (ws j)) (hsum w)
      (fun n => (((continuous_norm.tendsto _).comp (hcoef n)).pow 2).const_mul _) hQ
  have hall := tails_add _ _ (fun j n => sq_nonneg _)
    (fun j n => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))
    (fun j => PosWeight.summable_sq_of_lp _) (fun j => hsum (ws j)) hl2 hqt
  refine tsum_tendsto_zero_of_dom
    (fun j n => (def002 L s).w n * ‖fourierL2 L (ws j).val n - fourierL2 L w.val n‖^2)
    (fun j n => ‖fourierL2 L (ws j).val n‖^2 + |momentum L n|^(2*s) * ‖fourierL2 L (ws j).val n‖^2)
    (fun n => ‖fourierL2 L w.val n‖^2 + |momentum L n|^(2*s) * ‖fourierL2 L w.val n‖^2)
    (C := 2 * 2^(2*s)) (by positivity)
    (fun j n => mul_nonneg ((def002 L s).pos n).le (sq_nonneg _))
    (fun j n => add_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)))
    (fun n => add_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)))
    (fun j n => ?_)
    (fun j => (PosWeight.summable_sq_of_lp _).add (hsum (ws j)))
    ((PosWeight.summable_sq_of_lp _).add (hsum w))
    (fun n => ?_) hall
  · have h1 := sq_norm_sub_le (fourierL2 L (ws j).val n) (fourierL2 L w.val n)
    have h2 : (def002 L s).w n ≤ 2^(2*s) * (1 + |momentum L n|^(2*s)) :=
      one_add_rpow_le |momentum L n| (2*s) (abs_nonneg _) (by linarith)
    have hW : 0 ≤ (def002 L s).w n := ((def002 L s).pos n).le
    have hp : 0 ≤ |momentum L n|^(2*s) := Real.rpow_nonneg (abs_nonneg _) _
    have ha := sq_nonneg ‖fourierL2 L (ws j).val n‖
    have hb := sq_nonneg ‖fourierL2 L w.val n‖
    calc (def002 L s).w n * ‖fourierL2 L (ws j).val n - fourierL2 L w.val n‖^2
        ≤ (2^(2*s) * (1 + |momentum L n|^(2*s))) *
            (2 * (‖fourierL2 L (ws j).val n‖^2 + ‖fourierL2 L w.val n‖^2)) :=
          mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
      _ = 2 * 2^(2*s) * ((‖fourierL2 L (ws j).val n‖^2 +
            |momentum L n|^(2*s) * ‖fourierL2 L (ws j).val n‖^2) +
            (‖fourierL2 L w.val n‖^2 + |momentum L n|^(2*s) * ‖fourierL2 L w.val n‖^2)) := by ring
  · have h2 : Tendsto (fun j => ‖fourierL2 L (ws j).val n - fourierL2 L w.val n‖^2) atTop (𝓝 0) := by
      have := (((continuous_norm.tendsto _).comp ((hcoef n).sub_const (fourierL2 L w.val n))).pow 2)
      simpa using this
    simpa using h2.const_mul ((def002 L s).w n)

/-! ### The conditional homeomorphism at order `s` -/

theorem condHomeo_of (hκ : 0 < κ) {k : ℕ} {s : ℝ} (hks : (k:ℝ) ≤ s)
    (hmcs : MomentChar (L := L) hκ s) (hchk : CondHomeo (L := L) hκ k (Nat.cast_nonneg k))
    {Jc : Hk L k → ℝ} (hJc : Continuous Jc) (hId : Identity hκ k s Jc) (hs0 : 0 ≤ s) :
    CondHomeo (L := L) hκ s hs0 := by
  intro V e hex
  refine ⟨{ toFun := fwd hκ e hex hs0 hmcs
            invFun := bwd hκ e hex hs0 hmcs
            left_inv := bwd_fwd hκ e hex hs0 hmcs
            right_inv := fwd_bwd hκ e hex hs0 hmcs
            continuous_toFun := fwd_continuous hκ e hex hks hs0 hmcs hJc hId
            continuous_invFun := bwd_continuous hκ e hex hks hs0 hmcs hchk hJc hId }, ?_⟩
  intro u n
  rfl

end QuantumNLS.Reg013OHomeo

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg013OHomeo." ||
        n.toString.startsWith "_private.QuantumNLS.Reg013OHomeo." then
      pending := pending.push n
      roots := roots + 1
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
          throwError "Held name in closure: {n}"
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Reg013OHomeo aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
