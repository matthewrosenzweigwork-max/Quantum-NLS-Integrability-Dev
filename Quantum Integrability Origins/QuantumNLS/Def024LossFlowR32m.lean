import QuantumNLS.Def024LossSequenceR32m

/-! Finite physical input levels for chart flows and finite compositions. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

open scoped ContDiff NNReal
open Set

namespace QuantumNLS.Def024LossR32m

open QuantumNLS.Fourier Sobolev Sobolev.PosWeight ClassicalCharges PhysicalTensor
open RB7 LossSobolev Loss HierarchyFlow SmoothScalarMomentsPhysical

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}
variable {ι : Type} [Fintype ι]

/-- Sum of the frequency-growth levels for the chosen family. -/
def orderLevel (order : ι → ℕ) : ℝ≥0 := ∑ r, SOf (order r)

/-- The inverse chart is used at this level before applying the loss lemma. -/
def chartLevel (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) : ℝ≥0 :=
  orderLevel order + (((m : ℝ≥0) + 2) * (q + 1) + 1)

/-- Finite physical input level for `m` time derivatives into `H^q`. -/
def inputLevel (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) : ℝ≥0 :=
  chartLevel order m q + 2 + (2 * (m : ℝ≥0)) * orderLevel order

private theorem order_le (order : ι → ℕ) (r : ι) : SOf (order r) ≤ orderLevel order :=
  Finset.single_le_sum (f := fun r => SOf (order r)) (fun _ _ => bot_le) (Finset.mem_univ r)

private theorem order_chart_le (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (r : ι) :
    SOf (order r) ≤ chartLevel order m q :=
  (order_le order r).trans le_self_add

private theorem chart_input_le (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) :
    chartLevel order m q ≤ inputLevel order m q :=
  le_self_add.trans le_self_add

private theorem loss_levels (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) :
    q + 1 ≤ chartLevel order m q ∧
      ((((m + 1 : ℕ) : ℝ) + 1) * ((q + 1 : ℝ≥0) : ℝ)) < (chartLevel order m q : ℝ) := by
  constructor
  · rw [← NNReal.coe_le_coe]
    push_cast [chartLevel]
    nlinarith [NNReal.coe_nonneg q, NNReal.coe_nonneg (orderLevel order), Nat.cast_nonneg (α := ℝ) m]
  · push_cast [chartLevel]
    linarith [NNReal.coe_nonneg (orderLevel order)]

private def forward (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (A : ℝ≥0) : (fieldScale L).Y A → (seqScale L).Y A :=
  fun u => ((Classical.choose (regHomeo hR C (A : ℝ) A.2)) u).val

private theorem forward_cont (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (A : ℝ≥0) : Continuous (forward hR C A) := by
  let F := Classical.choose (regHomeo hR C (A : ℝ) A.2)
  change Continuous (fun u : H02 L (A : ℝ) => (F u).val)
  have hval : Continuous (fun z : Reg015Setting.Target (L := L) (Set.range C.Φ) (A : ℝ) A.2 => z.val) :=
    continuous_subtype_val
  exact hval.comp F.continuous

private theorem forward_coords (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (A : ℝ≥0) (u : (fieldScale L).Y A) (n : ℤ) :
    (forward hR C A u).val n = C.Φ u.val n :=
  (Classical.choose_spec (regHomeo hR C (A : ℝ) A.2)) u n

private def data (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (a : ℝ≥0) (ha : ∀ r, SOf (order r) ≤ a) : SeqData (def002 L a) ι :=
  scaleData L (fun r => (SOf (order r) : ℝ)) a (fun r => NNReal.coe_le_coe.2 (ha r))
    (fun r => Fd hR C (order r)) (fun r => Fd_contDiff hR C (order r))
    (fun r => Fd_inv hR C (order r))

private theorem data_freq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (a : ℝ≥0) (ha : ∀ r, SOf (order r) ≤ a) (z : (seqScale L).Y a)
    (r : ι) (n : ℤ) :
    (data hR C order a ha).D.Ω r z n =
      FreqSeq (SOf (order r) : ℝ) (Fd hR C (order r)) z.val n :=
  (SeqData.D_Ω _ r z n).trans (FreqSeq_eq _ _ _ rfl n).symm

private theorem chart_restrict (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (a : ℝ≥0) (z : (seqScale L).Y a) :
    (fieldScale L).emb a 0 (nn_zero_le a) (gOf hR C a z) =
      PsiC C ((seqScale L).emb a 0 (nn_zero_le a) z) := by
  apply WField.ext
  show (gOf hR C a z).val = C.Ψ (Reg015Setting.toBase (L := L) 0 (NNReal.coe_nonneg 0)
    (h02_mono L (NNReal.coe_nonneg a) z))
  refine (gOf_val hR C a z).trans ?_
  exact congrArg C.Ψ (lp.ext (funext fun n =>
    (Reg015Setting.toBase_apply (L := L) _ a.2 z n).trans
      (Reg015Setting.toBase_apply (L := L) _ (NNReal.coe_nonneg 0)
        (h02_mono L (NNReal.coe_nonneg a) z) n).symm))

private theorem output_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) :
    ContDiff ℝ (m : ℕ∞) (fun z : (seqScale L).Y (chartLevel order m q) =>
      (fieldScale L).emb (chartLevel order m q) q
        (le_trans le_self_add (loss_levels order m q).1) (gOf hR C _ z)) := by
  let a := chartLevel order m q
  have h := (loss_h_to_H L (k := m + 1) (by omega) (q := q + 1) (S := a)
    (by positivity) (loss_levels order m q).2 (loss_levels order m q).1
    (PsiC C) (PsiC_analytic C) (gOf hR C a) (gOf_cont hR C a) (chart_restrict hR C a)).1
  have h' : ContDiff ℝ (m : ℕ∞) (fun z : (seqScale L).Y a =>
      (fieldScale L).emb a (q + 1) (loss_levels order m q).1 (gOf hR C a z)) :=
    h.of_le (by exact_mod_cast Nat.le_succ m)
  have heq : (fun z : (seqScale L).Y a =>
      (fieldScale L).emb a q (le_trans le_self_add (loss_levels order m q).1) (gOf hR C a z)) =
      fun z => (fieldScale L).emb (q + 1) q le_self_add
        ((fieldScale L).emb a (q + 1) (loss_levels order m q).1 (gOf hR C a z)) := by
    funext z
    exact ((fieldScale L).emb_comp a (q + 1) q (loss_levels order m q).1 le_self_add
      (gOf hR C a z)).symm
  change ContDiff ℝ (m : ℕ∞) (fun z : (seqScale L).Y a =>
    (fieldScale L).emb a q (le_trans le_self_add (loss_levels order m q).1) (gOf hR C a z))
  rw [heq]
  exact ((fieldScale L).emb (q + 1) q le_self_add).contDiff.comp h'

private def inputSeq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (u : (fieldScale L).Y (inputLevel order m q)) :
    (seqScale L).Y (chartLevel order m q) :=
  (seqScale L).emb _ _ (chart_input_le order m q) (forward hR C _ u)

private theorem inputSeq_coords (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (u : (fieldScale L).Y (inputLevel order m q))
    (n : ℤ) : (inputSeq hR C order m q u).val n = C.Φ u.val n :=
  forward_coords hR C _ u n

/-- The finite-input flow consists of the forward Sobolev chart, rotations, and the inverse
Sobolev chart with loss. The chart flow on smooth profiles agrees with this map. -/
def finiteFlow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (t : ι → ℝ) (u : (fieldScale L).Y (inputLevel order m q)) :
    (fieldScale L).Y q :=
  (fieldScale L).emb (chartLevel order m q) q (le_trans le_self_add (loss_levels order m q).1)
    (gOf hR C _ (flow (data hR C order _ (order_chart_le order m q)).D t (inputSeq hR C order m q u)))

theorem finiteFlow_continuous (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) :
    Continuous (fun p : (ι → ℝ) × (fieldScale L).Y (inputLevel order m q) =>
      finiteFlow hR C order m q p.1 p.2) := by
  let a := chartLevel order m q
  let A := inputLevel order m q
  let D : FreqData (def002 L (a : ℝ)) ι := (data hR C order a (order_chart_le order m q)).D
  let input : H02 L (A : ℝ) → h02 L (a : ℝ) := inputSeq hR C order m q
  let timeAndSeq : (ι → ℝ) × H02 L (A : ℝ) → (ι → ℝ) × h02 L (a : ℝ) :=
    fun p => (p.1, input p.2)
  let rotate : (ι → ℝ) × h02 L (a : ℝ) → h02 L (a : ℝ) :=
    fun p => flow D p.1 p.2
  let output : h02 L (a : ℝ) → H02 L (q : ℝ) :=
    fun z => (fieldScale L).emb a q (le_trans le_self_add (loss_levels order m q).1) (gOf hR C a z)
  have hin : Continuous input :=
    ((seqScale L).emb A a (chart_input_le order m q)).continuous.comp (forward_cont hR C A)
  have htime : Continuous timeAndSeq := continuous_fst.prodMk (hin.comp continuous_snd)
  have hrotate : Continuous rotate := continuous_flow D
  have hout : Continuous output := (output_contDiff hR C order m q).continuous
  change Continuous (output ∘ rotate ∘ timeAndSeq)
  exact hout.comp (hrotate.comp htime)

private theorem data_rotation_contDiff (a : ℝ≥0) (D : SeqData (def002 L a) ι)
    (z : h02 L a) (m : ℕ)
    (hmoment : ∀ j ≤ m, Summable fun n =>
      sobolevWeight L ((a : ℝ) + 2) n * D.P n ^ (2 * j) * ‖z.val n‖ ^ 2) :
    ContDiff ℝ (m : ℕ∞) (fun t => flow D.D t z) := by
  obtain ⟨K, hK, hΩ⟩ := D.freq_bound' z
  have hΩ' (n : ℤ) : (∑ r, |D.D.Ω r z n|) ≤ K * D.P n := by
    unfold SeqData.P
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => hΩ r n
  exact finite_rotation_smooth D.D z D.P D.P_nonneg hK hΩ' m hmoment

theorem finiteFlow_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (u : (fieldScale L).Y (inputLevel order m q)) :
    ContDiff ℝ (m : ℕ∞) (fun t => finiteFlow hR C order m q t u) := by
  let a := chartLevel order m q
  let D := data hR C order a (order_chart_le order m q)
  let z := inputSeq hR C order m q u
  have hmoment (j : ℕ) (hj : j ≤ m) :
      Summable fun n => sobolevWeight L ((a : ℝ) + 2) n * D.P n ^ (2 * j) * ‖z.val n‖ ^ 2 := by
    apply finite_moment (S := fun r => (SOf (order r) : ℝ)) (fun _ => NNReal.coe_nonneg _)
    have hB : (∑ r, (SOf (order r) : ℝ)) = (orderLevel order : ℝ) := by simp [orderLevel]
    have hle : (a : ℝ) + 2 + (2 * (j : ℝ)) * (∑ r, (SOf (order r) : ℝ)) ≤
        (inputLevel order m q : ℝ) := by
      rw [hB]
      push_cast [inputLevel, ← show a = chartLevel order m q from rfl]
      gcongr
    exact RB7H.memHs_of_le hle _ (forward hR C _ u).summable
  exact (output_contDiff hR C order m q).comp (data_rotation_contDiff a D z m hmoment)

/-- For smooth input, the frozen all-level moment lemma supplies the same bounds at
each selected finite level and for every independent time. -/
theorem finiteFlow_contDiff_of_rapid (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (u : (fieldScale L).Y (inputLevel order m q))
    (hu : Hinf L (fun n => C.Φ u.val n)) :
    ContDiff ℝ (m : ℕ∞) (fun t => finiteFlow hR C order m q t u) := by
  let a := chartLevel order m q
  let D := data hR C order a (order_chart_le order m q)
  let z := inputSeq hR C order m q u
  have h : Hinf L z.val := by
    rw [show z.val = (fun n => C.Φ u.val n) from funext (inputSeq_coords hR C order m q u)]
    exact hu
  exact (output_contDiff hR C order m q).comp (data_rotation_contDiff a D z m
    (fun j _ => hzP_of_Hinf L (fun r => (SOf (order r) : ℝ))
      (fun _ => NNReal.coe_nonneg _) ((a : ℝ) + 2) z.val h j))

/-- A single bound for all derivatives through order `m` of a `C^m` map on a compact set. -/
theorem compact_derivatives {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {f : E → F} (hf : ContDiff ℝ (m : ℕ∞) f) {T : Set E} (hT : IsCompact T) :
    ∃ B : ℝ, ∀ t ∈ T, ∀ j ≤ m, ‖iteratedFDeriv ℝ j f t‖ ≤ B := by
  have h (j : Fin (m + 1)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ T, ‖iteratedFDeriv ℝ (j : ℕ) f t‖ ≤ B := by
    have hj : (j : ℕ) ≤ m := Nat.le_of_lt_succ j.isLt
    obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast hj : ((j : ℕ) : ℕ∞ω) ≤ (m : ℕ∞))).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun t ht => (hB t ht).trans (le_max_left _ _)⟩
  choose B hB using h
  refine ⟨∑ j, B j, fun t ht j hj => ?_⟩
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  exact ((hB j').2 t ht).trans
    (Finset.single_le_sum (f := B) (fun i _ => (hB i).1) (Finset.mem_univ j'))

/-- For a fixed finite-level datum, a single constant bounds the value and time derivatives
through order `m` in `H^q` on every compact set of times. -/
theorem finiteFlow_time_bound (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (u : (fieldScale L).Y (inputLevel order m q))
    {T : Set (ι → ℝ)} (hT : IsCompact T) :
    ∃ B : ℝ, ∀ t ∈ T, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun s => finiteFlow hR C order m q s u) t‖ ≤ B :=
  compact_derivatives (finiteFlow_contDiff hR C order m q u) hT

/-- The finite-level extension has exactly the same rotation coordinates as the hierarchy. -/
theorem finiteFlow_coords (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (q : ℝ≥0) (t : ι → ℝ)
    (u : (fieldScale L).Y (inputLevel order m q)) (n : ℤ) :
    C.Φ (finiteFlow hR C order m q t u).val n =
      Complex.exp (((-(∑ r, t r * FreqSeq (SOf (order r) : ℝ) (Fd hR C (order r))
        (fun i => C.Φ u.val i) n) : ℝ) : ℂ) * Complex.I) * C.Φ u.val n := by
  let a := chartLevel order m q
  let D := data hR C order a (order_chart_le order m q)
  let z := inputSeq hR C order m q u
  have hfield : (finiteFlow hR C order m q t u).val = (gOf hR C a (flow D.D t z)).val :=
    RB7H.emb_val (L := L) (le_trans le_self_add (loss_levels order m q).1) (gOf hR C a (flow D.D t z))
  rw [hfield, gOf_val, C.ΦΨ]
  refine (Reg015Setting.toBase_apply (L := L) (a : ℝ) a.2 (flow D.D t z) n).trans ?_
  refine (flow_val D.D t z n).trans ?_
  have hval : z.val = (fun i => C.Φ u.val i) := funext (inputSeq_coords hR C order m q u)
  have hangle : angle D.D t z n =
      -(∑ r, t r * FreqSeq (SOf (order r) : ℝ) (Fd hR C (order r)) (fun i => C.Φ u.val i) n) := by
    unfold angle
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    apply congrArg (fun w : ℝ => t r * w)
    exact (data_freq hR C order a (order_chart_le order m q) z r n).trans
      (congrArg (fun w => FreqSeq (SOf (order r) : ℝ) (Fd hR C (order r)) w n) hval)
  rw [hangle, congrFun hval n]

/-- All choices of finite levels give the same evolution as an `L²` class on their common domain. -/
theorem finiteFlow_compatible (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) {m m' : ℕ} {q q' : ℝ≥0} (t : ι → ℝ)
    {u : (fieldScale L).Y (inputLevel order m q)}
    {u' : (fieldScale L).Y (inputLevel order m' q')} (hu : u.val = u'.val) :
    (finiteFlow hR C order m q t u).val = (finiteFlow hR C order m' q' t u').val := by
  apply (Function.LeftInverse.injective C.ΨΦ)
  apply lp.ext
  funext n
  change C.Φ (finiteFlow hR C order m q t u).val n =
    C.Φ (finiteFlow hR C order m' q' t u').val n
  rw [finiteFlow_coords, finiteFlow_coords, hu]

end QuantumNLS.Def024LossR32m

#print axioms QuantumNLS.Def024LossR32m.finiteFlow_continuous
#print axioms QuantumNLS.Def024LossR32m.finiteFlow_contDiff
#print axioms QuantumNLS.Def024LossR32m.finiteFlow_time_bound
#print axioms QuantumNLS.Def024LossR32m.finiteFlow_coords
#print axioms QuantumNLS.Def024LossR32m.finiteFlow_compatible
