import QuantumNLS.AuditWeightedValuesR50a
import QuantumNLS.AuditWeightedPacketR49a
import QuantumNLS.AuditWeightedDiagonalR49a
import QuantumNLS.Ext025B6GraphCore

/-! Finite physical spectral projections of high-probability good events.
No product vector is put in an unbounded charge domain. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.AuditWeightedFiniteR50a
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.BetheCoefficientTransform QuantumNLS.EmpiricalRapidity
open QuantumNLS.CommonBethePacket QuantumNLS.AuditWeightedPacketR49a
open QuantumNLS.BoundedBetheTransfer QuantumNLS.Ext025B6GraphCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exact Born probability of the omitted spectral coordinates. -/
theorem projection_error_born (b : BetheBasis L N) (u : L2T L) (hu : ‖u‖=1)
    (E : Set (MArr N)) :
    ‖productVec L N u-projection b E (productVec L N u)‖^2 =
      (bornMeasure b u hu).real Eᶜ := by
  classical
  rw [vector_error]
  let w := fun m => if m ∈ E then (0 : ℝ) else bornLaw b u m
  have hw : ∀ m, 0 ≤ w m := fun m => by
    dsimp [w]
    split
    · exact le_rfl
    · exact bornLaw_nonneg b u m
  have hs : Summable w := Summable.of_nonneg_of_le hw
    (fun m => by
      dsimp [w]
      split
      · exact bornLaw_nonneg b u m
      · exact le_rfl) (summable_bornLaw b u)
  have he : bornMeasure b u hu Eᶜ = ENNReal.ofReal (∑' m, w m) := by
    unfold bornMeasure
    rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete,
      ENNReal.ofReal_tsum_of_nonneg hw hs]
    apply tsum_congr
    intro m
    simp only [Set.indicator_apply,Set.mem_compl_iff,bornPMF_apply,w]
    split <;> simp_all
  rw [measureReal_def,he,ENNReal.toReal_ofReal (tsum_nonneg hw)]
  apply tsum_congr
  intro m
  simp only [w,bornLaw,HilbertBasis.repr_apply_apply]

def truncCoefficients (b : BetheBasis L N) (F : Finset (MArr N)) (v : HN L N) : MArr N →₀ ℂ :=
  Finsupp.onFinset F (fun m => if m ∈ F then b.repr v m else 0)
    (fun m hm => by by_contra h; simp [h] at hm)

theorem truncCoefficients_apply (b : BetheBasis L N) (F : Finset (MArr N))
    (v : HN L N) (m : MArr N) :
    truncCoefficients b F v m = if m ∈ F then b.repr v m else 0 := rfl

theorem synthesis_truncCoefficients (b : BetheBasis L N) (F : Finset (MArr N)) (v : HN L N) :
    synthesis b (truncCoefficients b F v) = ∑ m ∈ F, b.repr v m • b m := by
  classical
  have hsupp : (truncCoefficients b F v).support ⊆ F := Finsupp.support_onFinset_subset
  change (truncCoefficients b F v).sum (fun m c => c • b m) = _
  rw [Finsupp.sum_of_support_subset _ hsupp _ (by simp)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [truncCoefficients_apply,ite_eq_left hm]

/-- Finite approximants to the good-event projection retain that event
exactly. The norm approximation is arbitrary and quantitative. -/
theorem finite_good_approximation (b : BetheBasis L N) (ψ : HN L N)
    (E : Set (MArr N)) (η : ℝ) (hη : 0 < η) :
    ∃ a : MArr N →₀ ℂ, (∀ m ∈ a.support, m ∈ E) ∧
      ‖synthesis b a-projection b E ψ‖ < η := by
  classical
  let v := projection b E ψ
  have ht := b.hasSum_repr v
  obtain ⟨F,hF⟩ := (ht.eventually (Metric.ball_mem_nhds _ hη)).exists
  refine ⟨truncCoefficients b F v, ?_, ?_⟩
  · intro m hm
    by_contra h
    have hz : truncCoefficients b F v m=0 := by
      rw [truncCoefficients_apply]
      dsimp [v]
      rw [projection_coord b E ψ m]
      split <;> simp_all
    exact Finsupp.mem_support_iff.mp hm hz
  · rw [synthesis_truncCoefficients]
    simpa only [Metric.mem_ball,dist_eq_norm,v] using hF

end QuantumNLS.AuditWeightedFiniteR50a


/-! Countable physical deviation constraints, selected before any fixed
charge or weight order. The general event lemma is independent of vectors. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedSelectionR50a
open QuantumNLS.AuditWeightedDiagonalR49a

/-- One good-event sequence captures every fixed member of a countable
family, uniformly on that sequence, and has complement probability → 0. -/
theorem common_good_events {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (X : ℕ → (N : ℕ) → Ω N → ℝ)
    (hX : ∀ k ε, 0 < ε → Tendsto (fun N => P N {ω | ε < X k N ω}) atTop (𝓝 0)) :
    ∃ E : (N : ℕ) → Set (Ω N),
      Tendsto (fun N => P N (E N)ᶜ) atTop (𝓝 0) ∧
      ∀ k ε, 0 < ε → ∀ᶠ N in atTop, ∀ ω ∈ E N, X k N ω ≤ ε := by
  classical
  let good := fun k N => {ω : Ω N | ∀ j ≤ k, X j N ω ≤ 1/((k : ℝ)+1)}
  have hcomp (k N : ℕ) : (good k N)ᶜ ⊆
      ⋃ j ∈ Finset.range (k+1), {ω : Ω N | 1/((k : ℝ)+1) < X j N ω} := by
    intro ω hω
    simp only [good,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,not_le] at hω
    obtain ⟨j,hj,hbad⟩ := hω
    simp only [Set.mem_iUnion,Finset.mem_range]
    exact ⟨j,by omega,hbad⟩
  have hgood (k : ℕ) : Tendsto (fun N => P N (good k N)ᶜ) atTop (𝓝 0) := by
    have ht : Tendsto (fun N => ∑ j ∈ Finset.range (k+1),
        P N {ω | 1/((k : ℝ)+1) < X j N ω}) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.range (k+1))
        (fun j _ => hX j (1/((k : ℝ)+1)) (by positivity))
      simpa only [Finset.sum_const_zero] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro N
    exact (measure_mono (hcomp k N)).trans (measure_biUnion_finset_le _ _)
  have hQ (k : ℕ) : ∀ᶠ N in atTop,
      P N (good k N)ᶜ ≤ ENNReal.ofReal (1/((k : ℝ)+1)) :=
    (hgood k).eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  obtain ⟨level,hl,hlevel⟩ := slow_diagonal _ hQ
  refine ⟨fun N => good (level N) N, ?_, ?_⟩
  · have ht : Tendsto (fun N => ENNReal.ofReal (1/((level N : ℝ)+1))) atTop (𝓝 0) := by
      have hh : Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0) := by
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp (hh.comp hl)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => bot_le) hlevel
  · intro k ε hε
    have hh : Tendsto (fun N => 1/((level N : ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hl
    filter_upwards [hl.eventually (eventually_ge_atTop k),
      hh.eventually (gt_mem_nhds hε)] with N hk he
    intro ω hω
    exact (hω k hk).trans he.le

end QuantumNLS.AuditWeightedSelectionR50a


/-! One finite normalized packet sequence from one physical good-event
sequence. Every fixed support requirement is inherited after selection. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.AuditWeightedCommonPacketR50a
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.BetheCoefficientTransform QuantumNLS.EmpiricalRapidity
open QuantumNLS.CommonBethePacket QuantumNLS.AuditWeightedPacketR49a
open QuantumNLS.BoundedBetheTransfer QuantumNLS.AuditWeightedFiniteR50a
variable {L : ℝ} [Fact (0 < L)]

def defaultArray (N : ℕ) : MArr N := ⟨Finsupp.single 0 N,by simp⟩

def defaultPacket {N : ℕ} (b : BetheBasis L N) : Packet b where
  coefficients := Finsupp.single (defaultArray N) 1
  normalized := by
    change ‖(Finsupp.single (defaultArray N) (1 : ℂ)).sum (fun m c => c • b m)‖=1
    rw [Finsupp.sum_single_index (by simp),one_smul]
    exact b.orthonormal.norm_eq_one _

/-- Finite normalized packets approximate the product vector and remain
inside the same good event eventually. Domain membership holds at ALL N. -/
theorem packets_from_events (b : (N : ℕ) → BetheBasis L N)
    (u : L2T L) (hu : ‖u‖=1) (E : (N : ℕ) → Set (MArr N))
    (hE : Tendsto (fun N => bornMeasure (b N) u hu (E N)ᶜ) atTop (𝓝 0)) :
    ∃ P : (N : ℕ) → Packet (b N),
      Tendsto (fun N => ‖vector (P N)-productVec L N u‖) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, ∀ m ∈ support (P N), m ∈ E N) ∧
      ∀ N (ev : MArr N → ℝ), vector (P N) ∈
        (QuantumNLS.BetheSpectralCharges.multiplier (b N) ev).domain := by
  classical
  have hη (N : ℕ) : 0 < 1/((N : ℝ)+1) := by positivity
  choose a ha hclose using (fun N => finite_good_approximation (b N) (productVec L N u)
    (E N) (1/((N : ℝ)+1)) (hη N))
  let v := fun N => synthesis (b N) (a N)
  have hproj : Tendsto (fun N => ‖productVec L N u-
      projection (b N) (E N) (productVec L N u)‖) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    simp only [ENNReal.toReal_zero] at ht
    have he (N : ℕ) : ‖productVec L N u-projection (b N) (E N) (productVec L N u)‖ =
        Real.sqrt ((bornMeasure (b N) u hu).real (E N)ᶜ) := by
      rw [← projection_error_born]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    simp_rw [he]
    simpa only [Function.comp_def,measureReal_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp ht
  have happrox : Tendsto (fun N => ‖v N-productVec L N u‖) atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.add hproj
    simp only [zero_add] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => norm_nonneg _)
    intro N
    have ht := norm_sub_le_norm_sub_add_norm_sub (v N) (projection (b N) (E N) (productVec L N u)) (productVec L N u)
    rw [norm_sub_rev (projection (b N) (E N) (productVec L N u))] at ht
    exact ht.trans (add_le_add (hclose N).le le_rfl)
  have hunit (N : ℕ) : ‖productVec L N u‖=1 := by
    rw [norm_productVec,hu,one_pow]
  let P := fun N => if h : ‖v N-productVec L N u‖<1 then
    normalize (b N) (a N) (Classical.choose (normalize_approximation (b N) (a N) _ (hunit N) h))
    else defaultPacket (b N)
  have hevent := happrox.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  have herr : ∀ᶠ N in atTop, ‖vector (P N)-productVec L N u‖ ≤ 2*‖v N-productVec L N u‖ := by
    filter_upwards [hevent] with N hN
    dsimp only [P]
    rw [dite_eq_left hN]
    exact Classical.choose_spec (normalize_approximation (b N) (a N) _ (hunit N) hN)
  refine ⟨P,?_,?_,fun N ev => packet_mem_every_domain (b N) (P N) ev⟩
  · have ht := happrox.const_mul 2
    rw [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => norm_nonneg _) herr
  · filter_upwards [hevent] with N hN
    intro m hm
    dsimp only [P] at hm
    rw [dite_eq_left hN] at hm
    exact ha N m (support_normalize_subset _ _ _ hm)

end QuantumNLS.AuditWeightedCommonPacketR50a

#print axioms QuantumNLS.AuditWeightedFiniteR50a.projection_error_born
#print axioms QuantumNLS.AuditWeightedSelectionR50a.common_good_events
#print axioms QuantumNLS.AuditWeightedCommonPacketR50a.packets_from_events

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedFiniteR50a." ||
        n.toString.startsWith "QuantumNLS.AuditWeightedSelectionR50a." ||
        n.toString.startsWith "QuantumNLS.AuditWeightedCommonPacketR50a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedCommonPacketR50a." then
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
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round50 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
