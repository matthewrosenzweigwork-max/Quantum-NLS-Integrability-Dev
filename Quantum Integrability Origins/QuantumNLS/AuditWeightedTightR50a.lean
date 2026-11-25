import QuantumNLS.AuditWeightedShellMeanR50a

/-! Slow moving integer cutoffs with a vanishing explicit shell bias. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.AuditWeightedCutoffR50a

def alpha (b : ℕ) : ℝ := 1/(2*((2*b+1 : ℕ) : ℝ))
def cutoff (b N : ℕ) : ℕ := ⌊(N : ℝ)^(alpha b)⌋₊

theorem alpha_pos (b : ℕ) : 0 < alpha b := by unfold alpha; positivity

theorem alpha_maximum (b : ℕ) : 1 < 2*((2*b+2 : ℕ) : ℝ)*alpha b := by
  unfold alpha
  have hd : 0 < (2 : ℝ)*((2*b+1 : ℕ) : ℝ) := by positivity
  rw [mul_one_div, lt_div_iff₀ hd]
  push_cast
  linarith

theorem cutoff_covers (b N : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (N : ℝ)^alpha b ≤ R+cutoff b N := by
  have h := Nat.lt_floor_add_one ((N : ℝ)^alpha b)
  change (N : ℝ)^alpha b ≤ R+(⌊(N : ℝ)^alpha b⌋₊ : ℝ)
  linarith

/-- This controls the finite shell bias even with the extra shell-count
factor. It is independent of the probability space. -/
theorem cutoff_bias_zero (b : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (fun N : ℕ => (R+cutoff b N+1)^(2*b+1)/(N : ℝ)) atTop (𝓝 0) := by
  have hR0 : 0 < R := by linarith
  let d : ℕ := 2*b+1
  have hd : (0 : ℝ) < d := by dsimp [d]; positivity
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hg := (tendsto_rpow_atTop (alpha_pos b)).comp hn
  have hlarge := hg.eventually (eventually_ge_atTop (max 1 (R+1)))
  have hbound : ∀ᶠ N : ℕ in atTop,
      0 ≤ (R+cutoff b N+1)^d/(N : ℝ) ∧
      (R+cutoff b N+1)^d/(N : ℝ) ≤ (2 : ℝ)^d*(N : ℝ)^(-(1/2 : ℝ)) := by
    filter_upwards [hlarge,eventually_ge_atTop 1] with N hN hN1
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN1
    have hx : 0 ≤ (N : ℝ)^alpha b := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hfloor : (cutoff b N : ℝ) ≤ (N : ℝ)^alpha b := Nat.floor_le hx
    have hbas : 0 ≤ R+cutoff b N+1 := by positivity
    constructor
    · exact div_nonneg (pow_nonneg hbas _) hNr.le
    · have hle : R+cutoff b N+1 ≤ 2*(N : ℝ)^alpha b := by
        have hh := (le_max_right _ _).trans hN
        change R+1 ≤ (N : ℝ)^alpha b at hh
        linarith
      have hpow := div_le_div_of_nonneg_right (pow_le_pow_left₀ hbas hle d) hNr.le
      apply hpow.trans_eq
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ)^alpha b) d, ← Real.rpow_mul hNr.le]
      have hexp : alpha b*(d : ℝ) = 1/2 := by
        change (1/(2*(d : ℝ)))*(d : ℝ)=1/2
        field_simp [ne_of_gt hd]
      rw [hexp, div_eq_mul_inv, mul_assoc, ← Real.rpow_neg_one,
        ← Real.rpow_add hNr]
      norm_num
  have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp hn).const_mul ((2 : ℝ)^d)
  rw [mul_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)

end QuantumNLS.AuditWeightedCutoffR50a


/-! Actual Born-law tightness of every fixed root moment. The integrable
quantity in the Markov step is the bounded shell majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedTightR50a
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.RootEvent QuantumNLS.Prop017Quantum
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.AuditWeightedTailR49a QuantumNLS.AuditWeightedShellR50a
open QuantumNLS.AuditWeightedShellMeanR50a QuantumNLS.AuditWeightedCutoffR50a
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedDetR49a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- Stronger moments are bounded in probability under the full Born law. -/
theorem even_root_moment_tight (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (b : ℕ) :
    RootMomentTight hκ (smoothL2 hf) hu (2*(b : ℝ)) := by
  obtain ⟨C,D,hC,hD,htail⟩ := smooth_born_tail hκ hf hu (2*b+2)
  let R := max 1 (eta0 L κ)
  have hR : 1 ≤ R := le_max_left _ _
  have hRη : eta0 L κ ≤ R := le_max_right _ _
  let H := (1+R^2)^b + 5^b*C*(∑' i, invSquare i)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (by positivity) (mul_nonneg (by positivity)
      (tsum_nonneg fun _ => by unfold invSquare; positivity))
  have hmean : ∀ N : ℕ, 0 < N →
      (∫ m, shellMajorant (qAct L κ N) b (cutoff b N) R m
        ∂bornMeasure (physBasis L hκ N) (smoothL2 hf) hu) ≤
      H+(5^b*D)*((R+cutoff b N+1)^(2*b+1)/(N : ℝ)) := by
    intro N hN
    apply mean_shell_bound hN _ _ Measurable.of_discrete b (cutoff b N) hR hC hD
    intro i
    exact htail N hN (R+i) (hRη.trans (by linarith [show (0 : ℝ) ≤ (i : ℝ) by positivity]))
  have hbias := (cutoff_bias_zero b hR).const_mul ((5 : ℝ)^b*D)
  rw [mul_zero] at hbias
  have hmax := maximum_power_cutoff hκ hf hu (2*b+2) (alpha b)
    (alpha_pos b) (alpha_maximum b)
  intro δ hδ
  let M := 2*(H+1)/δ+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMδ : H+1 ≤ M*(δ/2) := by
    dsimp [M]
    field_simp
    nlinarith
  refine ⟨M, ?_⟩
  filter_upwards [hbias.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hmax.eventually (gt_mem_nhds (half_pos hδ)),eventually_ge_atTop 1] with N hb hm hN1
  have hN : 0 < N := by omega
  let P := bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
  let Y := shellMajorant (qAct L κ N) b (cutoff b N) R
  have hYi : Integrable Y P := integrable_shellMajorant _ _ Measurable.of_discrete _ _ _
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (shellMajorant_nonneg _ _ _ _)) hYi M
  have he : (∫ m, Y m ∂P) ≤ H+1 := (hmean N hN).trans (by linarith)
  have hp : P.real {m | M ≤ Y m} ≤ δ/2 := by
    have := hmark.trans (he.trans hMδ)
    exact (mul_le_mul_iff_right₀ hM).mp this
  have hsub : {m | M < rootMoment (L := L) (κ := κ) (2*(b : ℝ)) N m} ⊆
      outside (qAct L κ N) ((N : ℝ)^alpha b) ∪ {m | M ≤ Y m} := by
    intro m hx
    by_cases hm : m ∈ outside (qAct L κ N) ((N : ℝ)^alpha b)
    · exact Or.inl hm
    · right
      have hq : ∀ j, |qAct L κ N m j| ≤ R+cutoff b N := by
        intro j
        have : |qAct L κ N m j| ≤ (N : ℝ)^alpha b := by
          exact le_of_not_gt (fun h => hm ⟨j,h⟩)
        exact this.trans (cutoff_covers b N hR)
      have hs := average_shell_bound hN (qAct L κ N) b (cutoff b N) hR m hq
      have hr : rootMoment (L := L) (κ := κ) (2*(b : ℝ)) N m ≤ Y m := by
        simpa only [rootMoment,rootWeight,show 2*(b : ℝ)/2=(b : ℝ) by ring,
          Real.rpow_natCast,qAct,Y] using hs
      exact hx.le.trans hr
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by
    change P.real (outside (qAct L κ N) ((N : ℝ)^alpha b)) < δ/2 at hm
    linarith))

/-- All real orders are covered by one higher even integer order. -/
theorem root_moment_tight (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (p : ℝ) :
    RootMomentTight hκ (smoothL2 hf) hu p := by
  obtain ⟨b,hb⟩ := exists_nat_ge (p/2)
  intro δ hδ
  obtain ⟨M,hM⟩ := even_root_moment_tight hκ hf hu b δ hδ
  refine ⟨M,hM.mono fun N hN => ?_⟩
  apply (measureReal_mono (fun m hm => ?_)).trans hN
  simp only [Set.mem_ofPred_eq] at hm ⊢
  apply hm.trans_le
  unfold rootMoment
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  unfold rootWeight
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (arrRoots L (κ/N) m j)])
    (by linarith)

/-- Exact weighted occupation convergence under the actual Born laws,
with the root-tightness hypothesis discharged. -/
theorem weighted_probability (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (p : ℝ) (hp : 0 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
      {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0) :=
  weighted_probability_of_root_moment_tight hκ (smoothL2 hf) hu p hp
    (root_moment_tight hκ hf hu (p+2)) ε hε

end QuantumNLS.AuditWeightedTightR50a

#print axioms QuantumNLS.AuditWeightedTightR50a.even_root_moment_tight
#print axioms QuantumNLS.AuditWeightedTightR50a.root_moment_tight
#print axioms QuantumNLS.AuditWeightedTightR50a.weighted_probability

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedCutoffR50a." ||
        n.toString.startsWith "QuantumNLS.AuditWeightedTightR50a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedTightR50a." then
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
