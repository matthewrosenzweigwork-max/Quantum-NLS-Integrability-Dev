import QuantumNLS.AuditWeightedSeriesR49a
import QuantumNLS.RootOccupationDet

/-! R-115CAA16: deterministic occupation upgrade. Accepted unweighted
occupation identification is reused as a theorem; no regular-cut contract
is introduced or used by this argument. A bounded higher empirical root
moment is an explicit analytical hypothesis, NOT an asserted Born estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace QuantumNLS.AuditWeightedDetR49a
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak
open QuantumNLS.RootOccupationDet QuantumNLS.AuditWeightedSeriesR49a
open QuantumNLS.PhysicalTensor
variable {L κ : ℝ} [Fact (0 < L)]

def rootWeight (p t : ℝ) : ℝ := (1+t^2)^(p/2)

def labelConstant (L κ : ℝ) : ℝ :=
  2 * (1 + ((L/(2*Real.pi))*(1+3*Real.sqrt (κ/L)))^2)

omit [Fact (0 < L)] in
theorem labelConstant_pos : 0 < labelConstant L κ := by
  unfold labelConstant
  positivity

theorem label_weight_le (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (B : OnShellBethe L κ N) (p : ℝ) (hp : 0 ≤ p) (j : Fin N) :
    weight p (B.n j) ≤ (labelConstant L κ)^(p/2) * rootWeight p (B.q j) := by
  have hL : 0 < L := Fact.out
  let a := L/(2*Real.pi)
  let d := 3*Real.sqrt (κ/L)
  let c := a*(1+d)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hc : 0 ≤ c := mul_nonneg ha (by linarith)
  have hlabel := QuantumNLS.LabelTightness.label_abs_le_bound hL hκ (by omega) B j
  change |(B.n j : ℝ)| ≤ a*(|B.q j|+d) at hlabel
  have hlin : |(B.n j : ℝ)| ≤ c*(1+|B.q j|) := by
    have : 0 ≤ a*d*|B.q j| := by positivity
    dsimp [c]
    nlinarith
  have hsq : (B.n j : ℝ)^2 ≤ c^2 * (1+|B.q j|)^2 := by
    have := mul_self_le_mul_self (abs_nonneg (B.n j : ℝ)) hlin
    simpa only [sq_abs, ← sq, mul_pow] using this
  have hq : (1+|B.q j|)^2 ≤ 2*(1+(B.q j)^2) := by
    nlinarith [sq_nonneg (|B.q j|-1), sq_abs (B.q j)]
  have hbase : 1+(B.n j : ℝ)^2 ≤ labelConstant L κ*(1+(B.q j)^2) := by
    have h := mul_le_mul_of_nonneg_left hq (sq_nonneg c)
    change 1+(B.n j : ℝ)^2 ≤ 2*(1+c^2)*(1+(B.q j)^2)
    nlinarith [sq_nonneg (B.q j)]
  unfold weight rootWeight
  calc
    (1+(B.n j : ℝ)^2)^(p/2) ≤
        (labelConstant L κ*(1+(B.q j)^2))^(p/2) :=
      Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = _ := Real.mul_rpow labelConstant_pos.le (by positivity)

omit [Fact (0 < L)] in
theorem weighted_occ_le_average {N : ℕ} (B : OnShellBethe L κ N)
    (F : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) (n : ℤ) :
    F n * occ B n ≤ (N : ℝ)⁻¹ * ∑ j, F (B.n j) := by
  classical
  have he : (∑ j ∈ Finset.univ.filter (fun j => B.n j=n), F (B.n j)) =
      ((Finset.univ.filter (fun j => B.n j=n)).card : ℝ) * F n := by
    calc
      _ = ∑ _j ∈ Finset.univ.filter (fun j => B.n j=n), F n := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2]
      _ = _ := by simp
  unfold occ
  calc
    F n * ((N : ℝ)⁻¹ * _) = (N : ℝ)⁻¹ *
        (∑ j ∈ Finset.univ.filter (fun j => B.n j=n), F (B.n j)) := by rw [he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => hF (B.n j)))
      (by positivity)

/-- Fixed-order label moments are controlled by the corresponding root
moment, with a constant independent of the particle number. -/
theorem weighted_occ_le_root_moment (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (B : OnShellBethe L κ N) (p : ℝ) (hp : 0 ≤ p) (n : ℤ) :
    weight p n * occ B n ≤ (labelConstant L κ)^(p/2) *
      ((N : ℝ)⁻¹ * ∑ j, rootWeight p (B.q j)) := by
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ j, weight p (B.n j) :=
      weighted_occ_le_average B (weight p) (fun n => (weight_pos p n).le) n
    _ ≤ (N : ℝ)⁻¹ * ∑ j, (labelConstant L κ)^(p/2) * rootWeight p (B.q j) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ => label_weight_le hκ hN B p hp j) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Deterministic weighted conclusion for every fixed real `p ≥ 0`.
Weak root convergence and a bounded root moment of order `p+2` suffice.
The probability and common-packet claims are separate obligations. -/
theorem deterministic_weighted (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖=1)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ)=QuantumNLS.PhysicalQuantumMeasure.measure hκ u)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k))
    (hweak : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) (p : ℝ) (hp : 0 ≤ p) (M : ℝ)
    (hM : ∀ k, ((N k : ℝ)⁻¹ * ∑ j, rootWeight (p+2) ((B k).q j)) ≤ M) :
    Tendsto (fun k => ∑' n, weight p n *
      |occ (B k) n-(QuantumNLS.RootIndexedMasses.masses hκ u).1 n|) atTop (𝓝 0) := by
  have hm := QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  have hl1 := occ_tendsto_seq hκ u hu hμ B hweak hNtop
  apply weighted_l1_of_pointwise (fun k => occ (B k))
    (QuantumNLS.RootIndexedMasses.masses hκ u).1 p ((labelConstant L κ)^((p+2)/2)*M)
    (fun k n => occ_nonneg (B k) n) hm.2.1 ?_ ?_
  · intro k n
    exact (weighted_occ_le_root_moment hκ (hN k) (B k) (p+2) (by linarith) n).trans
      (mul_le_mul_of_nonneg_left (hM k) (Real.rpow_nonneg labelConstant_pos.le _))
  · intro n
    have hs (k : ℕ) : Summable (fun j =>
        |occ (B k) j-(QuantumNLS.RootIndexedMasses.masses hκ u).1 j|) :=
      ((hasSum_occ (hN k) (B k)).summable.sub hm.2.2.1).abs
    have ht : Tendsto (fun k => |occ (B k) n-(QuantumNLS.RootIndexedMasses.masses hκ u).1 n|)
        atTop (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) (fun k =>
        (hs k).le_tsum n (fun _ _ => abs_nonneg _)) hl1
    exact (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa only [Real.norm_eq_abs] using ht)

/-- Uniform deterministic form at a fixed higher root-moment bound. The
neighbourhood is in weak probability-measure topology, with no Wasserstein
metric or unbounded expectation assumed. -/
theorem deterministic_weighted_uniform (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖=1)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ)=QuantumNLS.PhysicalQuantumMeasure.measure hκ u)
    (p : ℝ) (hp : 0 ≤ p) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
      ((N : ℝ)⁻¹ * ∑ j, rootWeight (p+2) (B.q j)) ≤ M →
      (∑' n, weight p n * |occ B n-(QuantumNLS.RootIndexedMasses.masses hκ u).1 n|) < ε := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨V, hV⟩ := (𝓝 μ).exists_antitone_basis
  have hpick : ∀ k : ℕ, ∃ N : ℕ, ∃ hN : 0 < N, k+1 ≤ N ∧
      ∃ B : OnShellBethe L κ N, rootP B hN ∈ V k ∧
        ((N : ℝ)⁻¹ * ∑ j, rootWeight (p+2) (B.q j)) ≤ M ∧
        ε ≤ ∑' n, weight p n * |occ B n-(QuantumNLS.RootIndexedMasses.masses hκ u).1 n| := by
    intro k
    exact hcon (V k) (hV.1.mem_of_mem trivial) (k+1)
  choose Nk hNk hkN Bk hBk hMk hle using hpick
  have hweak : Tendsto (fun k => rootP (Bk k) (hNk k)) atTop (𝓝 μ) := hV.tendsto hBk
  have hNtop : Tendsto Nk atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hkN k)) tendsto_id
  have ht := deterministic_weighted hκ u hu hμ hNk Bk hweak hNtop p hp M hMk
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact absurd (hle k) (not_le.2 hk)

end QuantumNLS.AuditWeightedDetR49a

#print axioms QuantumNLS.AuditWeightedDetR49a.rootWeight

#print axioms QuantumNLS.AuditWeightedDetR49a.labelConstant

#print axioms QuantumNLS.AuditWeightedDetR49a.labelConstant_pos

#print axioms QuantumNLS.AuditWeightedDetR49a.label_weight_le

#print axioms QuantumNLS.AuditWeightedDetR49a.weighted_occ_le_average

#print axioms QuantumNLS.AuditWeightedDetR49a.weighted_occ_le_root_moment

#print axioms QuantumNLS.AuditWeightedDetR49a.deterministic_weighted

#print axioms QuantumNLS.AuditWeightedDetR49a.deterministic_weighted_uniform

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedDetR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedDetR49a." then
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
  Lean.logInfo m!"Round49 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
