import QuantumNLS.TerraMultiRound18Flow

/-! Finite composition of short-time analytic solution maps. The named
hypothesis is the GP-04 analytic initial-dependence remainder on compact sets;
it does not assert analyticity at arbitrary times. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
open QuantumNLS.D01LocalPrimitive QuantumNLS.TerraMultiRound18Flow
namespace QuantumNLS.TerraMultiRound18AnalyticFlow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The short-time compact-uniform initial-dependence statement held by GP-04. -/
def GP04CompactLocalAnalyticity (S : Hyp H) : Prop :=
  ∀ K : Set H, IsCompact K → ∃ δ > (0 : ℝ),
    ∀ x ∈ K, ∀ t : ℝ, |t| < δ → AnalyticAt ℝ (flow S t) x

/-- Composing finitely many analytic short-time solution maps. -/
theorem analytic_finite_steps (S : Hyp H) (u : H) (d : ℝ) (n : ℕ)
    (hstep : ∀ k < n, AnalyticAt ℝ (flow S d) (flow S ((k : ℝ) * d) u)) :
    AnalyticAt ℝ (flow S ((n : ℝ) * d)) u := by
  induction n with
  | zero =>
      have h0 : flow S 0 = id := funext fun x => (flow_spec S x).1
      simpa only [Nat.cast_zero, zero_mul, h0] using (analyticAt_id : AnalyticAt ℝ (id : H → H) u)
  | succ n ih =>
      have hi := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      have hh := (hstep n (Nat.lt_succ_self n)).comp hi
      convert hh using 1
      funext x
      rw [Nat.cast_succ, add_mul, one_mul, add_comm, flow_add]
      rfl

/-- The compact-uniform local GP-04 remainder implies analytic dependence for
all finite real times by composition along the compact trajectory. -/
theorem analytic_initial_dependence (S : Hyp H) (hlocal : GP04CompactLocalAnalyticity S)
    (t : ℝ) (u : H) : AnalyticAt ℝ (flow S t) u := by
  let K : Set H := (fun s : ℝ => flow S s u) '' Icc (-|t|) |t|
  have hc : Continuous (fun s => flow S s u) :=
    continuous_iff_continuousAt.mpr (fun s => ((flow_spec S u).2 s).continuousAt)
  have hK : IsCompact K := isCompact_Icc.image hc
  obtain ⟨δ, hδ, hlocalK⟩ := hlocal K hK
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / δ)
  let N : ℕ := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hlarge : |t| / δ < (N : ℝ) := by dsimp [N]; push_cast; linarith
  let d : ℝ := t / N
  have hd : |d| < δ := by
    dsimp [d]
    rw [abs_div, abs_of_pos hN, div_lt_iff₀ hN]
    have hh := (div_lt_iff₀ hδ).mp hlarge
    nlinarith
  have hmem (k : ℕ) (hk : k < N) : flow S ((k : ℝ) * d) u ∈ K := by
    refine ⟨(k : ℝ) * d, ?_, rfl⟩
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    have hratio : (0 : ℝ) ≤ (k : ℝ) / N ∧ (k : ℝ) / N ≤ 1 :=
      ⟨div_nonneg hk0 hN.le, (div_le_one hN).mpr hkN⟩
    have he : (k : ℝ) * d = ((k : ℝ) / N) * t := by dsimp [d]; ring
    rw [he]
    have hupper := mul_nonneg hratio.1 (sub_nonneg.mpr (le_abs_self t))
    have hlower : 0 ≤ ((k : ℝ) / N) * (|t| + t) :=
      mul_nonneg hratio.1 (by linarith [neg_abs_le t])
    have hrest := mul_nonneg (sub_nonneg.mpr hratio.2) (abs_nonneg t)
    constructor <;> nlinarith
  have hsteps := analytic_finite_steps S u d N (fun k hk => hlocalK _ (hmem k hk) d hd)
  have htotal : (N : ℝ) * d = t := by dsimp [d]; field_simp
  simpa only [htotal] using hsteps

#print axioms analytic_finite_steps
#print axioms analytic_initial_dependence
end QuantumNLS.TerraMultiRound18AnalyticFlow
