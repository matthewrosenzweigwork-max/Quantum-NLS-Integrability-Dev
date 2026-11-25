import QuantumNLS.REF88STruncation
import QuantumNLS.REF88StageC

/-! R-EF8C2837 item (iv), physical_cubic.tex:331–337.
Finite action truncations converge in the ℓ¹ norm. On the active-coordinate domain,
every continuous frequency has the unique limit stated by the printed rough boundary.
No moment or energy hypothesis occurs. Author sol_multi round23; reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
namespace QuantumNLS.REF88SRoughLimit
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.REF88STruncation (supports supports_tendsto pair_mem)

/-- The finite action vector, retaining a specified pair of indices. -/
def actions (a : PosL1) (n m : ℤ) (j : ℕ) : PosL1 :=
  ⟨∑ k ∈ supports n m j, lp.single 1 k (a.1 k), by
    intro k
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_single, Finset.sum_pi_single]
    split_ifs <;> simp_all [a.2 k]⟩

@[simp] theorem actions_apply (a : PosL1) (n m : ℤ) (j : ℕ) (k : ℤ) :
    (actions a n m j).1 k = if k ∈ supports n m j then a.1 k else 0 := by
  change (∑ k ∈ supports n m j, lp.single 1 k (a.1 k) : lp (fun _ : ℤ => ℝ) 1) k = _
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Finset.sum_pi_single]

theorem actions_tendsto (a : PosL1) (n m : ℤ) :
    Tendsto (actions a n m) atTop (𝓝 a) := by
  apply tendsto_subtype_rng.2
  exact (lp.hasSum_single (p := (1 : ℝ≥0∞)) (by simp) a.1).comp (supports_tendsto n m)

theorem actions_pair (a : PosL1) (n m : ℤ) (j : ℕ) :
    (actions a n m j).1 n = a.1 n ∧ (actions a n m j).1 m = a.1 m := by
  simp only [actions_apply, (pair_mem n m j).1, (pair_mem n m j).2, ite_true, and_self]

/-- Every active frequency is the unique limit along finite truncations. -/
theorem active_limit (ν : PosL1 → ℝ) (n : ℤ)
    (hν : ContinuousOn ν {a : PosL1 | 0 < a.1 n})
    (a : PosL1) (ha : 0 < a.1 n) (m : ℤ) :
    Tendsto (fun j => ν (actions a n m j)) atTop (𝓝 (ν a)) ∧
      ∀ l : ℝ, Tendsto (fun j => ν (actions a n m j)) atTop (𝓝 l) → l = ν a := by
  have h : Tendsto (fun j => ν (actions a n m j)) atTop (𝓝 (ν a)) :=
    (hν a ha).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨actions_tendsto a n m,
      Eventually.of_forall fun j => by
        change 0 < (actions a n m j).1 n
        rw [(actions_pair a n m j).1]
        exact ha⟩)
  exact ⟨h, fun l hl => tendsto_nhds_unique hl h⟩

/-- The conclusion applies to any finite-action formula already identified with the active
frequency. This is the passage to the limit only; item (iii) supplies the finite formula. -/
theorem finite_formula_limit (ν : PosL1 → ℝ) (n : ℤ)
    (hν : ContinuousOn ν {a : PosL1 | 0 < a.1 n})
    (a : PosL1) (ha : 0 < a.1 n) (m : ℤ) (formula : ℕ → ℝ)
    (hf : ∀ j, formula j = ν (actions a n m j)) :
    Tendsto formula atTop (𝓝 (ν a)) := by
  exact (active_limit ν n hν a ha m).1.congr fun j => (hf j).symm

/-- A continuous extension of values on finite action supports is unique on the active domain. -/
theorem continuous_extension_unique (f g : PosL1 → ℝ) (n : ℤ)
    (hf : ContinuousOn f {a : PosL1 | 0 < a.1 n})
    (hg : ContinuousOn g {a : PosL1 | 0 < a.1 n})
    (hfg : ∀ a : PosL1, 0 < a.1 n → (∃ F : Finset ℤ, ∀ k ∉ F, a.1 k = 0) → f a = g a)
    (a : PosL1) (ha : 0 < a.1 n) : f a = g a := by
  have heq : ∀ j, f (actions a n n j) = g (actions a n n j) := by
    intro j
    apply hfg _ (by rw [(actions_pair a n n j).1]; exact ha)
    refine ⟨supports n n j, fun k hk => ?_⟩
    simp only [actions_apply,if_neg hk]
  exact tendsto_nhds_unique (active_limit f n hf a ha n).1
    ((active_limit g n hg a ha n).1.congr fun j => (heq j).symm)

/-- The actual physical-flow frequencies satisfy the rough continuous-limit clause.
Only the exact REG-015 predecessor input is open; no finite moment is required. -/
theorem physical_rough_limitInput {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (hR : REF88Reg015.Reg015Input L κ hκ) {Φ : PhysicalTensor.L2T L → REF88Chart.K}
    (hΦ : REF88PrintedChart.PrintedChart hκ Φ) :
    ∃ ν : ℤ → PosL1 → ℝ,
      (∀ (u : PhysicalTensor.L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (L2Flow.flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ u n) ∧
      (∀ n, ContinuousOn (ν n) {a : PosL1 | 0 < a.1 n}) ∧
      ∀ (a : PosL1) (n m : ℤ), 0 < a.1 n →
        Tendsto (fun j => ν n (actions a n m j)) atTop (𝓝 (ν n a)) ∧
        ∀ l : ℝ, Tendsto (fun j => ν n (actions a n m j)) atTop (𝓝 l) → l = ν n a := by
  obtain ⟨ν,hrot,-,-,hcont,-,-⟩ := (REF88StageC.stageC hκ hR hΦ).1
  exact ⟨ν,hrot,hcont,fun a n m ha => active_limit (ν n) n (hcont n) a ha m⟩

#print axioms continuous_extension_unique
#print axioms physical_rough_limitInput
#print axioms actions_tendsto
#print axioms active_limit
#print axioms finite_formula_limit
end QuantumNLS.REF88SRoughLimit
