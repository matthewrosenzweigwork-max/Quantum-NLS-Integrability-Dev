import QuantumNLS.REF88Reg015Bridge
import QuantumNLS.REF88PrintedChart

/-! R-EF8C2837 item (iv), physical_cubic.tex:316–337, sha256 64ec3e0215716404f81e6dabec749fe6cab471b8ff7ed8284127f8160c275115.
Finite coordinate truncation containing a prescribed pair, in every weighted space.
`physical_truncationInput` uses precisely the named REG-015 input, with no extra input.
`physical_truncation_of_final` uses the conditional REG-015 bridge (review pending).
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
namespace QuantumNLS.REF88STruncation
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.REF88Chart QuantumNLS.REF88Reg015 QuantumNLS.REF88PrintedChart
variable {L κ : ℝ} [Fact (0 < L)]

/-- Increasing finite sets, each containing both prescribed indices. -/
def supports (a b : ℤ) (j : ℕ) : Finset ℤ := Finset.Icc (-(j : ℤ)) (j : ℤ) ∪ {a,b}

theorem pair_mem (a b : ℤ) (j : ℕ) : a ∈ supports a b j ∧ b ∈ supports a b j := by
  simp [supports]

theorem supports_mono (a b : ℤ) : Monotone (supports a b) := by
  intro j k hjk n hn
  simp only [supports, Finset.mem_union, Finset.mem_Icc] at hn ⊢
  rcases hn with ⟨h1,h2⟩ | h
  · left; constructor <;> omega
  · exact Or.inr h

theorem supports_tendsto (a b : ℤ) : Tendsto (supports a b) atTop atTop := by
  apply tendsto_atTop.2
  intro F
  have h : ∀ n ∈ F, ∀ᶠ j : ℕ in atTop, n ∈ supports a b j := by
    intro n _
    filter_upwards [eventually_ge_atTop n.natAbs] with j hj
    apply Finset.mem_union_left
    simp only [Finset.mem_Icc]
    constructor <;> omega
  simpa only [Finset.subset_iff] using
    ((Filter.eventually_all_finset F).2 h)

/-- Actual coordinate truncation in an arbitrary positive weighted Hilbert space. -/
def trunc (W : PosWeight) (F : Finset ℤ) (z : WSeq W) : WSeq W :=
  WSeq.mk W (fun n => if n ∈ F then z.val n else 0) (by
    apply summable_of_ne_finset_zero (s := F)
    intro n hn; simp [hn])

@[simp] theorem trunc_apply (W : PosWeight) (F : Finset ℤ) (z : WSeq W) (n : ℤ) :
    (trunc W F z).val n = if n ∈ F then z.val n else 0 := rfl

theorem trunc_tendsto (W : PosWeight) (a b : ℤ) (z : WSeq W) :
    Tendsto (fun j => trunc W (supports a b j) z) atTop (𝓝 z) := by
  have he : ∀ F : Finset ℤ, toL2 W (trunc W F z) =
      ∑ n ∈ F, lp.single 2 n ((toL2 W z) n) := by
    intro F
    apply lp.ext; funext n
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_single, Finset.sum_pi_single, toL2_apply, trunc_apply]
    split_ifs <;> simp_all
  have h := (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by simp) (toL2 W z)).comp
    (supports_tendsto a b)
  have hh := ((toL2ᵢ W).symm.continuous.tendsto (toL2 W z)).comp h
  have hz : (toL2ᵢ W).symm (toL2 W z) = z := (toL2ᵢ W).symm_apply_apply z
  rw [hz] at hh
  exact hh.congr fun j => by
    change (toL2ᵢ W).symm (∑ n ∈ supports a b j, lp.single 2 n ((toL2 W z) n)) = _
    rw [← he]
    exact (toL2ᵢ W).symm_apply_apply _

/-- Finite-action physical approximants containing the active pair, converging in H^s.
The coordinate identity is exact, including zero coordinates. -/
theorem physical_truncationInput (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ)
    (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) (a b : ℤ) :
    ∃ v : ℕ → H02 L s,
      Tendsto v atTop (𝓝 u) ∧
      ∀ j n, Φ (H02.toL2 hs (v j)) n =
        if n ∈ supports a b j then Φ (H02.toL2 hs u) n else 0 := by
  obtain ⟨hcΦ,hcΨ⟩ := printedChart_continuity hκ hΦ
  obtain ⟨e,he⟩ := sobolev_homeomorphism hκ hR hΦ.symp hcΦ hcΨ hΦ.moduli s hs
  let v : ℕ → H02 L s := fun j => e.symm (trunc (def002 L s) (supports a b j) (e u))
  refine ⟨v, ?_, ?_⟩
  · have h := (e.symm.continuous.tendsto (e u)).comp (trunc_tendsto (def002 L s) a b (e u))
    simpa only [Function.comp_def, v, e.symm_apply_apply] using h
  · intro j n
    have hv := congrArg (fun z : K => z n) (he (v j))
    rw [← hv, toK_apply]
    change (e (e.symm _)).val n = _
    rw [e.apply_symm_apply, trunc_apply]
    have hu := congrArg (fun z : K => z n) (he u)
    rw [toK_apply] at hu
    rw [hu]

/-- Conditional implementation of the printed H¹ truncation using REG-015's final build.
This does not assert predecessor acceptance. -/
theorem physical_truncation_of_final (hκ : 0 < κ)
    {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ) (u : H02 L 1) (a b : ℤ) :
    ∃ v : ℕ → H02 L 1, Tendsto v atTop (𝓝 u) ∧
      ∀ j n, Φ (H02.toL2 (by norm_num : (0 : ℝ) ≤ 1) (v j)) n =
        if n ∈ supports a b j then Φ (H02.toL2 (by norm_num : (0 : ℝ) ≤ 1) u) n else 0 :=
  physical_truncationInput hκ (REF88Reg015Bridge.reg015Input_of_final hκ) hΦ 1 (by norm_num) u a b

#print axioms supports_tendsto
#print axioms trunc_tendsto
#print axioms physical_truncationInput
#print axioms physical_truncation_of_final
end QuantumNLS.REF88STruncation
