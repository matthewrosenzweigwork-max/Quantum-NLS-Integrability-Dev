import QuantumNLS.Reg011SettingR48a
import QuantumNLS.Reg011SequencesR48a
import QuantumNLS.Reg011ReverseTailR48a
import QuantumNLS.TerraMultiRound76MomentBridge
import QuantumNLS.TerraMultiRound77ActionCriteria

/-! REG-011 step 1 (haiku_inventory, module Reg011HReverseMoment).
Reverse direction: convergence of weighted coordinates z_j → z in h^s (0 < s ≤ 2),
pulled back by the inverse of the exact moduli map, gives weighted ℓ¹ convergence of the
root-indexed actions (via the frozen coordinate lemma `squared_moduli_tendsto`), and then
same-order physical moment convergence ∫|t|^{2s} dμ_{u_j} → ∫|t|^{2s} dμ_u through the
uniform-tail excess bound `excess_le_indexed_tail` and the frozen truncation bridge
`moment_convergence_of_uniform_excess`.
Read-only imports of the frozen Reg011SettingR48a, Reg011SequencesR48a, Reg011ReverseTailR48a,
TerraMultiRound76MomentBridge and TerraMultiRound77ActionCriteria. No REG-010 input is used
and no review record unfrozen module is imported. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.RootWeightedCellsR26
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.Reg011HReverseMoment

variable {L κ : ℝ} [Fact (0 < L)] {V : Set Seq}

/-- The DEF-002 weight at order s is the same-order weight (1+|momentum|)^{2s}. -/
theorem def002_w_eq (s : ℝ) (n : ℤ) :
    (def002 L s).w n = (1 + |momentum L n|) ^ (2 * s) := by
  simp only [def002, sobolevWeight, momentum]

/-- Convergence of z_j to z in h^s gives convergence of the points in V, as a subtype. -/
theorem toBase_subtype_tendsto (s : ℝ) (hs : 0 ≤ s) (z : ℕ → h02 L s) (z0 : h02 L s)
    (hz : Tendsto z atTop (𝓝 z0)) (hzV : ∀ j, toBase (L := L) s hs (z j) ∈ V)
    (hV0 : toBase (L := L) s hs z0 ∈ V) :
    Tendsto (fun j => (⟨toBase (L := L) s hs (z j), hzV j⟩ : ↥V)) atTop
      (𝓝 (⟨toBase (L := L) s hs z0, hV0⟩ : ↥V)) := by
  refine tendsto_subtype_rng.mpr ?_
  exact ((toBase (L := L) s hs).continuous.tendsto z0).comp hz

/-- The inverse image map is continuous in the weighted coordinates: L² convergence of u_j. -/
theorem inverse_tendsto (e : L2T L ≃ₜ V) (s : ℝ) (hs : 0 ≤ s)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs (z j) ∈ V) (hV0 : toBase (L := L) s hs z0 ∈ V) :
    Tendsto (fun j => baseInverse e s hs (⟨z j, hzV j⟩ : Target (L := L) V s hs)) atTop
      (𝓝 (baseInverse e s hs (⟨z0, hV0⟩ : Target (L := L) V s hs))) := by
  exact (e.symm.continuous.tendsto _).comp (toBase_subtype_tendsto s hs z z0 hz hzV hV0)

/-- Reverse weighted ℓ¹ action convergence: weighted coordinate convergence in h^s gives
convergence to zero of Σ_n (1+|momentum n|)^{2s} |m_n(u_j) − m_n(u)|, where m_n(u) is the
root-indexed mass of the inverse image u = baseInverse z. -/
theorem action_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ) (hs : 0 ≤ s)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs (z j) ∈ V) (hV0 : toBase (L := L) s hs z0 ∈ V) :
    Tendsto (fun j => ∑' n : ℤ, (1 + |momentum L n|) ^ (2 * s) *
      |(QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs (⟨z j, hzV j⟩ : Target (L := L) V s hs))).1 n -
        (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs (⟨z0, hV0⟩ : Target (L := L) V s hs))).1 n|)
      atTop (𝓝 0) := by
  have hsq := QuantumNLS.Reg011SequencesR48a.squared_moduli_tendsto (def002 L s) z z0 hz
  refine hsq.congr (fun j => ?_)
  apply tsum_congr
  intro n
  rw [def002_w_eq, inverse_moduli e hκ he s hs (⟨z j, hzV j⟩ : Target (L := L) V s hs) n,
    inverse_moduli e hκ he s hs (⟨z0, hV0⟩ : Target (L := L) V s hs) n]

/-- Summability of the same-order indexed actions of an inverse image. -/
theorem masses_summable (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ) (hs : 0 ≤ s)
    (z : h02 L s) (hz : toBase (L := L) s hs z ∈ V) :
    Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs (⟨z, hz⟩ : Target (L := L) V s hs))).1 n) := by
  refine (PosWeight.WSeq.summable z).congr (fun n => ?_)
  rw [def002_w_eq, inverse_moduli e hκ he s hs (⟨z, hz⟩ : Target (L := L) V s hs) n]

/-- REG-011 step 1, same-order physical moment convergence on the reverse side.
For 0 < s ≤ 2, if z_j → z in h^s with z_j ∈ V, then the physical moments of order 2s of the
inverse images converge to the moment of the inverse image of z. -/
theorem moment_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs0.le (z j) ∈ V) (hV0 : toBase (L := L) s hs0.le z0 ∈ V) :
    Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))))
      atTop (𝓝 (∫ t : ℝ, |t| ^ (2 * s)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))))) := by
  have hL : (0 : ℝ) < L := Fact.out
  have hp : (0 : ℝ) < 2 * s := by linarith
  have hu := inverse_tendsto e s hs0.le z z0 hz hzV hV0
  have hv : MeasureTheory.Integrable (fun t : ℝ => |t| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))) :=
    (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s hs0).mpr
      (masses_summable hκ e he s hs0.le z0 hV0)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * Real.sqrt (κ * (‖baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)‖ + 1) ^ 2 / L) :=
    ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hnorm := hu.norm
  -- common confinement bound, uniform in j eventually
  have hconf : ∀ᶠ j in atTop, 2 * Real.sqrt (κ *
      ‖baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)‖ ^ 2 / L) ≤ B := by
    filter_upwards [hnorm.eventually (gt_mem_nhds (lt_add_one
      ‖baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)‖))] with j hj
    have h2 : κ * ‖baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)‖ ^ 2 / L ≤
        κ * (‖baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)‖ + 1) ^ 2 / L := by
      refine div_le_div_of_nonneg_right ?_ hL.le
      refine mul_le_mul_of_nonneg_left ?_ hκ.le
      nlinarith [norm_nonneg (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)),
        norm_nonneg (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))]
    have h3 := Real.sqrt_le_sqrt h2
    rw [hBdef]
    linarith
  -- ℓ¹ difference of weighted actions, from the coordinate lemma
  have hd := action_tendsto hκ e he s hs0.le z z0 hz hzV hV0
  have hd' : Tendsto (fun j => ∑' n : ℤ, |(1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))).1 n -
      (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))).1 n|)
      atTop (𝓝 0) := by
    refine hd.congr (fun j => tsum_congr (fun n => ?_))
    rw [← mul_sub, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (1 + |momentum L n|) ^ (2 * s) by positivity)]
  have ha : ∀ j n, 0 ≤ (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))).1 n :=
    fun j n => mul_nonneg (by positivity)
      ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ _).2.1 n)
  have hb : ∀ n, 0 ≤ (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))).1 n :=
    fun n => mul_nonneg (by positivity)
      ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ _).2.1 n)
  have hi : ∀ j, Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))).1 n) :=
    fun j => masses_summable hκ e he s hs0.le (z j) (hzV j)
  have hbs : Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))).1 n) :=
    masses_summable hκ e he s hs0.le z0 hV0
  -- uniform tail in the indexed cutoff R, from ℓ¹ convergence
  obtain hR := QuantumNLS.Reg011ReverseTailR48a.eventual_lattice_tail (fun n => momentum L n)
    (fun j n => (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))).1 n)
    (fun n => (1 + |momentum L n|) ^ (2 * s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))).1 n)
    ha hb hi hbs hd'
  have hUI : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ j in atTop,
      |(∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
          (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)))) -
        (∫ t : ℝ, min (|t| ^ (2 * s)) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
          (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))))| < ε := by
    intro ε hε
    have hpos : 0 < (1 + B) ^ (2 * s) := Real.rpow_pos_of_pos (by linarith) _
    obtain ⟨R, hRt⟩ := hR (ε / (1 + B) ^ (2 * s)) (div_pos hε hpos)
    refine ⟨⌈((R : ℝ) + B) ^ (2 * s)⌉₊, fun k hk => ?_⟩
    have hcut : ((R : ℝ) + B) ^ (2 * s) ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)
    filter_upwards [hRt, hconf] with j hj hcj
    have hex := QuantumNLS.Reg011ReverseTailR48a.excess_le_indexed_tail hκ
      (baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)) (2 * s) (R : ℝ) B (k : ℝ)
      hp (Nat.cast_nonneg R) hB (Nat.cast_nonneg k) hcj hcut (hi j)
    have hlt := mul_lt_mul_of_pos_left hj hpos
    have hcancel : (1 + B) ^ (2 * s) * (ε / (1 + B) ^ (2 * s)) = ε := by
      field_simp
    rw [hcancel] at hlt
    exact lt_of_le_of_lt hex hlt
  exact QuantumNLS.TerraMultiRound76MomentBridge.moment_convergence_of_uniform_excess hκ
    (fun j => baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le))
    (baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)) (2 * s) hp.le hu hv hUI

#print axioms def002_w_eq
#print axioms toBase_subtype_tendsto
#print axioms inverse_tendsto
#print axioms action_tendsto
#print axioms masses_summable
#print axioms moment_tendsto
end QuantumNLS.Reg011HReverseMoment
