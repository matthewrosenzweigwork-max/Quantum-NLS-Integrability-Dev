import QuantumNLS.REF88SRescale
import QuantumNLS.REF88Reg015Bridge

/-! R-EF8C2837 item (iv): the normalized occupation targets are continuous in ℓ¹.
Only accepted fixed-coupling indexed-mass continuity is used in the proof.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
namespace QuantumNLS.REF88SNormalizedActions
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (II)
open QuantumNLS.RootIndexedMasses (masses)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The normalized indexed probabilities as an ℓ¹ element. -/
def probabilities (hκ : 0 < κ) (u : L2T L) : lp (fun _ : ℤ => ℝ) 1 :=
  (‖u‖ ^ 2)⁻¹ • (masses hκ u).1

theorem probabilities_apply (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (hK : 0 < κ * ‖u‖ ^ 2) (n : ℤ) :
    probabilities hκ u n = II hK (FullMass.unitDir u) n := by
  change (‖u‖ ^ 2)⁻¹ * II hκ u n = _
  rw [REF88QuantumDef.II_unitDir hκ hu hK]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hu)),one_mul]

theorem probabilities_tendsto (hκ : 0 < κ) {v : ℕ → L2T L} {u : L2T L}
    (hu : u ≠ 0) (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun j => probabilities hκ (v j)) atTop (𝓝 (probabilities hκ u)) := by
  have ha : Tendsto (fun j => (masses hκ (v j)).1) atTop (𝓝 (masses hκ u).1) :=
    (continuous_subtype_val.comp (DEF014Continuity.continuous_physical_masses hκ)).tendsto u |>.comp hv
  exact ((hv.norm.pow 2).inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hu))).smul ha

theorem normalized_l1 (hκ : 0 < κ) {v : ℕ → L2T L} {u : L2T L}
    (hu : u ≠ 0) (hv0 : ∀ j, v j ≠ 0) (hv : Tendsto v atTop (𝓝 u))
    (hK : 0 < κ * ‖u‖ ^ 2) (hKs : ∀ j, 0 < κ * ‖v j‖ ^ 2) :
    Tendsto (fun j => ∑' n : ℤ, |II (hKs j) (FullMass.unitDir (v j)) n -
      II hK (FullMass.unitDir u) n|) atTop (𝓝 0) := by
  have h := tendsto_iff_norm_sub_tendsto_zero.1 (probabilities_tendsto hκ hu hv)
  have he : ∀ j, ‖probabilities hκ (v j) - probabilities hκ u‖ =
      ∑' n : ℤ, |II (hKs j) (FullMass.unitDir (v j)) n - II hK (FullMass.unitDir u) n| := by
    intro j
    rw [Reg015Setting.lp_one_norm]
    apply tsum_congr; intro n
    simp only [lp.coeFn_sub,Pi.sub_apply,probabilities_apply hκ (hv0 j) (hKs j),
      probabilities_apply hκ hu hK]
  simpa only [he] using h

/-- Local occupation error plus convergence of the normalized targets gives the exact
fixed-target hη required by the accepted deterministic and varying-coupling gap theorems. -/
theorem occupations_to_target {Ks : ℕ → ℝ} (hKs : ∀ j, 0 < Ks j)
    (v : ℕ → L2T L) {K : ℝ} (hK : 0 < K) (u : L2T L)
    (η : ∀ n : ℕ, BetheLabels.MArr (n + 1))
    (hoc : Tendsto (fun n => RootOccupationLimit.occDist (hKs n) (v n) (n + 1) (η n)) atTop (𝓝 0))
    (hI : Tendsto (fun j => ∑' m : ℤ, |II (hKs j) (v j) m - II hK u m|) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK u m|)
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => RootOccupationLimit.occDist hK u (n + 1) (η n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => RootOccupationLimit.occDist_nonneg _ _ _ _)
      (fun n => ?_) (by simpa only [add_zero] using hoc.add hI)
    have hs : Summable (fun m : ℤ => |II (hKs n) (v n) m - II hK u m|) :=
      REF88Reg015Bridge.summable_abs_lp_one ((masses (hKs n) (v n)).1 - (masses hK u).1)
    calc RootOccupationLimit.occDist hK u (n + 1) (η n)
        ≤ ∑' m : ℤ, (|RootOccupationLimit.occVec (n + 1) (η n) m - II (hKs n) (v n) m| +
          |II (hKs n) (v n) m - II hK u m|) := by
          apply Summable.tsum_le_tsum _ (RootOccupationLimit.summable_occDist _ _ _ _)
            ((RootOccupationLimit.summable_occDist _ _ _ _).add hs)
          intro m
          have := abs_add_le (RootOccupationLimit.occVec (n + 1) (η n) m - II (hKs n) (v n) m)
            (II (hKs n) (v n) m - II hK u m)
          simpa only [sub_add_sub_cancel] using this
      _ = RootOccupationLimit.occDist (hKs n) (v n) (n + 1) (η n) +
          ∑' m : ℤ, |II (hKs n) (v n) m - II hK u m| := by
          rw [Summable.tsum_add (RootOccupationLimit.summable_occDist _ _ _ _) hs]; rfl
  simpa only [RootOccupationLimit.occDist,RootOccupationLimit.occVec,Nat.cast_add,Nat.cast_one] using hsum

#print axioms probabilities_tendsto
#print axioms normalized_l1
#print axioms occupations_to_target
end QuantumNLS.REF88SNormalizedActions
