import QuantumNLS.ActualGapDataR26

/-! Deterministic transfer stability for both orientations of the actual gap.
Only accepted response, selection and occupation-limit statements are composed. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace QuantumNLS.ActualGapTransferR26
open ActualGapDataR26
open PhysicalTensor (L2T)
open BetheLabels (MArr arrRoots)
open AdjacentResponse (transfer transfer_receiver transfer_transfer transfer_apply l1_response)
open F04SelBand (Mu II)
open RootOccupationLimit (occDist occVec)
open StepIntegrals (stepL2)
open StrongLimitBulk (Q2)
variable {L κ : ℝ} [Fact (0 < L)]

/-- A one-particle transfer changes the occupation distance by at most `2/N`. -/
theorem occ_transfer_le (hκ : 0 < κ) (u : L2T L) {N : ℕ} (hN : 0 < N)
    (m : MArr N) {a b : ℤ} (ha : 1 ≤ m.1 a) :
    occDist hκ u N (transfer m ha b) ≤ occDist hκ u N m + 2 / N := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let d (k : ℤ) : ℝ := (if k = a then 1 / (N : ℝ) else 0) + (if k = b then 1 / (N : ℝ) else 0)
  have hd : Summable d := by
    apply summable_of_ne_finset_zero (s := {a,b})
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    simp [d,hk.1,hk.2]
  have hdt : ∑' k, d k = 2 / (N : ℝ) := by
    have hs1 : Summable (fun k : ℤ => if k = a then 1 / (N : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := {a}) (by intro k hk; simp only [Finset.mem_singleton] at hk; simp [hk])
    have hs2 : Summable (fun k : ℤ => if k = b then 1 / (N : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := {b}) (by intro k hk; simp only [Finset.mem_singleton] at hk; simp [hk])
    rw [show d = (fun k => (if k = a then 1 / (N : ℝ) else 0) +
      (if k = b then 1 / (N : ℝ) else 0)) from rfl,hs1.tsum_add hs2]
    simp only [tsum_ite_eq]; ring
  have hp : ∀ k : ℤ, |occVec N (transfer m ha b) k - II hκ u k| ≤
      |occVec N m k - II hκ u k| + d k := by
    intro k
    have hh : ((transfer m ha b).1 k : ℝ) = (m.1 k : ℝ) -
        (if k = a then 1 else 0) + (if k = b then 1 else 0) := by
      exact_mod_cast transfer_apply m ha b k
    have habs := abs_le.1 (le_refl |occVec N m k - II hκ u k|)
    dsimp only [occVec,d]
    rw [hh]
    split_ifs <;> simp only [add_div,sub_div,sub_zero,add_zero] <;> rw [abs_le] <;> constructor <;>
      dsimp only [occVec] at habs <;> linarith [one_div_pos.2 hn]
  have hs := RootOccupationLimit.summable_occDist hκ u N m
  calc occDist hκ u N (transfer m ha b)
      ≤ ∑' k, (|occVec N m k - II hκ u k| + d k) :=
        Summable.tsum_le_tsum hp (RootOccupationLimit.summable_occDist hκ u N _) (hs.add hd)
    _ = occDist hκ u N m + 2 / N := by rw [hs.tsum_add hd,hdt]; rfl

/-- Finite early terms may be filled with a single-label array. -/
theorem patch_donor (hκ : 0 < κ) (u : L2T L) (D : Data hκ u)
    (m : ∀ n : ℕ, MArr (n + 1))
    (he : Tendsto (fun n : ℕ => err D (n + 1) (m n)) atTop (𝓝 0))
    {a : ℤ} (ha : 0 < II hκ u a) :
    ∃ p : ∀ n : ℕ, MArr (n + 1), (∀ n, 1 ≤ (p n).1 a) ∧
      (∀ᶠ n : ℕ in atTop, p n = m n) ∧
      Tendsto (fun n : ℕ => err D (n + 1) (p n)) atTop (𝓝 0) := by
  classical
  have hoc := (err_limits D m he).1
  have ho : Tendsto (fun n : ℕ => ((m n).1 a : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (II hκ u a)) :=
    DetGapMain.occ_tendsto hκ u m (by simpa only [occDist,occVec,Nat.cast_add,Nat.cast_one] using hoc) a
  have hd : ∀ᶠ n : ℕ in atTop, 1 ≤ (m n).1 a := by
    filter_upwards [ho.eventually (lt_mem_nhds ha)] with n hn
    have hpos : (0 : ℝ) < (m n).1 a := by
      have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).1 hn
      simpa only [zero_mul] using hh
    exact_mod_cast hpos
  let p : ∀ n : ℕ, MArr (n + 1) := fun n =>
    if 1 ≤ (m n).1 a then m n else singleArr (n + 1) a
  have hpe : ∀ᶠ n : ℕ in atTop, p n = m n := hd.mono fun n hn => ite_eq_left hn
  refine ⟨p,fun n => ?_,hpe,he.congr' (hpe.mono fun n hn => congrArg (err D (n + 1)) hn.symm)⟩
  dsimp only [p]
  split_ifs with hn
  · exact hn
  · simp [singleArr]

/-- Transfer preserves both deterministic inputs, including quadratic Wasserstein convergence. -/
theorem transfer_limits (hκ : 0 < κ) (u : L2T L) (D : Data hκ u)
    (m : ∀ n : ℕ, MArr (n + 1)) {a b : ℤ} (ha : ∀ n, 1 ≤ (m n).1 a) (hab : a ≠ b)
    (hoc : Tendsto (fun n : ℕ => occDist hκ u (n + 1) (m n)) atTop (𝓝 0))
    (hq : Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) (m n)) - Q2 D.bd‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => occDist hκ u (n + 1) (transfer (m n) (ha n) b)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) (transfer (m n) (ha n) b)) - Q2 D.bd‖)
      atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n : ℕ => 2 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have ho : Tendsto (fun n : ℕ => occDist hκ u (n + 1) (transfer (m n) (ha n) b)) atTop (𝓝 0) := squeeze_zero (fun n : ℕ => RootOccupationLimit.occDist_nonneg hκ u _ _)
    (fun n : ℕ => occ_transfer_le hκ u (b := b) (Nat.succ_pos n) (m n) (ha n))
    (by simpa using hoc.add hsmall)
  refine ⟨ho, ?_⟩
  simp only [Nat.cast_add,Nat.cast_one]
  apply DetGapW2.quantile_conv_of_W2 (C := 2 * Real.pi / L * |(a : ℝ) - b|) D.bd
    (fun n : ℕ => (RootContraction.isActual_roots (Fact.out : 0 < L) (by positivity : 0 < κ / ((n : ℝ) + 1))
      (AdjacentResponse.labs_mono (m n))).sorted.monotone)
    (wasserstein D m hq)
  intro n
  have hc : 0 < κ / ((n : ℝ) + 1) := by positivity
  change (∑ j, |arrRoots L (κ / ((n : ℝ) + 1)) (transfer (m n) (ha n) b) j -
    arrRoots L (κ / ((n : ℝ) + 1)) (m n) j|) ≤ _
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rw [l1_response (Fact.out : 0 < L) hc (m n) (ha n) hlt]
    rw [abs_of_neg (sub_neg.2 (by exact_mod_cast hlt))]
    have : (b : ℝ) - a = -((a : ℝ) - b) := by ring
    rw [this]
  · have hb := transfer_receiver (m n) (ha n) hab.symm
    have hh := l1_response (Fact.out : 0 < L) hc (transfer (m n) (ha n) b) hb hgt
    rw [transfer_transfer (m n) (ha n) hab.symm] at hh
    simp_rw [abs_sub_comm (arrRoots L (κ / ((n : ℝ) + 1)) (m n) _)] at hh
    -- One bound works for either orientation.
    rw [hh,abs_of_pos (sub_pos.2 (by exact_mod_cast hgt))]

/-- The accepted deterministic proposition, fed by the error limits. -/
theorem forward (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (D : Data hκ u)
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (m : ∀ n : ℕ, MArr (n + 1)) (hmb : ∀ n, 1 ≤ (m n).1 b)
    (hoc : Tendsto (fun n : ℕ => occDist hκ u (n + 1) (m n)) atTop (𝓝 0))
    (hq : Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) (m n)) - Q2 D.bd‖)
      atTop (𝓝 0)) :
    IntervalIntegrable D.integrand volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => F02Tightness.Q2 L (κ / ((n + 1 : ℕ) : ℝ)) (transfer (m n) (hmb n) a) -
      F02Tightness.Q2 L (κ / ((n + 1 : ℕ) : ℝ)) (m n)) atTop (𝓝 (D.omega a b)) := by
  have hw := wasserstein D m hq
  have hm := fun n : ℕ => (RootContraction.isActual_roots (Fact.out : 0 < L)
    (by positivity : 0 < κ / ((n : ℝ) + 1)) (AdjacentResponse.labs_mono (m n))).sorted.monotone
  have hh := DetGapFinal.deterministic_gap hκ u hu D.bulk hab hb ha m hmb
    (by simpa only [occDist,occVec,Nat.cast_add,Nat.cast_one] using hoc)
    (VarW2Weak.weak_of_W2 D.bd hm hw) hw D.response D.fm D.pull D.xl
    (fun _ _ _ _ _ _ => D.phase _)
  refine ⟨hh.1, ?_⟩
  simpa only [Data.omega,Data.integrand,F02Tightness.Q2,Nat.cast_add,Nat.cast_one] using hh.2

/-- Both oriented gaps converge, and their frequency integrals are finite. -/
theorem deterministic_actual (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (D : Data hκ u)
    {a b : ℤ} (hab : a ≠ b) (ha : 0 < II hκ u a) (hb : 0 < II hκ u b)
    (m : ∀ n : ℕ, MArr (n + 1))
    (he : Tendsto (fun n : ℕ => err D (n + 1) (m n)) atTop (𝓝 0)) :
    IntervalIntegrable D.integrand volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => F02Tightness.gap L κ a b (m n)) atTop (𝓝 (D.omega a b)) := by
  obtain ⟨p,hp,hpm,hpe⟩ := patch_donor hκ u D m he ha
  obtain ⟨hoc,hq⟩ := err_limits D p hpe
  have hc : ∀ n : ℕ, 0 < κ / ((n : ℝ) + 1) := fun n => by positivity
  have hfinal : (Tendsto (fun n : ℕ => F02Tightness.gap L κ a b (p n)) atTop (𝓝 (D.omega a b))) →
      Tendsto (fun n : ℕ => F02Tightness.gap L κ a b (m n)) atTop (𝓝 (D.omega a b)) :=
    fun h => h.congr' (hpm.mono fun n hn => congrArg (F02Tightness.gap L κ a b) hn)
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · obtain ⟨hi,ht⟩ := forward hκ u hu D hlt ha hb p hp hoc hq
    refine ⟨hi.symm,hfinal ?_⟩
    have hn := ht.neg
    have hw : -(D.omega b a) = D.omega a b := by
      unfold Data.omega
      rw [intervalIntegral.integral_symm (a := (a : ℝ)) (b := (b : ℝ))]
      ring
    rw [hw] at hn
    refine hn.congr fun n => ?_
    simp only [F02Tightness.gap,dite_eq_left (hp n)]
    ring
  · let η : ∀ n : ℕ, MArr (n + 1) := fun n => transfer (p n) (hp n) b
    have hη : ∀ n, 1 ≤ (η n).1 b := fun n => transfer_receiver (p n) (hp n) hab.symm
    obtain ⟨hoη,hqη⟩ := transfer_limits hκ u D p hp hab hoc hq
    obtain ⟨hi,ht⟩ := forward hκ u hu D hgt hb ha η hη hoη hqη
    refine ⟨hi,hfinal (ht.congr fun n => ?_)⟩
    simp only [F02Tightness.gap,dite_eq_left (hp n),η,transfer_transfer (p n) (hp n) hab.symm]

end QuantumNLS.ActualGapTransferR26
#print axioms QuantumNLS.ActualGapTransferR26.deterministic_actual
