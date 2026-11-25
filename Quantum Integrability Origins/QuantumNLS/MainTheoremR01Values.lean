import QuantumNLS.AllOrderEnergyFinalR60a

/-!
# MainTheoremR01Values: part (i) of R-AF8F7562 `thm:main` (values and actions)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex`, lines 9-23 (part (i)); proof
`source-text/chapters/core/correspondence_theorem.tex`, lines 11-15 ("For part (i), Lemma lem:audit-weighted ...").

Part (i) is assembled from the accepted R-115CAA16 final `Bind7B115CAA16H02.audit_weighted_printed`
(weighted occupations in probability) and from the accepted R-568BCDF8 packet clause
`AllOrderEnergyPacketsR57a.common_packets_prepared` at the accepted R-115CAA16 binding
`AllOrderEnergyFinalR60a.weighted_bound` (the SAME common packet sequence, with its DEF-031 energy preparation,
which part (iv) refers to as "the common energy-recovering packets in part (i)").

Derived here (no new objects):
* `scaled_charge_eq`: `N⁻¹ Q_{N,r}` on a vector of its domain is the spectral multiplier of `Λ_{N,r}/N`;
* `values_norm`: the printed `‖(N⁻¹Q_{N,r} - I_{r+1}(u))Φ_N‖ → 0` from the support-uniform values;
* `weight_le_weightAbs`, `weightAbs_le`: `(1+n²)^{p/2} ≤ (1+|n|)^p ≤ 2^{p/2}(1+n²)^{p/2}`;
* `errorAbs_le`, `actions_abs`: the original `(1+|n|)^p`-weighted conclusion in probability.

No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology MeasureTheory
open scoped InnerProductSpace

namespace QuantumNLS.MainTheoremR01Values

open Def033HierarchyR24m (Smooth physical)
open BetheCoefficientTransform (BetheBasis HN productVec)
open BetheLabels (MArr)
open CommonBethePacket (Packet vector support)
open BulkResponseActual (physBasis)
open EmpiricalRapidity (bornMeasure)
open TensorCarrier (htpow)
open EnergyPreparationDef (EnergyPreparation)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The spectral charge `Q_{N,r}` (DEF-008) on the physical Bethe basis at coupling `κ/N`. -/
abbrev Q (hκ : 0 < κ) (N r : ℕ) : HN L N →ₗ.[ℂ] HN L N :=
  BetheSpectralCharges.charge (physBasis L hκ N) (κ / N) r

/-- The classical value `I_{r+1}^{(κ)}(u)`. -/
abbrev Ival (κ : ℝ) (u : Smooth L) (r : ℕ) : ℝ := (ClassicalCharges.charge L κ u.val (r + 1)).re

/-- The original theorem's weight `(1+|n|)^p`. -/
def weightAbs (p : ℝ) (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ p

/-- The weighted occupation error with the original weight `(1+|n|)^p`. -/
def errorAbs (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (p : ℝ) (N : ℕ) (m : MArr N) : ℝ :=
  ∑' n : ℤ, weightAbs p n * |(m.1 n : ℝ) / N - (QuantumNLS.RootIndexedMasses.masses hκ u).1 n|

/-! ### The weight comparison -/

theorem weight_le_weightAbs (p : ℝ) (hp : 0 ≤ p) (n : ℤ) :
    AuditWeightedSeriesR49a.weight p n ≤ weightAbs p n := by
  unfold AuditWeightedSeriesR49a.weight weightAbs
  have h0 : (0 : ℝ) ≤ 1 + |(n : ℝ)| := by positivity
  have h1 : (1 + (n : ℝ) ^ 2) ≤ (1 + |(n : ℝ)|) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)]
  calc (1 + (n : ℝ) ^ 2) ^ (p / 2) ≤ ((1 + |(n : ℝ)|) ^ (2 : ℝ)) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = (1 + |(n : ℝ)|) ^ p := by
        rw [← Real.rpow_mul h0]
        congr 1
        ring

theorem weightAbs_le (p : ℝ) (hp : 0 ≤ p) (n : ℤ) :
    weightAbs p n ≤ (2 : ℝ) ^ (p / 2) * AuditWeightedSeriesR49a.weight p n := by
  unfold AuditWeightedSeriesR49a.weight weightAbs
  have h0 : (0 : ℝ) ≤ 1 + |(n : ℝ)| := by positivity
  have h1 : (1 + |(n : ℝ)|) ^ (2 : ℝ) ≤ 2 * (1 + (n : ℝ) ^ 2) := by
    rw [Real.rpow_two]
    nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]
  calc (1 + |(n : ℝ)|) ^ p = ((1 + |(n : ℝ)|) ^ (2 : ℝ)) ^ (p / 2) := by
        rw [← Real.rpow_mul h0]
        congr 1
        ring
    _ ≤ (2 * (1 + (n : ℝ) ^ 2)) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = (2 : ℝ) ^ (p / 2) * (1 + (n : ℝ) ^ 2) ^ (p / 2) :=
        Real.mul_rpow (by norm_num) (by positivity)

/-- The `(1+|n|)^p` error is at most `2^{p/2}` times the printed error (both as Lean `tsum`s). -/
theorem errorAbs_le (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (p : ℝ) (hp : 0 ≤ p) (N : ℕ)
    (m : MArr N) :
    errorAbs hκ u p N m ≤ (2 : ℝ) ^ (p / 2) * AuditWeightedProbabilityR49a.error hκ u p N m := by
  unfold errorAbs AuditWeightedProbabilityR49a.error
  set d : ℤ → ℝ := fun n => |(m.1 n : ℝ) / N - (QuantumNLS.RootIndexedMasses.masses hκ u).1 n|
  have hd : ∀ n, 0 ≤ d n := fun n => abs_nonneg _
  have hw : ∀ n, 0 ≤ AuditWeightedSeriesR49a.weight p n :=
    fun n => (AuditWeightedSeriesR49a.weight_pos p n).le
  have hle : ∀ n, weightAbs p n * d n ≤ (2 : ℝ) ^ (p / 2) * (AuditWeightedSeriesR49a.weight p n * d n) := by
    intro n
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weightAbs_le p hp n) (hd n)
  have hnn : ∀ n, 0 ≤ weightAbs p n * d n := fun n => mul_nonneg (by unfold weightAbs; positivity) (hd n)
  have hpos : 0 ≤ ∑' n : ℤ, AuditWeightedSeriesR49a.weight p n * d n :=
    tsum_nonneg fun n => mul_nonneg (hw n) (hd n)
  by_cases hs : Summable (fun n => AuditWeightedSeriesR49a.weight p n * d n)
  · have hs' : Summable (fun n => weightAbs p n * d n) :=
      Summable.of_nonneg_of_le hnn hle (hs.mul_left _)
    calc (∑' n : ℤ, weightAbs p n * d n)
        ≤ ∑' n : ℤ, (2 : ℝ) ^ (p / 2) * (AuditWeightedSeriesR49a.weight p n * d n) :=
          hs'.tsum_le_tsum hle (hs.mul_left _)
      _ = (2 : ℝ) ^ (p / 2) * ∑' n : ℤ, AuditWeightedSeriesR49a.weight p n * d n := tsum_mul_left
  · have hs' : ¬ Summable (fun n => weightAbs p n * d n) := by
      intro h
      exact hs (Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (hd n))
        (fun n => mul_le_mul_of_nonneg_right (weight_le_weightAbs p hp n) (hd n)) h)
    rw [tsum_eq_zero_of_not_summable hs']
    exact mul_nonneg (by positivity) hpos

/-! ### Scaled charges on finite packets -/

theorem scaled_charge_eq {N : ℕ} (b : BetheBasis L N) (c : ℝ) (r : ℕ) (x : HN L N)
    (hx : x ∈ (BetheSpectralCharges.charge b c r).domain)
    (hx' : x ∈ (BetheSpectralCharges.multiplier b
      (fun m => BetheSpectralCharges.eigenvalue L N c r m / (N : ℝ))).domain) :
    (N : ℂ)⁻¹ • BetheSpectralCharges.charge b c r ⟨x, hx⟩ =
      BetheSpectralCharges.multiplier b
        (fun m => BetheSpectralCharges.eigenvalue L N c r m / (N : ℝ)) ⟨x, hx'⟩ := by
  apply b.repr.injective
  ext m
  rw [LinearIsometryEquiv.map_smul]
  change (N : ℂ)⁻¹ • (b.repr (BetheSpectralCharges.multiplier b
      (BetheSpectralCharges.eigenvalue L N c r) ⟨x, hx⟩)) m = _
  simp only [smul_eq_mul, HilbertBasis.repr_apply_apply,
    BetheSpectralCharges.multiplier_coord]
  push_cast
  ring

/-- **Printed values, norm form.** On a finite packet whose support values are uniformly within `ε` of `I`,
`‖(N⁻¹ Q_{N,r} - I) Φ‖ ≤ ε`. -/
theorem values_residual (hκ : 0 < κ) {N : ℕ} (P : Packet (physBasis L hκ N)) (r : ℕ) (I ε : ℝ)
    (hε : 0 ≤ ε)
    (hb : ∀ m ∈ support P, |BetheSpectralCharges.eigenvalue L N (κ / N) r m / (N : ℝ) - I| ≤ ε)
    (hx : vector P ∈ (Q hκ N r).domain) :
    ‖(N : ℂ)⁻¹ • Q hκ N r ⟨vector P, hx⟩ - (I : ℂ) • vector P‖ ≤ ε := by
  rw [scaled_charge_eq (physBasis L hκ N) (κ / N) r (vector P) hx
    (AuditWeightedPacketR49a.packet_mem_every_domain _ P _)]
  exact AllOrderEnergyPacketsR57a.packet_residual (physBasis L hκ N) P _ I ε hε hb

/-! ### Part (i) -/

/-- **Part (i), packet clause** (principal_correspondence.tex:11-15, 23, with eq:values-main): one sequence of
normalized finite Bethe packets `Φ_N` (the `Packet` structure carries normalization), norm-close to `u^{⊗N}`, in
every charge domain `D(Q_{N,s})`, with `‖(N⁻¹Q_{N,r} - I_{r+1}(u))Φ_N‖ → 0` for every fixed `r`; the original
support-uniform values and weighted occupations on the same packets; and the DEF-031 energy preparation of the
same packets (used by part (iv): "the common energy-recovering packets in part (i)"). -/
def PacketClause (hκ : 0 < κ) (u : Smooth L) : Prop :=
  ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
    Tendsto (fun N => ‖vector (P N) - productVec L N (physical u)‖) atTop (𝓝 0) ∧
    (∃ hdom : ∀ N s, vector (P N) ∈ (Q hκ N s).domain,
      ∀ r : ℕ, Tendsto (fun N : ℕ => ‖(N : ℂ)⁻¹ • Q hκ N r ⟨vector (P N), hdom N r⟩ -
        ((Ival κ u r : ℝ) : ℂ) • vector (P N)‖) atTop (𝓝 0)) ∧
    (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
      |BetheSpectralCharges.eigenvalue L N (κ / N) r m / (N : ℝ) - Ival κ u r| ≤ ε) ∧
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
      AuditWeightedProbabilityR49a.error hκ (physical u) p N m ≤ ε) ∧
    EnergyPreparation κ (physical u)
      (fun N => Nat.casesOn N (htpow 0 (physical u)) (fun n => (vector (P (n + 1))).val))

/-- **Part (i), actions** (eq:actions-main and the weight remark, principal_correspondence.tex:16-22). -/
def ActionsClause (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) : Prop :=
  (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
      {m | ε < AuditWeightedProbabilityR49a.error hκ (physical u) p N m}) atTop (𝓝 0)) ∧
  (∀ p : ℝ, 0 ≤ p → ∀ n : ℤ,
    AuditWeightedSeriesR49a.weight p n ≤ weightAbs p n ∧
      weightAbs p n ≤ (2 : ℝ) ^ (p / 2) * AuditWeightedSeriesR49a.weight p n) ∧
  (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
      {m | ε < errorAbs hκ (physical u) p N m}) atTop (𝓝 0))

theorem packet_clause (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    PacketClause hκ u := by
  obtain ⟨P, hcharge, hweight, hprep, -⟩ :=
    AllOrderEnergyPacketsR57a.common_packets_prepared hκ (AllOrderEnergyFinalR60a.weighted_bound hκ) u hu
  have hclose1 : Tendsto (fun n => ‖vector (P (n + 1)) - productVec L (n + 1) (physical u)‖) atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 1).mpr hprep.normClose.2
    refine h.congr (fun n => ?_)
    change ‖(vector (P (n + 1))).val - htpow (n + 1) (physical u)‖ = _
    rw [← BetheCoefficientTransform.productVec_coe (N := n + 1) (physical u), ← Submodule.coe_sub,
      Submodule.norm_coe]
  have hclose : Tendsto (fun N => ‖vector (P N) - productVec L N (physical u)‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hclose1
  have hdom : ∀ N s, vector (P N) ∈ (Q hκ N s).domain :=
    fun N s => AuditWeightedPacketR49a.packet_mem_every_domain _ (P N) _
  refine ⟨P, hclose, ⟨hdom, fun r => ?_⟩, hcharge, hweight, hprep⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hcharge r (ε / 2) (half_pos hε)] with N hN
  rw [dist_zero_right, norm_norm]
  exact (values_residual hκ (P N) r _ (ε / 2) (half_pos hε).le hN (hdom N r)).trans_lt (half_lt_self hε)

theorem actions_clause (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    ActionsClause hκ u hu := by
  have h1 : ∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
        {m | ε < AuditWeightedProbabilityR49a.error hκ (physical u) p N m}) atTop (𝓝 0) :=
    (Bind7B115CAA16H02.audit_weighted_printed (L := L) hκ u.property hu).1
  refine ⟨h1, fun p hp n => ⟨weight_le_weightAbs p hp n, weightAbs_le p hp n⟩, ?_⟩
  intro p hp ε hε
  have hc : 0 < (2 : ℝ) ^ (p / 2) := by positivity
  have h := h1 p hp (ε / (2 : ℝ) ^ (p / 2)) (div_pos hε hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) (fun N => ?_)
  refine measure_mono (fun m hm => ?_)
  simp only [Set.mem_ofPred_eq] at hm ⊢
  have he := errorAbs_le hκ (physical u) p hp N m
  rw [div_lt_iff₀ hc]
  linarith [mul_comm ((2 : ℝ) ^ (p / 2)) (AuditWeightedProbabilityR49a.error hκ (physical u) p N m)]

end QuantumNLS.MainTheoremR01Values

#print axioms QuantumNLS.MainTheoremR01Values.packet_clause
#print axioms QuantumNLS.MainTheoremR01Values.actions_clause
