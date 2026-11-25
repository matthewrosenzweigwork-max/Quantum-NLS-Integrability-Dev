import QuantumNLS.Prop025PacketR59a

/-! PROP-025, mixed_propagation.tex:68–93. The error on lines 88–89 is the
fixed-packet error defined on line 707. The constant and the particle
threshold can still depend on the charge orders, rank, and boxes. -/

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace QuantumNLS.Prop025ProvenanceR59a

open scoped Topology ENNReal
open Filter
open Def033HierarchyR24m (Smooth physical)
open ActualModelTargetR53a (HigherFlows higher target)
open ActualModelCorollaryR53a (EstimateWithZeta boxError preparationError)
open Prop025OFinal (zeta zeta_tendsto zeta_empty main_of_total)
open Prop025OTarget (enum)
open Prop025OParams (alpha)
open PROP018Probability (cut_bounds)
open Prop017Quantum (eta0)
open Prop025PacketR59a (contourErrors core_at_packet)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

omit [Fact (0 < L)] in
private theorem height_gt (κ : ℝ) : eta0 L κ < eta0 L κ + 1 :=
  lt_add_of_pos_right _ zero_lt_one

/-- The contour height and limiting measure used by frozen OMain. -/
def fixedErrors (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (I : Finset ℤ) :
    (ℕ → ℝ) × (ℕ → ℝ) :=
  contourErrors hκ (physical u) hu (FreeLimit.muKappa_spec (physical u) hu hκ)
    (height_gt (L := L) κ) (enum I)

/-- The sequence of PROP-025, using the fixed derivative and count packet. -/
def fixedZeta (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (I : Finset ℤ) (N : ℕ) : ℝ :=
  zeta ((fixedErrors hκ u hu I).1 N) ((fixedErrors hκ u hu I).2 N)

private theorem higher_at_packet (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r)
    (hR2 : ∀ r ∈ R, 2 ≤ r) (hk : 1 ≤ k) :
    Tendsto (fixedZeta hκ u hu I) atTop (𝓝 0) ∧
      (I = ∅ → ∀ N, fixedZeta hκ u hu I N = 0) ∧
      ∃ A : ℝ, 0 ≤ A ∧ EstimateWithZeta hκ M.chart.chart (higher M.dynamics.hierarchy)
        u I R k Θ T A (fixedZeta hκ u hu I) := by
  let d := max 2 (R.sup id)
  have hd : 2 ≤ d := le_max_left _ _
  have hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d := fun r hr =>
    ⟨hR2 r hr, (Finset.le_sup (f := id) hr).trans (le_max_right _ _)⟩
  let T' : ℕ → ℝ := fun r => if r ∈ R then T r else 0
  have hT' : ∀ r, 0 ≤ T' r := fun r => by
    by_cases hr : r ∈ R
    · simpa [T', hr] using hT r hr
    · simp [T', hr]
  have hbox : ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) → ∀ r ∈ R, |t r| ≤ T' r :=
    fun t ht r hr => by simpa [T', hr] using ht r hr
  have hμ := FreeLimit.muKappa_spec (physical u) hu hκ
  have hmom := Prop025OMain.evenMoments hκ (physical u) hu M.spectral.scalar hμ
  obtain ⟨uf, hrep⟩ := Prop025OMain.periodicRep u
  have hh : 0 < eta0 L κ + 1 :=
    (Prop017Quantum.eta0_pos hκ).trans (height_gt κ)
  obtain ⟨δ, d0, hδ, hd0, l0, hin⟩ :=
    RootSpectralInputsDischarge.rootSpectralInputs hκ hu hrep hμ hmom hh
  obtain ⟨hη0, hρ0, hηt, hρt, hemp, Cp, Dp, Cb, Ck, hCp, hDp, hCb, hCk, M0, hcore⟩ :=
    core_at_packet hκ Prop021Input WindowInput M.chart.chart M.chart.sobolev
      (higher M.dynamics.hierarchy) u hu hμ (height_gt κ) hδ hd0 hin d hd R hR T' hT' I Θ hΘ k hk
  have hL : 0 < L := Fact.out
  obtain ⟨A, hA, hmain⟩ := main_of_total d hd (3 * Real.pi / L) Cp Dp Cb Ck
    (by positivity) hCp hDp hCb hCk
  refine ⟨zeta_tendsto _ _ hηt hρt, ?_, A, hA, M0, fun N hN hk' ψ hψ => ?_⟩
  · intro hI N
    obtain ⟨hη, hρ⟩ := hemp hI N
    unfold fixedZeta fixedErrors
    rw [hη, hρ]
    exact zeta_empty
  · unfold boxError
    refine iSup_le fun t => iSup_le fun θ => ?_
    have hc := hcore (N + 1) (by omega) hk' ψ hψ t.val (hbox t.val t.property) θ.val θ.property
    rw [Prop025OUnit.unitary_eq] at hc
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
    obtain ⟨hc1, hc2, -⟩ := cut_bounds (θ := alpha d) hL (N + 1)
    unfold preparationError fixedZeta fixedErrors
    exact hmain ((N + 1 : ℕ) : ℝ) hN1 _ hc1 hc2 _ _ _ _ (hη0 _) (hρ0 _) le_rfl

private theorem zero_rank_at_packet (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (R : Finset ℕ)
    (Θ : ℤ → ℝ) (T : ℕ → ℝ) (ζ : ℕ → ℝ) :
    EstimateWithZeta hκ C F u I R 0 Θ T 0 ζ := by
  refine ⟨0, fun N _ hk ψ hψ => ?_⟩
  unfold boxError
  refine iSup_le fun t => iSup_le fun θ => ?_
  have hn : ‖((ActualModelQuantumR52a.chargeUnitary hκ R t.val N
      (ActualModelQuantumR52a.countUnitary hκ I θ.val N ψ) :
        BetheCoefficientTransform.HN L (N + 1)) :
        TensorCarrier.HilbertTensorPower ℂ (PhysicalTensor.L2T L) (N + 1))‖ = 1 :=
    ((ActualModelQuantumR52a.chargeUnitary hκ R t.val N).norm_map
      (ActualModelQuantumR52a.countUnitary hκ I θ.val N ψ)).trans
        (((ActualModelQuantumR52a.countUnitary hκ I θ.val N).norm_map ψ).trans hψ)
  rw [Prop025OUnit.rank_zero_marginal (N + 1) hk _ hn, sub_self, Fidelity.traceNorm_zero]
  exact bot_le

/-- PROP-025 at its DEF-044 interface, with the fixed-packet witness shared
across the charge set, marginal rank, and both boxes. -/
def PROP025WithPacket (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ),
    let ζ := fixedZeta hκ u hu I
    Tendsto ζ atTop (𝓝 0) ∧ (I = ∅ → ∀ N, ζ N = 0) ∧
      ∀ (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
        (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
        ∃ A : ℝ, 0 ≤ A ∧ EstimateWithZeta hκ M.chart.chart (higher M.dynamics.hierarchy)
          u I R k Θ T A ζ

/-- Conditional strengthened PROP-025, using the same physical inputs
as frozen OMain and OLow. -/
theorem prop025_intermediate (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ) :
    PROP025WithPacket (L := L) hκ := by
  intro u hu M I
  have hReference := higher_at_packet hκ Prop021Input WindowInput u hu M I ∅ 1
    (fun _ => 0) (fun _ => 0) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (by simp) le_rfl
  refine ⟨hReference.1, hReference.2.1, fun R k Θ T hΘ hT => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, le_rfl, zero_rank_at_packet hκ _ _ u I R Θ T _⟩
  let Rh := R.filter (fun r => 2 ≤ r)
  have hTh : ∀ r ∈ Rh, 0 ≤ T r := fun r hr => hT r (Finset.mem_filter.1 hr).1
  have hRh : ∀ r ∈ Rh, 2 ≤ r := fun _ hr => (Finset.mem_filter.1 hr).2
  obtain ⟨A, hA, N₀, hest⟩ :=
    (higher_at_packet hκ Prop021Input WindowInput u hu M I Rh k Θ T hΘ hTh hRh hk).2.2
  refine ⟨A, hA, N₀, fun N hN hkN ψ hψ => ?_⟩
  have h := hest N hN hkN ψ hψ
  change boxError hκ _ _ u I (R.filter (fun r => 2 ≤ r)) Θ T k N hkN ψ ≤ _ at h
  rw [← Prop025OLow.d_low R] at h
  refine le_trans ?_ h
  unfold boxError
  refine iSup_le fun t => iSup_le fun θ => ?_
  refine (Prop025OLow.box_low hκ _ _ u I R k N hkN ψ t.val θ.val).trans ?_
  exact le_iSup₂_of_le (f := fun (t' : {t : ℕ → ℝ // ∀ r ∈ Rh, |t r| ≤ T r})
      (θ' : {θ : ℤ → ℝ // ∀ n ∈ I, |θ n| ≤ Θ n}) =>
      TraceClass.traceNorm (PhysicalTensor.reducedDensityN (N + 1) k hkN
        (ActualModelQuantumR52a.chargeUnitary hκ Rh t'.val N
          (ActualModelQuantumR52a.countUnitary hκ I θ'.val N ψ) :
            TensorCarrier.HilbertTensorPower ℂ (PhysicalTensor.L2T L) (N + 1)) -
        Prop025OInputs.tensorProj k (target M.chart.chart (higher M.dynamics.hierarchy) I Rh θ'.val t'.val u)))
    ⟨t.val, fun r hr => t.property r (Finset.mem_filter.1 hr).1⟩ θ le_rfl

/-- The frozen R56a consumer follows by instantiating the boxes. -/
theorem to_PROP025Input (hκ : 0 < κ) (h : PROP025WithPacket (L := L) hκ) :
    ActualModelCorollaryR56a.PROP025Input (L := L) hκ := by
  intro u hu M I R k Θ T hΘ hT
  obtain ⟨hlim, hempty, hbox⟩ := h u hu M I
  obtain ⟨A, hA, hest⟩ := hbox R k Θ T hΘ hT
  exact ⟨A, hA, fixedZeta hκ u hu I, hlim, hempty, hest⟩

/-- The earlier R53a angle-box consumer also follows. -/
theorem to_R53a_PROP025Input (hκ : 0 < κ) (h : PROP025WithPacket (L := L) hκ) :
    ActualModelCorollaryR53a.PROP025Input (L := L) hκ := by
  intro u hu M I Θ hΘ
  obtain ⟨hlim, hempty, hbox⟩ := h u hu M I
  exact ⟨fixedZeta hκ u hu I, hlim, hempty, fun R k T hT => hbox R k Θ T hΘ hT⟩

end QuantumNLS.Prop025ProvenanceR59a
