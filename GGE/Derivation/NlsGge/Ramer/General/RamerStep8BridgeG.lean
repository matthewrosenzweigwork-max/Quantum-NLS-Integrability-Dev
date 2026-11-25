import Mathlib
import NlsGge.Ramer.General.RamerStep8cG
import NlsGge.Ramer.General.RamerJacobianHeadG

/-!
# Bridge: Step 8's divergence and `S.ramerJac`, generalized (GD10)

Adapted from `NlsGge/Ramer/RamerStep8Bridge.lean`.  Dictionary: `c, s, hs ↦ S`,
`ramerDiv ↦ S.ramerDiv`, `ramerJac ↦ S.ramerJac`, `ramerJE ↦ S.ramerJE`,
`inclE ↦ S.incl`, `fullWeightSequenceGaussian c.val ↦ S.γ`,
`fullWeightedSequenceGaussian c s ↦ S.γE`.

* `Gen.ae_eq_of_subseq_ae_of_tendstoInMeasure`: an a.e. limit along a subsequence agrees a.e.
  with the limit in measure of the whole sequence.
* `S.step8_delta_ae_eq_ramerDiv`: any such `δL` equals `S.ramerDiv L` `γ`-a.e.
* `S.ramerJE_ae_eq_of_ae_eq`: a.e.-equal divergences give `γ_E`-a.e.-equal Jacobians.
* `S.step8c_ramerJac`: `step8c` restated for `S.ramerJac L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

/-- A subsequence a.e. limit coincides a.e. with the in-measure limit of the full sequence.
(Old: `NlsGge.Ramer.ae_eq_of_subseq_ae_of_tendstoInMeasure`.) -/
theorem ae_eq_of_subseq_ae_of_tendstoInMeasure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g h : α → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun j => f (φ j) x) atTop (𝓝 (g x)))
    (hmeas : TendstoInMeasure μ f atTop h) :
    g =ᵐ[μ] h := by
  have hsub : TendstoInMeasure μ (fun j => f (φ j)) atTop h :=
    hmeas.comp hφ.tendsto_atTop
  obtain ⟨ns, hns, hns_ae⟩ := hsub.exists_seq_tendsto_ae
  filter_upwards [hae, hns_ae] with x hx1 hx2
  exact tendsto_nhds_unique (hx1.comp hns.tendsto_atTop) hx2

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- **Bridge 1.** The Step-8 divergence (any a.e. subsequence limit of `S.ramerA · L`) is
`S.ramerDiv L` almost surely. (Old: `step8_delta_ae_eq_ramerDiv`.) -/
theorem step8_delta_ae_eq_ramerDiv
    (L : S.E → S.H) (hL : ContDiff ℝ 2 L)
    (δL : (ℤ → ℂ) → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ᵐ z ∂S.γ,
      Tendsto (fun j => S.ramerA (φ j) L z) atTop (𝓝 (δL z))) :
    δL =ᵐ[S.γ] S.ramerDiv L :=
  NlsGge.Ramer.Gen.ae_eq_of_subseq_ae_of_tendstoInMeasure
    (f := fun n => S.ramerA n L) (g := δL) (h := S.ramerDiv L)
    hφ hlim (S.ramerDiv_spec L hL).2.2

/-- A.e.-equal divergences give `γ_E`-a.e.-equal Jacobians. (Old: `ramerJE_ae_eq_of_ae_eq`.) -/
theorem ramerJE_ae_eq_of_ae_eq
    (L : S.E → S.H) {δ δ' : (ℤ → ℂ) → ℝ}
    (h : δ =ᵐ[S.γ] δ') :
    S.ramerJE L δ =ᵐ[S.γE] S.ramerJE L δ' := by
  filter_upwards [S.ae_of_ae_coordE h] with x hx
  rw [S.ramerJE_eq, S.ramerJE_eq, hx]

/-- **Bridge 2.** Ramer's Step 8 conclusions (positivity, (**) for sets, and null-set
preservation), stated for `S.ramerJac L`. (Old: `step8c_ramerJac`.) -/
theorem step8c_ramerJac (L : S.E → S.H)
    {ε : ℝ} (hyp : S.Step8Hyp L ε) :
    (∀ᵐ x ∂S.γE, x ∈ closedBall (0 : S.E) ε → 0 < S.ramerJac L x) ∧
      (∀ M : Set S.E, M ⊆ ball (0 : S.E) (ε / 2) →
        ∫⁻ x in closedBall (0 : S.E) ε ∩ (fun y => y + S.incl (L y)) ⁻¹' M,
          ENNReal.ofReal (S.ramerJac L x) ∂S.γE ≤ S.γE M) ∧
      (∀ M : Set S.E, MeasurableSet M → M ⊆ ball (0 : S.E) (ε / 2) →
        S.γE M = 0 →
        S.γE (closedBall (0 : S.E) ε ∩ (fun y => y + S.incl (L y)) ⁻¹' M) = 0) := by
  obtain ⟨δL, hm, ⟨φ, hφ, hlim⟩, -⟩ := S.step8b_divergence L hyp
  have hEq : S.ramerJE L δL =ᵐ[S.γE] S.ramerJac L :=
    S.ramerJE_ae_eq_of_ae_eq L (S.step8_delta_ae_eq_ramerDiv L hyp.smooth δL φ hφ hlim)
  refine ⟨?_, ?_, fun M hMm hM h0 => S.step8c_null L hyp δL hm φ hφ hlim hMm hM h0⟩
  · filter_upwards [hEq] with x hx hxB
    rw [← hx]
    exact S.ramerJE_pos_closedBall L hyp δL hxB
  · intro M hM
    calc ∫⁻ x in closedBall (0 : S.E) ε ∩ (fun y => y + S.incl (L y)) ⁻¹' M,
          ENNReal.ofReal (S.ramerJac L x) ∂S.γE
        = ∫⁻ x in closedBall (0 : S.E) ε ∩ (fun y => y + S.incl (L y)) ⁻¹' M,
          ENNReal.ofReal (S.ramerJE L δL x) ∂S.γE :=
          lintegral_congr_ae (ae_restrict_of_ae (hEq.mono fun x hx => by dsimp only; rw [hx]))
      _ ≤ _ := S.step8c_set L hyp δL hm φ hφ hlim hM

end NlsGge.Ramer.General.RamerSetting
