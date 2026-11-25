import QuantumNLS.Prop025OUnit
import QuantumNLS.Prop025OAffine
import QuantumNLS.ActualModelCorollaryR56a
import QuantumNLS.RootSpectralInputsDischarge
import QuantumNLS.Fidelity

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O6a:
**the headline estimate eq:MP-main for every charge family of orders `≥ 2` and every marginal rank** (source lines
68-100 and 664-710), in the PRINTED quantifier order and in the shape of the consumer
`ActualModelCorollaryR53a.MainEstimate`.

Fix `L, κ > 0`, a smooth unit profile `u`, the DEF-044 interface `M : Def044BindingR26m.MixedInterface` (its chart, its
Sobolev restrictions, its spectral requirements and its hierarchy), finite `I`, `R ⊆ {2,3,…}`, a marginal rank `k`
and the boxes `|t_r| ≤ T_r`, `|θ_n| ≤ Θ_n`; THEN there are `C`, `ζ_{I,N} → 0` (`ζ ≡ 0` for empty `I`) and a threshold,
uniformly in the times, angles and normalized preparations `Ψ_N` (`N+1` particles in the R53a convention):
`sup_{t,θ} ‖γ^{(k)}_{U_N(t)V_N(θ)Ψ_N} − |Φ_t(Φ_I(θ)u)^{⊗k}⟩⟨·|‖₁ ≤ 2e_N + Cζ_{I,N} + C N^{−1/[224(d+1)]}`.

* `evenMoments`, `periodicRep`: the spectral inputs of the frozen O3f/O4b/O5a stages from DEF-044 clause (1)
  (`RootSpectralInputsDischarge.rootSpectralInputs`, the absolute moments of the DEF-044 scalar measure);
* `core`: the total-error bracket eq:MP-total-error, at every particle number `M ≥ M₀` with `k ≤ M`, from O3f
  `quantum_comparison`, O5a `affine_propagation` (named `Prop021Input`), O5b `classical_target` (named `WindowInput`),
  O4b `factorial_bound`, O4a `coh_inv`, O4d `coh_field` and the projector bound;
* **`main_hi`**: `MainEstimate` for `R ⊆ {2,3,…}` and EVERY rank `k` (`k = 0` by `rank_zero_marginal`: both the
  `0`-marginal and the `0`-fold projector are the scalar `1`), with `ζ = √η^I + ρ^I` (`Prop025OFinal.zeta`) and the O2
  `main_of_total` (designated cut, `c = 3π/L`).
The route does not use eq:MP-frequency or the higher frequency-derivative estimates (O4c/O4d replace them).
No hypothesis is added beyond the named inputs; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal InnerProductSpace
open MeasureTheory Filter Set

namespace QuantumNLS.Prop025OMain
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheSpectralCharges (evolution)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure IsPeriodicRepresentative)
open QuantumNLS.TensorCarrier (HilbertTensorPower htpow reducedDensityPower SymSector)
open QuantumNLS.TraceClass (traceNorm traceNorm_add_le)
open QuantumNLS.Prop025OTarget (enum sum_enum classical_target)
open QuantumNLS.Prop025OUnit (cproj cproj_nonneg tensorProj_sub_le norm_traj rdN_add unitary_eq rank_zero_marginal)
open QuantumNLS.Prop025OPhase (mixedEv LmixOp quantum_comparison)
open QuantumNLS.Prop025OAffine (affine_propagation)
open QuantumNLS.Prop025OFact (factorial_bound)
open QuantumNLS.Prop025OKer (mixK mixD coh_inv mixK_selfAdjoint)
open QuantumNLS.Prop025OFinal (etaG W Delta totalBracket zeta main_of_total zeta_tendsto)
open QuantumNLS.Prop025OParams (alpha alpha_pos)
open QuantumNLS.PROP018Probability (cutN cutIdx cut_bounds)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.Prop017Quantum (eta0)
open QuantumNLS.MPContour (nu zθ uθ continuous_zθ continuous_uθ)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.SymplecticBracket (hamField)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.ActualModelTargetR53a (HigherFlows higher target)
open QuantumNLS.ActualModelCorollaryR53a (MainEstimate boxError preparationError EstimateWithZeta)
open QuantumNLS.Prop022PositiveDataR126 (positiveExtension)
open QuantumNLS.Prop022ActualProfileR117 (velocity)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. The spectral inputs from DEF-044 clause (1) -/

/-- The even moments of the limiting rapidity measure, from the absolute moments of the DEF-044 scalar measure. -/
theorem evenMoments (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (S : Def044D1SpectralR51a.ScalarRequirements hκ u hu) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) :
    RootSpectralInputsDischarge.EvenMoments (μ : Measure ℝ) := by
  intro p
  rw [RootSpectralInputsDischarge.measure_eq_limit hκ hu hμ, ← S.physical_measure]
  refine (S.absolute_moments (2 * p)).congr (Eventually.of_forall fun x => ?_)
  show |x| ^ (2 * p) = x ^ (2 * p)
  rw [pow_mul, pow_mul, sq_abs]

/-- A smooth profile has a continuous periodic representative. -/
theorem periodicRep (u : Smooth L) : ∃ uf : ℝ → ℂ, IsPeriodicRepresentative L (physical u) uf := by
  let g := WeakDerivatives.liftC u.property.smooth.continuous u.property.periodic
  refine ⟨fun x => g (x : AddCircle L), g.continuous.comp continuous_quotient_mk', fun x => ?_, ?_⟩
  · show g ((x + L : ℝ) : AddCircle L) = g (x : AddCircle L)
    rw [AddCircle.coe_add_period]
  · filter_upwards [PhysicalProductPreparation.smoothClass_ae u.property] with y hy
    refine hy.trans ?_
    show g y = g ((AddCircle.equivIco L 0 y : ℝ) : AddCircle L)
    rw [AddCircle.coe_equivIco]

/-- Three-term triangle inequality for the trace norm. -/
theorem tri3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B C D : E →L[ℂ] E) :
    traceNorm (A - D) ≤ traceNorm (A - B) + traceNorm (B - C) + traceNorm (C - D) := by
  have e : A - D = (A - B) + (B - C) + (C - D) := by abel
  rw [e]
  have h1 := traceNorm_add_le (A - B + (B - C)) (C - D)
  have h2 := traceNorm_add_le (A - B) (B - C)
  exact h1.trans (by gcongr)

/-! ### 2. The total-error bracket -/

theorem ofReal_add3_le {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z ≤ w) :
    ENNReal.ofReal x + ENNReal.ofReal y + ENNReal.ofReal z ≤ ENNReal.ofReal w := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add (add_nonneg hx hy) hz]
  exact ENNReal.ofReal_le_ofReal h

theorem final_arith {e C1 C2 cw B p w b6 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hcw : 0 ≤ cw) (hB : 0 ≤ B)
    (hpw : 0 ≤ p * w) (h6 : 0 ≤ b6) :
    2 * e + C1 * B + C2 * p * w + cw * b6 ≤ 2 * e + (C1 + C2 + cw) * (B + p * w + b6) := by
  nlinarith [mul_nonneg hC1 hpw, mul_nonneg hC1 h6, mul_nonneg hC2 hB, mul_nonneg hC2 h6,
    mul_nonneg hcw hB, mul_nonneg hcw hpw]

set_option maxHeartbeats 64000000 in
/-- **eq:MP-total-error** at every large particle number, uniformly in the boxes and the normalized preparation. -/
theorem core (hκ : 0 < κ) (H21 : Prop025OInputs.Prop021Input (L := L))
    (HW : Prop025OInputs.WindowInput (L := L) hκ)
    (C : Def021ChartR41b.Chart L κ hκ) (hsob : Def044ChartR51a.SobolevRestrictions hκ C) (F : HigherFlows L κ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ (physical u) hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d) (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r)
    (I : Finset ℤ) (Θ : ℤ → ℝ) (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (k : ℕ) (hk : 1 ≤ k) :
    ∃ ηI ρI : ℕ → ℝ, (∀ N, 0 ≤ ηI N) ∧ (∀ N, 0 ≤ ρI N) ∧ Tendsto ηI atTop (𝓝 0) ∧
      Tendsto ρI atTop (𝓝 0) ∧ (I = ∅ → ∀ N, ηI N = 0 ∧ ρI N = 0) ∧
      ∃ Cp Dp Cb Ck : ℝ, 0 ≤ Cp ∧ 0 ≤ Dp ∧ 0 ≤ Cb ∧ 0 ≤ Ck ∧
      ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ hkM : k ≤ M, ∀ Ψ : HN L M, ‖Ψ‖ = 1 →
        ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) → ∀ θ : ℤ → ℝ, (∀ n ∈ I, |θ n| ≤ Θ n) →
          traceNorm (PhysicalTensor.reducedDensityN M k hkM
              ((evolution (physBasis L hκ M) (mixedEv L κ R t (enum I) (fun i => θ (enum I i)) M) 1 Ψ :
                HN L M) : HilbertTensorPower ℂ (L2T L) M) -
            Prop025OInputs.tensorProj k (target C F I R θ t u)) ≤
          ENNReal.ofReal (2 * ‖Ψ - wvec M (physical u)‖ +
            Ck * totalBracket d Cp Dp Cb (M : ℝ) (cutN L (alpha d) M) (ηI M) (ρI M)) := by
  have hL : 0 < L := Fact.out
  have hh : 0 < h := lt_trans (Prop017Quantum.eta0_pos hκ) hηh
  have hords : R ⊆ Finset.range (d + 1) := fun r hr => Finset.mem_range.2 (by have := (hR r hr).2; omega)
  have hn_mem : ∀ i, enum I i ∈ I := fun i => (I.equivFin.symm i).2
  have hΘf0 : ∀ i, 0 ≤ Θ (enum I i) := fun i => hΘ _ (hn_mem i)
  obtain ⟨ηI, ρI, hη0, hρ0, hηt, hρt, hemp, Cp, Dp, Cb, C1, hCp, hDp, hCb, hC1, hev1⟩ :=
    quantum_comparison hκ (physical u) hu hμ hηh hδ hd0 hin d k hd R hords T (enum I) (fun i => Θ (enum I i)) hΘf0
  obtain ⟨C2, hC2, hev2⟩ := affine_propagation H21 hκ (physical u) hu hμ hηh hδ hd0 hin d hd R hords T
    (enum I) (fun i => Θ (enum I i)) k hk
  obtain ⟨Cf, hCf, hev3⟩ := factorial_bound hκ (physical u) hu hμ hηh hδ hd0 hin d hd R hords T
    (enum I) (fun i => Θ (enum I i))
  have hμm : PhysicalQuantumMeasure.measure hκ (physical u) = (μ : Measure ℝ) :=
    (RootSpectralInputsDischarge.measure_eq_limit hκ hu hμ).symm
  obtain ⟨Cw, hCw, l1, hct⟩ := classical_target hκ HW C hsob F u (μ : Measure ℝ) hμm hh d hd R hR T hT I Θ
  obtain ⟨⟨dl, CL, hdl, hCL, Φloc, Ψloc, hloc⟩, hglob⟩ := RF535Final.global_actual_chart L
  have hG := hglob dl CL Φloc Ψloc hdl hCL hloc κ hκ
  -- thresholds
  have hpow : Tendsto (fun M : ℕ => ((M : ℝ) ^ alpha d)) atTop atTop :=
    (tendsto_rpow_atTop (alpha_pos d)).comp tendsto_natCast_atTop_atTop
  have hidx : ∀ᶠ M : ℕ in atTop, l1 ≤ cutIdx L (alpha d) M := by
    have h1 := (hpow.const_mul_atTop (div_pos hL Real.pi_pos)).eventually_ge_atTop (l1 : ℝ)
    filter_upwards [h1] with M hM
    have h2 := (cut_bounds (θ := alpha d) hL M).2.2
    have h3 : (l1 : ℝ) ≤ cutIdx L (alpha d) M := by
      calc (l1 : ℝ) ≤ L / Real.pi * (M : ℝ) ^ alpha d := hM
        _ = L * (M : ℝ) ^ alpha d / Real.pi := by ring
        _ ≤ _ := h2
    exact_mod_cast h3
  have hcutT : Tendsto (fun M : ℕ => cutN L (alpha d) M) atTop atTop :=
    tendsto_atTop_mono (fun M => (cut_bounds (θ := alpha d) hL M).1) (hpow.const_mul_atTop two_pos)
  have hsmall : ∀ᶠ M : ℕ in atTop, Cw * (cutN L (alpha d) M) ^ (-(1/4 : ℝ)) ≤ 1 := by
    have h1 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp hcutT).const_mul Cw
    rw [mul_zero] at h1
    exact h1.eventually (Iic_mem_nhds one_pos)
  obtain ⟨q1, hq1⟩ := eventually_atTop.1 hev1
  obtain ⟨q2, hq2⟩ := eventually_atTop.1 hev2
  obtain ⟨M1, hM1⟩ := eventually_atTop.1 (hidx.and (hsmall.and hev3))
  set Ck : ℝ := C1 + C2 + cproj k * Cw with hCkdef
  have hcw : 0 ≤ cproj k * Cw := mul_nonneg (cproj_nonneg k) hCw
  refine ⟨ηI, ρI, hη0, hρ0, hηt, hρt, fun hI N => hemp (by simp [hI]) N, Cp, Dp, Cb, Ck, hCp, hDp, hCb,
    by positivity, max M1 (k + max q1 q2), fun M hM hkM Ψ hΨ t ht θ hθ => ?_⟩
  obtain ⟨hidxM, hsmM, hfM⟩ := hM1 M ((le_max_left _ _).trans hM)
  obtain ⟨q, rfl⟩ : ∃ q, M = k + q := ⟨M - k, by omega⟩
  have hq : max q1 q2 ≤ q := by have := (le_max_right M1 (k + max q1 q2)).trans hM; omega
  rw [rdN_add]
  have hθf : ∀ i, |θ (enum I i)| ≤ Θ (enum I i) := fun i => hθ _ (hn_mem i)
  have hQ := hq1 q ((le_max_left _ _).trans hq) Ψ hΨ t ht (fun i => θ (enum I i)) hθf
  obtain ⟨γ, hγ0, hγ, hA⟩ := hq2 q ((le_max_right _ _).trans hq) t ht (fun i => θ (enum I i)) hθf
  obtain ⟨hcont, hw, him, hfac⟩ := hfM t ht (fun i => θ (enum I i)) hθf
  -- the frozen coherent energy: torus invariant, differentiable, with the Hartree field
  have ha0 : 0 ≤ cutN L (alpha d) (k + q) :=
    le_trans (by positivity) (cut_bounds (θ := alpha d) hL (k + q)).1
  have hW0 : 0 ≤ W d (cutN L (alpha d) (k + q)) := by unfold W; positivity
  have hMc0 : 0 ≤ (nu (6 + I.card * 6)).real univ * Cf * 2 * Real.exp (L * h) *
      W d (cutN L (alpha d) (k + q)) := by
    have := (measureReal_nonneg : 0 ≤ (nu (6 + I.card * 6)).real univ)
    positivity
  have hsK : ∀ j, (mixK (L := L) hκ (physical u) (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) R t (enum I)
      (fun i => θ (enum I i)) j).adjoint = mixK (L := L) hκ (physical u) (μ : Measure ℝ) h
        (cutN L (alpha d) (k + q)) R t (enum I) (fun i => θ (enum I i)) j :=
    fun j => mixK_selfAdjoint hκ (physical u) _ h _ R t (enum I) _ j
  have hfield := fun v => Prop025OPhys.coh_field
    (mixK (L := L) hκ (physical u) (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) R t (enum I)
      (fun i => θ (enum I i))) hMc0 (by positivity : (0 : ℝ) ≤ κ * L) hfac hsK v
  have hFd : Differentiable ℝ (R52CFHartree.coh (mixK (L := L) hκ (physical u) (μ : Measure ℝ) h
      (cutN L (alpha d) (k + q)) R t (enum I) (fun i => θ (enum I i)))) := fun v => (hfield v).1
  have hFinv : ∀ (ψ : QuantumNLS.Ext025B6TorusCoordinates.Torus) (v : L2T L),
      R52CFHartree.coh (mixK (L := L) hκ (physical u) (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) R t
        (enum I) (fun i => θ (enum I i))) (RF535Final.Tact (L := L) hκ ψ v) =
      R52CFHartree.coh (mixK (L := L) hκ (physical u) (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) R t
        (enum I) (fun i => θ (enum I i))) v :=
    coh_inv hκ hG _ _ ((continuous_uθ κ _).mul hcont) (continuous_zθ _) him hw
  have hγ' : ∀ τ, HasDerivAt γ (hamField (R52CFHartree.coh (mixK (L := L) hκ (physical u) (μ : Measure ℝ) h
      (cutN L (alpha d) (k + q)) R t (enum I) (fun i => θ (enum I i)))) (γ τ)) τ := fun τ => by
    rw [(hfield (γ τ)).2]; exact hγ τ
  -- the classical target
  have hcl := hct (cutIdx L (alpha d) (k + q)) hidxM t ht θ hθ hFinv hFd γ hγ0 hγ'
  have hγ1 : ‖γ 1‖ = 1 := norm_traj hκ hG hFinv hFd hu γ hγ0 hγ' 1
  have hcl' : ‖γ 1 - target C F I R θ t u‖ ≤ 1 := hcl.trans hsmM
  have htgt : ‖target C F I R θ t u‖ ≤ 2 := by
    have := norm_sub_le (γ 1) (γ 1 - target C F I R θ t u)
    rw [sub_sub_cancel] at this
    linarith
  have hP := tensorProj_sub_le k (γ 1) (target C F I R θ t u) (by rw [hγ1]; norm_num) htgt
  have hP' : traceNorm (Prop025OInputs.tensorProj k (γ 1) - Prop025OInputs.tensorProj k (target C F I R θ t u)) ≤
      ENNReal.ofReal (cproj k * Cw * (cutN L (alpha d) (k + q)) ^ (-(1/4 : ℝ))) := by
    refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcl (cproj_nonneg k)
  refine (tri3 _ _ _ _).trans ((add_le_add (add_le_add hQ hA) hP').trans ?_)
  -- arithmetic
  set N : ℝ := ((k + q : ℕ) : ℝ) with hNdef
  set a : ℝ := cutN L (alpha d) (k + q) with hadef
  have hN0 : 0 < N := by rw [hNdef]; exact_mod_cast (show 0 < k + q by omega)
  have hD0 : 0 ≤ Delta d N := by unfold Delta; positivity
  have hρq := hρ0 (k + q)
  have hB1 : 0 ≤ Real.sqrt (ηI (k + q) + etaG d Cp Dp Cb N a) + ρI (k + q) + W d a / N + W d a * Delta d N := by
    positivity
  have hB2 : 0 ≤ N ^ (-(1/4 : ℝ)) * W d a ^ 7 := by positivity
  have hB3 : 0 ≤ a ^ (-(1/4 : ℝ)) := Real.rpow_nonneg ha0 _
  have hE0 : 0 ≤ 2 * ‖Ψ - wvec (k + q) (physical u)‖ := by positivity
  have hcp := cproj_nonneg k
  refine ofReal_add3_le (by positivity) (by positivity) (by positivity) ?_
  unfold totalBracket
  rw [hCkdef]
  exact final_arith hC1 hC2 hcw hB1 hB2 hB3

/-! ### 3. The headline for charge orders `≥ 2`, every rank -/

/-- **Rank zero** (every finite order set): both the `0`-marginal and the `0`-fold projector are the scalar `1`. -/
theorem rank_zero (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (F : HigherFlows L κ) (u : Smooth L)
    (I : Finset ℤ) (R : Finset ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ) :
    MainEstimate hκ C F u I R 0 Θ T := by
  refine ⟨0, le_rfl, fun _ => 0, tendsto_const_nhds, fun _ _ => rfl, 0, fun N _ hk ψ hψ => ?_⟩
  unfold boxError
  refine iSup_le fun t => iSup_le fun θ => ?_
  have hn : ‖((ActualModelQuantumR52a.chargeUnitary hκ R t.val N
      (ActualModelQuantumR52a.countUnitary hκ I θ.val N ψ) : HN L (N + 1)) :
        HilbertTensorPower ℂ (L2T L) (N + 1))‖ = 1 := by
    have h1 := (ActualModelQuantumR52a.chargeUnitary hκ R t.val N).norm_map
      (ActualModelQuantumR52a.countUnitary hκ I θ.val N ψ)
    have h2 := (ActualModelQuantumR52a.countUnitary hκ I θ.val N).norm_map ψ
    exact h1.trans (h2.trans hψ)
  rw [rank_zero_marginal (N + 1) hk _ hn, sub_self, Fidelity.traceNorm_zero]
  exact bot_le

/-- **eq:MP-main (orders `≥ 2`, every rank `k`)**, as `MainEstimate`, in the printed quantifier order. -/
theorem main_hi (hκ : 0 < κ) (H21 : Prop025OInputs.Prop021Input (L := L))
    (HW : Prop025OInputs.WindowInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) (hR2 : ∀ r ∈ R, 2 ≤ r) :
    MainEstimate hκ M.chart.chart (higher M.dynamics.hierarchy) u I R k Θ T := by
  have hL : 0 < L := Fact.out
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact rank_zero hκ _ _ u I R Θ T
  set d : ℕ := max 2 (R.sup id) with hd_def
  have hd : 2 ≤ d := le_max_left _ _
  have hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d := fun r hr =>
    ⟨hR2 r hr, (Finset.le_sup (f := id) hr).trans (le_max_right _ _)⟩
  set T' : ℕ → ℝ := fun r => if r ∈ R then T r else 0 with hT'def
  have hT' : ∀ r, 0 ≤ T' r := fun r => by
    rw [hT'def]; dsimp only; split_ifs with h
    · exact hT r h
    · exact le_rfl
  have hbox : ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) → ∀ r ∈ R, |t r| ≤ T' r := fun t ht r hr => by
    rw [hT'def]; dsimp only; rw [if_pos hr]; exact ht r hr
  have hμ := FreeLimit.muKappa_spec (physical u) hu hκ
  have hmom := evenMoments hκ (physical u) hu M.spectral.scalar hμ
  obtain ⟨uf, hrep⟩ := periodicRep u
  have hηh : eta0 L κ < eta0 L κ + 1 := by linarith
  have hh : 0 < eta0 L κ + 1 := by linarith [Prop017Quantum.eta0_pos (L := L) hκ]
  obtain ⟨δ, d0, hδ, hd0, l0, hin⟩ := RootSpectralInputsDischarge.rootSpectralInputs hκ hu hrep hμ hmom hh
  obtain ⟨ηI, ρI, hη0, hρ0, hηt, hρt, hemp, Cp, Dp, Cb, Ck, hCp, hDp, hCb, hCk, M0, hcore⟩ :=
    core hκ H21 HW M.chart.chart M.chart.sobolev (higher M.dynamics.hierarchy) u hu hμ hηh hδ hd0 hin
      d hd R hR T' hT' I Θ hΘ k hk
  obtain ⟨A, hA, hmain⟩ := main_of_total d hd (3 * Real.pi / L) Cp Dp Cb Ck (by positivity) hCp hDp hCb hCk
  refine ⟨A, hA, fun N => zeta (ηI N) (ρI N), zeta_tendsto ηI ρI hηt hρt, fun hI N => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hemp hI N
    show zeta (ηI N) (ρI N) = 0
    rw [h1, h2]
    exact Prop025OFinal.zeta_empty
  · refine ⟨M0, fun N hN hk' ψ hψ => ?_⟩
    unfold boxError
    refine iSup_le fun t => iSup_le fun θ => ?_
    have hc := hcore (N + 1) (by omega) hk' ψ hψ t.val (hbox t.val t.property) θ.val θ.property
    rw [unitary_eq] at hc
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
    obtain ⟨hc1, hc2, -⟩ := cut_bounds (θ := alpha d) hL (N + 1)
    have hB := hmain ((N + 1 : ℕ) : ℝ) hN1 _ hc1 hc2 _ (‖ψ - wvec (N + 1) (physical u)‖) (ηI (N + 1))
      (ρI (N + 1)) (hη0 _) (hρ0 _) le_rfl
    unfold preparationError
    exact hB

end QuantumNLS.Prop025OMain

#print axioms QuantumNLS.Prop025OMain.evenMoments
#print axioms QuantumNLS.Prop025OMain.periodicRep
#print axioms QuantumNLS.Prop025OMain.core
#print axioms QuantumNLS.Prop025OMain.rank_zero
#print axioms QuantumNLS.Prop025OMain.main_hi
-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OMain." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
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
  Lean.logInfo m!"Prop025OMain aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
