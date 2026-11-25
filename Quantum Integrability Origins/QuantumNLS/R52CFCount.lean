import QuantumNLS.Prop010SingleContourR17
import QuantumNLS.RootProductSymbolAnalytic

/-!
# R-52CF5DA1 stage 10a: the count reconstruction holds uniformly on a neighborhood of the rough center

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraphs "Use the resulting joint quantum
spectral projection `P_N` and the same bounded cutoff contour operators `C^{(0)}_{N,n}`, `C^{(1)}_{N,n}` ... These
operators and `P_N` depend on `u_*`, not on the nearby tested profile. ... By continuity of the transfer ... a fixed
open neighborhood of `u_*` gives a common positive probe margin ... B4's centered moments depend only on kernel rank
sums and are uniform over unit product vectors. Markov's inequality at the finite probes consequently gives ...
extends the intensive reconstruction bound to `v^{⊗N}`, uniformly with error `C_* N^{-2}`."

For a unit rough center `u`, a label `n`, a rectangle height `h > 0` and cutoff extensions `f, g` with the printed
agreement on the tube of radius `r` around `s_u` (the hypotheses of the accepted PROP-010 norm clause), the operator
`B_{N,n} - C_{N,n}` built from `u` (the actual normalized count minus the two-term contour operator) satisfies, with
ONE constant and ONE threshold, `‖(B_{N,n} - C_{N,n}) v^{⊗N}‖ ≤ D N^{-2}` for EVERY unit `v` in a neighborhood of `u`
(`count_near`).  The probe set, probe margin and two-term scalar reconstruction are those of the accepted
`cutoff_probes` at the concrete band carrier `Prop026Bound.scalarCuts` (D1-regular separators `b_j(u)`); the probe
margin `ε` at `u` becomes `ε/2` at `v` by continuity of `v ↦ s(z_j; v)`; the Markov step is the accepted
`CondensateLocalizationR10.physical_error_rate` at `v` (eighth moments uniform over unit product vectors).
No hypothesis is added; all inherited modules are read-only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped InnerProductSpace BigOperators ContDiff

namespace QuantumNLS.R52CFCount

open QuantumNLS.Prop010ContourBindingR11
open IndexedScalarMeasure IndexedScalarMeasureCuts
open PhysicalTensor (L2T)
open BetheCoefficientTransform (HN)
open LabelJointLimit LabelJointWeak LabelBlock
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm

variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

theorem continuous_symbol_input (hκ : 0 < κ) (z : ℂ) :
    Continuous (fun v : L2T L => NormalizedTransfer.productSymbol L κ v z) := by
  have he : (fun v : L2T L => NormalizedTransfer.productSymbol L κ v z) =
      fun v => Complex.exp (Complex.I * z * (L : ℂ) / 2) * L2SpatialTransfer.discriminant κ v z :=
    funext fun v => RootProductSymbolAnalytic.productSymbol_eq_exp_mul_discriminant L κ hκ.le v z
  rw [he]
  exact continuous_const.mul (continuous_iff_continuousAt.mpr fun v =>
    (DEF014DiscriminantAnalytic.analyticAt_discriminant κ z v).continuousAt)

/-- **Uniform count reconstruction near the rough center.** -/
theorem count_near (hκ : 0<κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ)
    {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (f : Extension (ℂ × ℂ)) (g : Extension (ℂ × (ℂ × ℂ)))
    (hf : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      f.value (z,w)=localLog L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w)
    (hg : ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
      ∀ w v,‖w-sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖<r →
      ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
      g.value (z,(w,v))=localCorrection L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w v) :
    ∃ D≥0,∃ N₀ : ℕ,∃ U ∈ 𝓝 u,∀ (N : ℕ) (hN : 0<N),N₀≤N → ∀ v ∈ U,‖v‖=1 →
      ‖(B L hκ hN n-C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1))
        (RootScalarPeriodR8.cut hκ u n) h) (HighMomentsOps.wvec N v)‖≤D*((N:ℝ)⁻¹)^2 := by
  let S := Prop026Bound.scalarCuts hκ u hu
  let a := RootScalarPeriodR8.cut hκ u (n-1)
  let b := RootScalarPeriodR8.cut hκ u n
  let G := EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)
  have hne : u≠0 := by intro he; rw [he,norm_zero] at hu; norm_num at hu
  have hcut (k : ℤ) : RootScalarPeriodR8.cut hκ u k ∈ S.cuts :=
    (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).separator_in_band k
  have hforce (k : ℤ) : exteriorForce L κ S.μ (RootScalarPeriodR8.cut hκ u k)=
      2*((k:ℝ)+1/2)*Real.pi := by
    change exteriorForce L κ (Prop026Bound.M hκ u) _ = _
    rw [Prop026Bound.force_eq hκ hne (hcut k)]
    have hp := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec k
    change Prop026Bound.theta hκ u (RootScalarPeriodR8.cut hκ u k)=((k:ℝ)+1/2)*Real.pi at hp
    rw [hp]
    ring
  have hab : a<b := (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)
  have h1 : 2*Real.pi*(n-1)<exteriorForce L κ S.μ a := by dsimp [a]; rw [hforce]; push_cast; nlinarith [Real.pi_pos]
  have h2 : exteriorForce L κ S.μ a<2*Real.pi*n := by dsimp [a]; rw [hforce]; push_cast; nlinarith [Real.pi_pos]
  have h3 : 2*Real.pi*n<exteriorForce L κ S.μ b := by dsimp [b]; rw [hforce]; nlinarith [Real.pi_pos]
  have h4 : exteriorForce L κ S.μ b<2*Real.pi*(n+1) := by dsimp [b]; rw [hforce]; nlinarith [Real.pi_pos]
  obtain ⟨m,z,hz,ε,hε,N₀,Cs,hCs,hprobes⟩ := cutoff_probes S (hcut (n-1)) (hcut n) hab hh hr h1 h2 h3 h4
  let K0 := 1+K κ a b h f g
  let D := Real.sqrt (Cs^2+K0^2*(ε/2)⁻¹^8*∑ _j : Fin m,max 0 (HighMomentsTransfer.Cunif L κ 0 4))
  -- the neighborhood: the probe values of `v` are within `ε/2` of those of `u`
  let U : Set (L2T L) := {v | ∀ j, ‖NormalizedTransfer.productSymbol L κ v (z j) -
    NormalizedTransfer.productSymbol L κ u (z j)‖ < ε/2}
  have hU : U ∈ 𝓝 u := by
    have : ∀ᶠ v in 𝓝 u, ∀ j, ‖NormalizedTransfer.productSymbol L κ v (z j) -
        NormalizedTransfer.productSymbol L κ u (z j)‖ < ε/2 := by
      rw [Filter.eventually_all]
      intro j
      have hc : ContinuousAt (fun v : L2T L => ‖NormalizedTransfer.productSymbol L κ v (z j) -
          NormalizedTransfer.productSymbol L κ u (z j)‖) u :=
        ((continuous_symbol_input L hκ (z j)).sub continuous_const).norm.continuousAt
      apply hc.eventually (gt_mem_nhds _)
      simp only [sub_self, norm_zero]
      positivity
    exact this
  refine ⟨D,Real.sqrt_nonneg _,N₀,U,hU,?_⟩
  intro N hN hN0 v hvU hv
  let R := B L hκ hN n-C L hκ hN f g a b h
  let re : BetheLabels.MArr N → ℂ := fun i =>
    (((i.1 n:ℝ)/N:ℝ):ℂ)-((c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i:ℝ):ℂ)
  have hR : ∀ i,R (basis L hκ hN i)=re i • basis L hκ hN i := by
    intro i
    dsimp [R,re]
    rw [sub_apply,B_basis,C_basis L hκ hN f g hab.le hh.le]
    exact (sub_smul _ _ _).symm
  have hbound : ∀ i,‖re i‖≤K0 := by
    intro i
    have hC := (condensate_reconstruction_operator_binding L hκ hN f g hab.le hh.le).2.2.2.2
    have hc := (C L hκ hN f g a b h).le_opNorm (basis L hκ hN i)
    rw [C_basis L hκ hN f g hab.le hh.le,norm_smul,(basis L hκ hN).orthonormal.1 i,mul_one,mul_one] at hc
    calc ‖re i‖ ≤ ‖(((i.1 n:ℝ)/N:ℝ):ℂ)‖+‖((c0 L hκ hN f a b h i+(N:ℝ)⁻¹*c1 L hκ hN g a b h i:ℝ):ℂ)‖ := by
            dsimp [re]; push_cast; exact norm_sub_le _ _
         _ ≤ K0 := add_le_add (massFraction_bound hN i n) (hc.trans hC)
  have hgood : ∀ i,(∀ j,‖ev L hκ hN (z j) i-NormalizedTransfer.productSymbol L κ u (z j)‖<ε) →
      ‖re i‖≤Cs*((N:ℝ)⁻¹)^2 := by
    intro i hi
    let Bc := configuration L hκ hN i
    have hprobe : ∀ j,‖sNf L (κ/N) Bc.q (z j)-sf L κ G (z j)‖<ε := by
      intro j
      have hroot : ∀ k,z j≠(Bc.q k:ℂ) := by
        intro k he
        have hhj := (hz j).1
        have him := congrArg Complex.im he
        simp only [Complex.ofReal_im] at him
        linarith
      rw [← ev_configuration L hκ hN i (z j) hroot]
      have hs := RootScalarPeriodR10.transfer_identity hκ u (z j) (Or.inl (ne_of_gt (show 0<(z j).im by have hj := (hz j).1; linarith)))
      have hs' : NormalizedTransfer.productSymbol L κ u (z j)=sf L κ G (z j) := by
        simpa [RootScalarPeriodR10.symbol,ScalarLogBranchR10.transfer,RootScalarPeriodR10.exponential,
          RootScalarPeriodR10.exponent,RootCauchyFullBracketR8.G,sf,Af,ef,G,mul_assoc,mul_left_comm,mul_comm] using hs
      rw [← hs']
      exact hi j
    obtain ⟨hl,herr⟩ := hprobes N hN hN0 Bc hprobe
    have hroot (w : ℂ) (hw : w ∈ Gam a b h) : ∀ k,w≠(Bc.q k:ℂ) := by
      intro k he
      have hn := (hl w hw).2.2.2.1 k
      rw [he,sub_self,norm_zero] at hn
      linarith [abs_nonneg (κ/(N:ℝ))]
    have hv' : ∀ w ∈ Gam a b h,‖deriv (sNf L (κ/N) Bc.q) w‖≤MixedQuadratures.Rbd L κ (h+1) := by
      intro w hw
      rw [← dev_configuration L hκ hN i w (hroot w hw)]
      exact derivative_cutoff_bound L hκ hN i w (Gam_abs_im hh hw)
    have hs := scalar_cutoff_error G Bc n hab.le hh.le f g hf hg hl hv'
    have heq : |((Finset.univ.filter fun j => Bc.n j=n).card:ℝ)/N -
        (-(2*Real.pi*κ)⁻¹*(LabelExactPeriod.rectIntegral (fun z => f.value (z,sNf L (κ/N) Bc.q z)) a b h).re+
         (N:ℝ)⁻¹*((I/(2*Real.pi):ℂ)*LabelExactPeriod.rectIntegral
           (fun z => g.value (z,(sNf L (κ/N) Bc.q z,deriv (sNf L (κ/N) Bc.q) z))) a b h).re)| = ‖re i‖ := by
      have hef := LabelExactPeriod.rectIntegral_congr
        (f := fun w => f.value (w,sNf L (κ/N) Bc.q w)) (g := fun w => f.value (w,ev L hκ hN w i))
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (bot_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (top_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (right_mem hh.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (left_mem hh.le hw))])
      have heg := LabelExactPeriod.rectIntegral_congr
        (f := fun w => g.value (w,(sNf L (κ/N) Bc.q w,deriv (sNf L (κ/N) Bc.q) w)))
        (g := fun w => g.value (w,(ev L hκ hN w i,dev L hκ hN w i)))
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (bot_mem hab.le hw)),dev_configuration L hκ hN i _ (hroot _ (bot_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (top_mem hab.le hw)),dev_configuration L hκ hN i _ (hroot _ (top_mem hab.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (right_mem hh.le hw)),dev_configuration L hκ hN i _ (hroot _ (right_mem hh.le hw))])
        (fun w hw => by rw [ev_configuration L hκ hN i _ (hroot _ (left_mem hh.le hw)),dev_configuration L hκ hN i _ (hroot _ (left_mem hh.le hw))])
      rw [hef,heg,configuration_count]
      simp only [re,← Complex.ofReal_sub,c0,c1,Complex.norm_real,Real.norm_eq_abs]
    rw [heq] at hs
    exact hs.trans herr
  -- at `v`: probe margin `ε/2` and the triangle inequality give the probe margin `ε` at `u`
  have hgood' : ∀ i,(∀ j,‖NormalityBridge.eigen (L := L) κ hκ hN i (z j)-
      NormalizedTransfer.productSymbol L κ v (z j)‖<ε/2) → ‖re i‖≤Cs*((N:ℝ)⁻¹)^2 := by
    intro i hi
    apply hgood i
    intro j
    have h1 := hi j
    have h2 := hvU j
    calc ‖ev L hκ hN (z j) i-NormalizedTransfer.productSymbol L κ u (z j)‖
        ≤ ‖NormalityBridge.eigen (L := L) κ hκ hN i (z j)-NormalizedTransfer.productSymbol L κ v (z j)‖+
          ‖NormalizedTransfer.productSymbol L κ v (z j)-NormalizedTransfer.productSymbol L κ u (z j)‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (NormalityBridge.eigen (L := L) κ hκ hN i (z j))
            (NormalizedTransfer.productSymbol L κ v (z j)) (NormalizedTransfer.productSymbol L κ u (z j))
          exact this
      _ < ε/2+ε/2 := add_lt_add h1 h2
      _ = ε := by ring
  exact CondensateLocalizationR10.physical_error_rate hκ v hv hN z hz R re hR (half_pos hε) hbound hgood'

end QuantumNLS.R52CFCount

#print axioms QuantumNLS.R52CFCount.count_near
