import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.DM.DM009
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST006
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST013
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.GK38.Lib.CircleArgument
import NlsGge.ThirdConsultation.M.MRound11Elim
import NlsGge.ThirdConsultation.KST.KST033Real
import NlsGge.ThirdConsultation.KST.KST052Host

                                                                                                                                
                                                                                    
                                                                                                                           
                                                                                    
                                                                                                                             
                                                                                                       
                                                                                                                          
                                                                                                                     
                                               
                                                                                                                             
                                                             
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.ThirdConsultation.KST.KST052S

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
  NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Schur
open NlsGge.DM009Psi
open NlsGge.Atomic.KST016 (frame entry correction localCorrection localFreeFactor entry_eq frame_inner
  frame_coe entries_correction qOperator_local_resolvent_identity)

/-! ### (1) off-diagonal real-form identity -/

theorem c_eq_eps_star_b (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (w : ℂ) :
    c φ n w = (ε : ℂ) * star (b φ n (star w)) := by
  have h1 := PsiMap_inner ε hε (kstPnUpper n)
    (localCorrection n (center n) (center_mem_strip n) (w, φ) (kstPnLower n))
  rw [PsiMap_upper, KST033R.psiE_localCorrection φ ε hε h n w (kstPnLower n), PsiMap_lower,
    inner_smul_left, Complex.conj_ofReal] at h1
  have h2 : star (c φ n w) = (ε : ℂ) * b φ n (star w) := by
    rw [c_formula, b_formula]
    exact h1.symm
  have hs : star (ε : ℂ) = (ε : ℂ) := by simp
  calc c φ n w = star (star (c φ n w)) := (star_star _).symm
    _ = star ((ε : ℂ) * b φ n (star w)) := by rw [h2]
    _ = (ε : ℂ) * star (b φ n (star w)) := by
        rw [star_mul', hs]

/-! ### (2) equal diagonal entries -/

theorem frame_true_coe (n : ℤ) : ((frame n true : resonantSubspace n) : KSTPairL2) = kstPnUpper n := by
  rw [frame_coe]
  simp [kstPnFrame]

theorem frame_false_coe (n : ℤ) : ((frame n false : resonantSubspace n) : KSTPairL2) = kstPnLower n := by
  rw [frame_coe]
  simp [kstPnFrame]

theorem correction_eq_local (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) :
    localCorrection n (center n) (center_mem_strip n) (z, φ) = correction φ n z hz := by
  have hfree : IsUnit (localFreeFactor n (center n) (center_mem_strip n) (z, φ)) :=
    isUnit_free_of_strips n (center n) z (center_mem_strip n) hz
  have hq := qOperator_local_resolvent_identity φ n (center n) z (center_mem_strip n) hz hfree
  unfold localCorrection correction
  rw [hq]
  rfl

theorem entry_true_true (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) :
    entry φ n z hz true true = entry φ n z hz false false := by
  have hd := NlsGge.DM009Diag.diag_identity n φ z
  rw [correction_eq_local φ n z hz] at hd
  have ha : a φ n z = NlsGge.Atomic.KST016.reducedA φ n z hz :=
    congrArg Prod.fst (abc_eq_reduced φ n z hz)
  have e1 := (entries_correction φ n z hz).1
  have e2 : inner ℂ ((frame n true : resonantSubspace n) : KSTPairL2)
      (correction φ n z hz ((frame n true : resonantSubspace n) : KSTPairL2)) =
      NlsGge.Atomic.KST016.reducedA φ n z hz := by
    rw [frame_true_coe, hd, ha]
  rw [entry_eq, entry_eq, frame_inner, frame_inner, e2, ← e1]
  simp

/-! ### (3) vanishing entries give the zero operator -/

theorem resonant_expand' (n : ℤ) (w : resonantSubspace n) :
    (w : KSTPairL2) = inner ℂ (kstPnLower n) (w : KSTPairL2) • kstPnLower n +
      inner ℂ (kstPnUpper n) (w : KSTPairL2) • kstPnUpper n := by
  obtain ⟨v, hv⟩ := w.2
  have hfix : spectralPn n (w : KSTPairL2) = (w : KSTPairL2) := by
    change spectralPn n v = (w : KSTPairL2) at hv
    have h := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S v) (spectralPn_idempotent n)
    change spectralPn n (spectralPn n v) = spectralPn n v at h
    rw [hv] at h
    exact h
  calc (w : KSTPairL2) = spectralPn n (w : KSTPairL2) := hfix.symm
    _ = _ := by rw [spectralPn_apply, add_comm]

theorem reducedS_frame_eq_zero (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (h0 : ∀ i j : Bool, entry φ n z hz i j = 0) (j : Bool) :
    NlsGge.Atomic.KST013.reducedS φ n z hz (frame n j) = 0 := by
  apply Subtype.ext
  have e0 : inner ℂ (kstPnLower n)
      ((NlsGge.Atomic.KST013.reducedS φ n z hz (frame n j) : resonantSubspace n) : KSTPairL2) = 0 := by
    have h := h0 false j
    unfold entry at h
    rwa [frame_false_coe] at h
  have e1 : inner ℂ (kstPnUpper n)
      ((NlsGge.Atomic.KST013.reducedS φ n z hz (frame n j) : resonantSubspace n) : KSTPairL2) = 0 := by
    have h := h0 true j
    unfold entry at h
    rwa [frame_true_coe] at h
  rw [resonant_expand' n (NlsGge.Atomic.KST013.reducedS φ n z hz (frame n j)), e0, e1]
  simp

theorem reducedS_eq_zero_of_entries (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (h0 : ∀ i j : Bool, entry φ n z hz i j = 0) :
    NlsGge.Atomic.KST013.reducedS φ n z hz = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = inner ℂ (kstPnLower n) (u : KSTPairL2) • frame n false +
      inner ℂ (kstPnUpper n) (u : KSTPairL2) • frame n true := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, frame_false_coe, frame_true_coe]
    exact resonant_expand' n u
  calc NlsGge.Atomic.KST013.reducedS φ n z hz u
      = NlsGge.Atomic.KST013.reducedS φ n z hz
        (inner ℂ (kstPnLower n) (u : KSTPairL2) • frame n false +
          inner ℂ (kstPnUpper n) (u : KSTPairL2) • frame n true) := congrArg _ hu
    _ = 0 := by
        rw [map_add, map_smul, map_smul, reducedS_frame_eq_zero φ n z hz h0 false,
          reducedS_frame_eq_zero φ n z hz h0 true]
        simp

/-! ### (4) the actual eigenspace is the resonant space -/

theorem eigenspace_equiv (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hT : ‖qOperator φ n z hz ^ 2‖ < 1) (hunit : IsUnit (1 - qOperator φ n z hz))
    (hS : NlsGge.Atomic.KST013.reducedS φ n z hz = 0) :
    ∃ E : eigenspace φ z ≃ₗ[ℂ] resonantSubspace n,
      ∀ f : eigenspace φ z,
        (E f : KSTPairL2) = spectralPn n (((f.1 : (dirac φ).domain)) : KSTPairL2) := by
  have eig : ∀ f : (dirac φ).domain, f ∈ eigenspace φ z → dirac φ f = z • (f : KSTPairL2) := by
    intro f hf
    have h : (dirac φ).toFun f - z • (f : KSTPairL2) = 0 := hf
    exact sub_eq_zero.mp h
  have mem : ∀ f : (dirac φ).domain, dirac φ f = z • (f : KSTPairL2) → f ∈ eigenspace φ z := by
    intro f hf
    show (dirac φ).toFun f - z • (f : KSTPairL2) = 0
    exact sub_eq_zero.mpr hf
  let Φ : eigenspace φ z →ₗ[ℂ] resonantSubspace n :=
    { toFun := fun f => ⟨spectralPn n (((f.1 : (dirac φ).domain)) : KSTPairL2), ⟨_, rfl⟩⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp [map_add]
      map_smul' := fun c f => by
        apply Subtype.ext
        simp [map_smul] }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have hP : spectralPn n (((f.1 : (dirac φ).domain)) : KSTPairL2) = 0 :=
      congrArg (fun a : resonantSubspace n => (a : KSTPairL2)) hf
    have hF := eig f.1 f.2
    have hact : actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
        ⟨((f.1 : (dirac φ).domain) : KSTPairL2), (f.1 : (dirac φ).domain).property⟩ =
        -(z • ((f.1 : (dirac φ).domain) : KSTPairL2)) := by
      have hdirac : dirac φ f.1 =
          -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
            ⟨((f.1 : (dirac φ).domain) : KSTPairL2), (f.1 : (dirac φ).domain).property⟩ := rfl
      rw [hdirac] at hF
      exact neg_eq_iff_eq_neg.mp hF
    obtain ⟨g, hgraph, hprod⟩ :=
      (NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff φ
        ((f.1 : (dirac φ).domain) : KSTPairL2)
        (z • ((f.1 : (dirac φ).domain) : KSTPairL2))).2
        ⟨(f.1 : (dirac φ).domain).property, hact⟩
    have h0 := NlsGge.Atomic.KST013.stage13G_projection_zero_forces_zero φ n z hz _ g hgraph hprod
      hunit hP
    apply Subtype.ext
    apply Subtype.ext
    exact h0
  have hsurj : Function.Surjective Φ := by
    intro u
    have hu : spectralPn n (u : KSTPairL2) = (u : KSTPairL2) := by
      obtain ⟨v, hv⟩ := u.2
      change spectralPn n v = (u : KSTPairL2) at hv
      have h := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S v) (spectralPn_idempotent n)
      change spectralPn n (spectralPn n v) = spectralPn n v at h
      rw [hv] at h
      exact h
    have hred : (z - (n : ℂ) * (Real.pi : ℂ)) • (u : KSTPairL2) =
        spectralPn n (Ring.inverse (1 - qOperator φ n z hz)
          (potentialOnPn φ n (u : KSTPairL2))) := by
      have h := congrArg (fun a : resonantSubspace n => (a : KSTPairL2))
        (show NlsGge.Atomic.KST013.reducedS φ n z hz u = 0 by simp [hS])
      change (z - (n : ℂ) * (Real.pi : ℂ)) • (u : KSTPairL2) -
        spectralPn n (Ring.inverse (1 - qOperator φ n z hz)
          (potentialOnPn φ n (u : KSTPairL2))) = 0 at h
      exact sub_eq_zero.mp h
    obtain ⟨hgraph, hprod, hPu, -⟩ :=
      NlsGge.ThirdConsultation.MTwoModeSupp.backward_construct
        NlsGge.Atomic.KST012.stageD_reconstructed_actual_bridges φ n z hz hT (u : KSTPairL2) hu hred
    obtain ⟨hf, hact⟩ :=
      (NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff φ
        ((u : KSTPairL2) + reconstructedComplement φ n z hz (u : KSTPairL2))
        (z • ((u : KSTPairL2) + reconstructedComplement φ n z hz (u : KSTPairL2)))).1
        ⟨_, hgraph, hprod⟩
    have hmem : (⟨_, hf⟩ : (dirac φ).domain) ∈ eigenspace φ z := by
      apply mem
      change -actualFullPeriodTwoDoubledCirclePerturbedDiracAction (-(φ true)) (-(φ false))
        ⟨_, hf⟩ = _
      rw [hact, neg_neg]
    exact ⟨⟨⟨_, hf⟩, hmem⟩, Subtype.ext hPu⟩
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun f => rfl⟩

/-! ### (5) a double zero of the determinant -/

theorem determinant_order_ge_two (n : ℤ) (fa fb fc : ℂ → ℂ) (σ : ℂ)
    (ha : AnalyticAt ℂ fa σ) (hb : AnalyticAt ℂ fb σ) (hc : AnalyticAt ℂ fc σ)
    (hσ : σ = center n + fa σ) (hb0 : fb σ = 0) (hc0 : fc σ = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (determinant n fa fb fc) σ := by
  let g : ℂ → ℂ := fun z => z - center n - fa z
  have hg : AnalyticAt ℂ g σ := (analyticAt_id.sub analyticAt_const).sub ha
  have hg0 : g σ = 0 := by
    simp only [g]
    linear_combination hσ
  have h1 : (1 : ℕ∞) ≤ analyticOrderAt g σ :=
    ENat.one_le_iff_ne_zero.mpr (analyticOrderAt_ne_zero.mpr ⟨hg, hg0⟩)
  have hb1 : (1 : ℕ∞) ≤ analyticOrderAt fb σ :=
    ENat.one_le_iff_ne_zero.mpr (analyticOrderAt_ne_zero.mpr ⟨hb, hb0⟩)
  have hc1 : (1 : ℕ∞) ≤ analyticOrderAt fc σ :=
    ENat.one_le_iff_ne_zero.mpr (analyticOrderAt_ne_zero.mpr ⟨hc, hc0⟩)
  have e1 : determinant n fa fb fc = g ^ 2 - fb * fc := by
    funext z
    simp [determinant, g]
  rw [e1]
  refine le_trans ?_ le_analyticOrderAt_sub
  refine le_min ?_ ?_
  · rw [analyticOrderAt_pow hg]
    calc (2 : ℕ∞) = 2 • (1 : ℕ∞) := by simp
      _ ≤ 2 • analyticOrderAt g σ := nsmul_le_nsmul_right h1 2
  · rw [analyticOrderAt_mul hb hc]
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := add_le_add hb1 hc1

theorem determinant_analyticAt (n : ℤ) (fa fb fc : ℂ → ℂ) (z : ℂ)
    (ha : AnalyticAt ℂ fa z) (hb : AnalyticAt ℂ fb z) (hc : AnalyticAt ℂ fc z) :
    AnalyticAt ℂ (determinant n fa fb fc) z := by
  have : determinant n fa fb fc = fun w => (w - center n - fa w) ^ 2 - fb w * fc w := by
    funext w
    rfl
  rw [this]
  exact (((analyticAt_id.sub analyticAt_const).sub ha).pow 2).sub (hb.mul hc)

open Classical in
theorem double_zero_multiset {D : ℂ → ℂ} {c0 : ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ D (Metric.closedBall c0 R))
    {σ x y : ℂ} (hσ : σ ∈ Metric.ball c0 R) (hord : (2 : ℕ∞) ≤ analyticOrderAt D σ)
    (hm : NlsGge.GK38.Lib.zeroMultiset D (Metric.ball c0 R) = {x, y}) :
    x = σ ∧ y = σ := by
  by_cases htop : analyticOrderAt D σ = ⊤
  · exfalso
    have hev : ∀ᶠ z in 𝓝 σ, D z = 0 := analyticOrderAt_eq_top.mp htop
    have hzero : Set.EqOn D 0 (Metric.ball c0 R) :=
      (hA.mono Metric.ball_subset_closedBall).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball c0 R).isPreconnected hσ hev
    have hxmem : x ∈ NlsGge.GK38.Lib.zeroMultiset D (Metric.ball c0 R) := by
      rw [hm]
      simp
    rw [NlsGge.GK38.Lib.mem_zeroMultiset_ball hA] at hxmem
    obtain ⟨hxb, hxne⟩ := hxmem
    apply hxne
    have htx : analyticOrderAt D x = ⊤ := by
      rw [analyticOrderAt_eq_top]
      filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with z hz using hzero hz
    simp [analyticOrderNatAt, htx]
  · have hcount := NlsGge.GK38.Lib.count_zeroMultiset_ball hA σ
    rw [if_pos hσ, hm] at hcount
    obtain ⟨m, hmm⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hmm] at hord
    have h2 : 2 ≤ m := by exact_mod_cast hord
    have hnat : analyticOrderNatAt D σ = m := by
      simp [analyticOrderNatAt, ← hmm]
    rw [hnat, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hcount
    by_cases hx : σ = x
    · by_cases hy : σ = y
      · exact ⟨hx.symm, hy.symm⟩
      · rw [if_pos hx, if_neg hy] at hcount
        omega
    · by_cases hy : σ = y
      · rw [if_neg hx, if_pos hy] at hcount
        omega
      · rw [if_neg hx, if_neg hy] at hcount
        omega

end NlsGge.ThirdConsultation.KST.KST052S
end
