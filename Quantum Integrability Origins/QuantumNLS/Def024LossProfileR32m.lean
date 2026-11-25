import QuantumNLS.Def024LossFlowR32m
import QuantumNLS.RB7BindChart
import QuantumNLS.RB7Conserve

/-! Finite time-space regularity and the all-order DEF-024 multitime supplement. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open scoped ContDiff NNReal
open Set

namespace QuantumNLS.Def024LossR32m

open QuantumNLS.Fourier Sobolev Sobolev.PosWeight ClassicalCharges PhysicalTensor
open RB7 LossSobolev HierarchyFlow SmoothScalarMomentsPhysical

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-- A smooth periodic function at any finite field level. -/
def smoothInput {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ≥0) : (fieldScale L).Y s :=
  WField.mk (smoothL2 hu) (memHs_of_smooth hu (s : ℝ))

/-- Evaluating the Fourier representative of an `H^{m+2}` curve gives `C^m` jointly in all
parameters and the spatial variable. -/
theorem profile_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (V : E → H02 L ((m : ℝ) + 2)) (hV : ContDiff ℝ (m : ℕ∞) V) :
    ContDiff ℝ (m : ℕ∞) (fun p : E × ℝ => RB7H.Phi (L := L) ((m : ℝ) + 2) (by positivity) p.2 (V p.1)) := by
  exact (RB7H.isBoundedBilinear_eval (L := L) ((m : ℝ) + 2)).contDiff.comp
    (((RB7H.phi_contDiff (L := L) m).comp contDiff_snd).prodMk (hV.comp contDiff_fst))

private theorem profile_matches {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (m : ℕ)
    (v : H02 L ((m : ℝ) + 2)) (hv : v.val = smoothL2 hf) (x : ℝ) :
    RB7H.Phi (L := L) ((m : ℝ) + 2) (by positivity) x v = f x := by
  have hcurve : ∀ q : ℝ, 0 < q → ∃ V : ℝ → H02 L q, ContDiff ℝ ∞ V ∧
      ∀ τ, (V τ).val = smoothL2 hf := by
    intro q hq
    exact ⟨fun _ => WField.mk (smoothL2 hf) (memHs_of_smooth hf q), contDiff_const, fun _ => rfl⟩
  obtain ⟨hg, he⟩ := (RB7H.joint_smooth (fun _ => smoothL2 hf) hcurve).2.2 0
  have hpoint := congrFun (RB7H.eq_of_smoothL2_eq hg hf he) x
  have hs : 1 < (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  refine (RB7H.Phi_apply hs (by positivity) x v).trans ?_
  refine Eq.trans ?_ hpoint
  simp only [RB7H.Gfun]
  apply tsum_congr
  intro n
  simp only [RB7H.coefLin, LinearMap.coe_mk, AddHom.coe_mk, hv]

variable {ι : Type} [Fintype ι]

/-- Finite-data spatial representative, with `C^m` regularity in all independent times and space. -/
theorem finiteFlow_profile_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (order : ι → ℕ) (m : ℕ) (u : (fieldScale L).Y (inputLevel order m ((m : ℝ≥0) + 2))) :
    ContDiff ℝ (m : ℕ∞) (fun p : (ι → ℝ) × ℝ =>
      RB7H.Phi (L := L) ((m : ℝ) + 2) (by positivity) p.2
        (finiteFlow hR C order m ((m : ℝ≥0) + 2) p.1 u)) :=
  profile_contDiff m _ (finiteFlow_contDiff hR C order m _ u)

/-- Order `r` flow on a finite physical Sobolev level, with real time. -/
def orderFlow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (r m : ℕ) (q : ℝ≥0) (t : ℝ)
    (u : (fieldScale L).Y (inputLevel (fun _ : Unit => r) m q)) : (fieldScale L).Y q :=
  finiteFlow hR C (fun _ : Unit => r) m q (fun _ => t) u

/-- The finite-level order-`r` extension agrees with the Hamiltonian chart flow on smooth data. -/
theorem orderFlow_matches_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (r m : ℕ) (q : ℝ≥0) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    (orderFlow hR C r m q t (smoothInput hu _)).val =
      smoothL2 (((isHamFlow_chart hR C r u hu).2.2 t).1) := by
  have hf := ((isHamFlow_chart hR C r u hu).2.2 t).1
  apply (Function.LeftInverse.injective C.ΨΦ)
  apply lp.ext
  funext n
  change C.Φ (orderFlow hR C r m q t (smoothInput hu _)).val n = C.Φ (smoothL2 hf) n
  refine (finiteFlow_coords hR C (fun _ : Unit => r) m q (fun _ => t) (smoothInput hu _) n).trans ?_
  refine Eq.trans ?_ (coords_chartFlow hR C r hu t hf n).symm
  rw [omegaOf_eq_FreqSeq]
  simp [smoothInput] <;> rfl

/-- End-to-end finite loss for every order. The extension has `m` time derivatives into
`H^q` at each finite-level datum, with bounds on compact time sets. Its restriction to
smooth input is the Hamiltonian chart flow. -/
def OrderFiniteLoss (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (r m : ℕ) (q : ℝ≥0) : Prop :=
    (∀ u : (fieldScale L).Y (inputLevel (fun _ : Unit => r) m q),
      ContDiff ℝ (m : ℕ∞) (fun t => orderFlow hR C r m q t u) ∧
      ∀ T : Set ℝ, IsCompact T → ∃ B : ℝ, ∀ t ∈ T, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun s => orderFlow hR C r m q s u) t‖ ≤ B) ∧
    (∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u) (t : ℝ),
      (orderFlow hR C r m q t (smoothInput hu _)).val =
        smoothL2 (((isHamFlow_chart hR C r u hu).2.2 t).1))

theorem orderFlow_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (r m : ℕ) (q : ℝ≥0) (u : (fieldScale L).Y (inputLevel (fun _ : Unit => r) m q)) :
    ContDiff ℝ (m : ℕ∞) (fun t => orderFlow hR C r m q t u) := by
  let order : Unit → ℕ := fun _ => r
  let A : ℝ →L[ℝ] (Unit → ℝ) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)
  let V : (Unit → ℝ) → (fieldScale L).Y q := fun t => finiteFlow hR C order m q t u
  have hV : ContDiff ℝ (m : ℕ∞) V := finiteFlow_contDiff hR C order m q u
  change ContDiff ℝ (m : ℕ∞) (V ∘ A)
  exact hV.comp A.contDiff

theorem orderFlow_finite_loss (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    (r m : ℕ) (q : ℝ≥0) : OrderFiniteLoss hR C r m q := by
  refine ⟨?_, fun _ hu t => orderFlow_matches_chart hR C r m q hu t⟩
  intro u
  exact ⟨orderFlow_contDiff hR C r m q u,
    fun _ hT => compact_derivatives (orderFlow_contDiff hR C r m q u) hT⟩

/-- The accepted chart and REG-015 supply the orderwise finite-loss property at every level. -/
theorem finite_loss_all_orders (hκ : 0 < κ) :
    ∃ C : ChartFacts (L := L) hκ, ∀ (r m : ℕ) (q : ℝ≥0),
      OrderFiniteLoss (Reg015HFinal.REG015_final hκ) C r m q := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  exact ⟨C, orderFlow_finite_loss (Reg015HFinal.REG015_final hκ) C⟩

/-- Extend a vector of independent times for `𝓡` by zero on unused coordinates. -/
def extendTime (𝓡 : Finset ℕ) (t : (↥𝓡 → ℝ)) (r : ℕ) : ℝ :=
  if hr : r ∈ 𝓡 then t ⟨r, hr⟩ else 0

/-- At every finite Sobolev level the multitime extension agrees with the smooth
Hamiltonian composition. -/
theorem finiteFlow_matches_joint (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    {𝓡 : Finset ℕ} (F : HamFlows L κ 𝓡) (m : ℕ) (q : ℝ≥0) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (t : ↥𝓡 → ℝ)
    (hj : SmoothPeriodic L (jointClassicalFlow F (extendTime 𝓡 t) u)) :
    (finiteFlow hR C (fun r : ↥𝓡 => r.val) m q t (smoothInput hu _)).val = smoothL2 hj := by
  apply (Function.LeftInverse.injective C.ΨΦ)
  apply lp.ext
  funext n
  change C.Φ (finiteFlow hR C (fun r : ↥𝓡 => r.val) m q t (smoothInput hu _)).val n =
    C.Φ (smoothL2 hj) n
  refine (finiteFlow_coords hR C (fun r : ↥𝓡 => r.val) m q t (smoothInput hu _) n).trans ?_
  refine Eq.trans ?_ (joint_rotation_form hR C F (extendTime 𝓡 t) hu hj n).symm
  let ν (r : ℕ) : ℝ :=
    FreqSeq (SOf r : ℝ) (Fd hR C r) (fun i => C.Φ (smoothL2 hu) i) n
  have hsum : (∑ r : ↥𝓡, t r * ν r.val) = ∑ r ∈ 𝓡, extendTime 𝓡 t r * ν r := by
    rw [← Finset.sum_attach 𝓡 (fun r => extendTime 𝓡 t r * ν r)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show extendTime 𝓡 t r.val = t r from by simp [extendTime, r.property]]
  change Complex.exp (((-(∑ r : ↥𝓡, t r * ν r.val) : ℝ) : ℂ) * Complex.I) * C.Φ (smoothL2 hu) n =
    Complex.exp (((-(∑ r ∈ 𝓡, extendTime 𝓡 t r * ν r) : ℝ) : ℂ) * Complex.I) * C.Φ (smoothL2 hu) n
  rw [hsum]

/-- Joint smoothness in the independent times and space, for every enumeration, with
derivative bounds on compact time-space sets. -/
def JointContDiff {𝓡 : Finset ℕ} (F : HamFlows L κ 𝓡) (u : ℝ → ℂ) : Prop :=
    ContDiff ℝ ∞ (fun p : (↥𝓡 → ℝ) × ℝ => jointClassicalFlow F (extendTime 𝓡 p.1) u p.2) ∧
    (∀ l : List ℕ, l.Perm (𝓡.sort (· ≤ ·)) →
      ContDiff ℝ ∞ (fun p : (↥𝓡 → ℝ) × ℝ =>
        (((l.map fun r => F.Φ r (extendTime 𝓡 p.1 r)).foldr (· ∘ ·) id) u) p.2)) ∧
    ∀ (m : ℕ) (K : Set ((↥𝓡 → ℝ) × ℝ)), IsCompact K →
      ∃ B : ℝ, ∀ p ∈ K, ∀ j ≤ m, ‖iteratedFDeriv ℝ j
        (fun p : (↥𝓡 → ℝ) × ℝ => jointClassicalFlow F (extendTime 𝓡 p.1) u p.2) p‖ ≤ B

private theorem joint_contDiff_family (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)
    {𝓡 : Finset ℕ} (F : HamFlows L κ 𝓡) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    JointContDiff F u := by
  have hmain : ContDiff ℝ ∞ (fun p : (↥𝓡 → ℝ) × ℝ =>
      jointClassicalFlow F (extendTime 𝓡 p.1) u p.2) := by
    refine contDiff_infty.2 fun m => ?_
    let order : ↥𝓡 → ℕ := Subtype.val
    let q : ℝ≥0 := (m : ℝ≥0) + 2
    let V : (↥𝓡 → ℝ) → H02 L ((m : ℝ) + 2) :=
      fun t => finiteFlow hR C order m q t (smoothInput hu _)
    have hV : ContDiff ℝ (m : ℕ∞) V :=
      finiteFlow_contDiff_of_rapid hR C order m q (smoothInput hu _) (hinf_all hR C hu)
    have heq : (fun p : (↥𝓡 → ℝ) × ℝ => jointClassicalFlow F (extendTime 𝓡 p.1) u p.2) =
        fun p => RB7H.Phi (L := L) ((m : ℝ) + 2) (by positivity) p.2 (V p.1) := by
      funext p
      let t := extendTime 𝓡 p.1
      have hj : SmoothPeriodic L (jointClassicalFlow F t u) :=
        joint_smooth_of_family hR C F t hu
      have hv : (V p.1).val = smoothL2 hj :=
        finiteFlow_matches_joint hR C F m q hu p.1 hj
      exact (profile_matches hj m (V p.1) hv p.2).symm
    rw [heq]
    exact profile_contDiff m V hV
  refine ⟨hmain, ?_, ?_⟩
  · intro l hl
    have he : (fun p : (↥𝓡 → ℝ) × ℝ =>
        (((l.map fun r => F.Φ r (extendTime 𝓡 p.1 r)).foldr (· ∘ ·) id) u) p.2) =
          fun p => jointClassicalFlow F (extendTime 𝓡 p.1) u p.2 :=
      funext fun p => congrFun (foldr_perm hR C F (extendTime 𝓡 p.1) hl hu) p.2
    rw [he]
    exact hmain
  · intro m K hK
    exact compact_derivatives (m := m) (hmain.of_le (by simp)) hK

/-- The pre-start DEF-024 supplement uses the shared printed conditional hierarchy
statement as its one input. Its higher-order witnesses, together with the low-order
flows, give a family independent of the smooth initial datum. -/
theorem joint_contDiff_ofInput (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) (𝓡 : Finset ℕ) :
    (∃ F : HamFlows L κ 𝓡, ∀ u, SmoothPeriodic L u → JointContDiff F u) ∧
    ∀ (F : HamFlows L κ 𝓡) u, SmoothPeriodic L u → JointContDiff F u := by
  obtain ⟨A, hA, _⟩ := RB7BindChart.printedChart_antecedent (L := L) hκ
  obtain ⟨Φ, hΦ, _⟩ := HierarchyInput A.Φ hA
    (RB7BindChart.sobolev_antecedent hκ A.Φ hA)
    (RB7BindChart.scalarUniqueness_antecedent hκ)
    (RB7BindChart.scalarMoments_antecedent hκ)
  let hR : REG015Concl (L := L) hκ := Reg015HFinal.REG015_final hκ
  let C := RB7BindChart.chartFactsOf A
  let F : HamFlows L κ 𝓡 := {
    Φ := fun r => if 2 ≤ r then Φ r else chartFlow hR C r
    ham := fun r _ => by
      by_cases hr : 2 ≤ r
      · simpa [hr] using hΦ r hr
      · simpa [hr] using isHamFlow_chart hR C r
  }
  exact ⟨⟨F, fun _ hu => joint_contDiff_family hR C F hu⟩,
    fun G _ hu => joint_contDiff_family hR C G hu⟩

end QuantumNLS.Def024LossR32m

#print axioms QuantumNLS.Def024LossR32m.finiteFlow_profile_contDiff
#print axioms QuantumNLS.Def024LossR32m.orderFlow_finite_loss
#print axioms QuantumNLS.Def024LossR32m.finite_loss_all_orders
#print axioms QuantumNLS.Def024LossR32m.finiteFlow_matches_joint
#print axioms QuantumNLS.Def024LossR32m.JointContDiff
#print axioms QuantumNLS.Def024LossR32m.joint_contDiff_ofInput
