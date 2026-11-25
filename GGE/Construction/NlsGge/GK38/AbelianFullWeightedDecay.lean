import NlsGge.GK38.AbelianUnitWeightedDecay

/-! The true interpolation decay for arbitrary lp2 directions. The finite head
uses exact product factors; the direction tail uses the uniform actual derivative
bound. This never approximates the potential by finite-gap potentials. -/
set_option autoImplicit false
open Set Filter Topology Metric
open scoped ENNReal
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

def countingDecay (f : ℂ → ℂ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ z : ℂ,
    ‖z‖=m*Real.pi+Real.pi/2 → ‖f z‖ ≤ ε*‖Complex.sin z‖

theorem countingDecay_zero : countingDecay (fun _ : ℂ => (0 : ℂ)) := by
  intro ε hε
  exact ⟨0,fun _ _ z _ => by simpa only [norm_zero] using mul_nonneg hε.le (norm_nonneg (Complex.sin z))⟩

theorem countingDecay_add {f g : ℂ → ℂ} (hf : countingDecay f)
    (hg : countingDecay g) : countingDecay (fun z => f z+g z) := by
  intro ε hε
  obtain ⟨N,hN⟩ := hf (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := hg (ε/2) (by positivity)
  refine ⟨max N M,?_⟩
  intro m hm z hz
  have h1 := hN m ((le_max_left N M).trans hm) z hz
  have h2 := hM m ((le_max_right N M).trans hm) z hz
  exact (norm_add_le _ _).trans (by linarith)

theorem countingDecay_const_mul (a : ℂ) {f : ℂ → ℂ} (hf : countingDecay f) :
    countingDecay (fun z => a*f z) := by
  intro ε hε
  obtain ⟨N,hN⟩ := hf (ε/(‖a‖+1)) (by positivity)
  refine ⟨N,?_⟩
  intro m hm z hz
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left (hN m hm z hz) (norm_nonneg a)
  have hεa : ‖a‖*(ε/(‖a‖+1)) ≤ ε := by
    have hpos : 0 < ‖a‖+1 := by positivity
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hpos).2 (by nlinarith [norm_nonneg a])
  calc
    _ ≤ ‖a‖*(ε/(‖a‖+1)*‖Complex.sin z‖) := h
    _ = (‖a‖*(ε/(‖a‖+1)))*‖Complex.sin z‖ := by ring
    _ ≤ ε*‖Complex.sin z‖ := mul_le_mul_of_nonneg_right hεa (norm_nonneg _)

theorem countingDecay_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ r ∈ S, countingDecay (f r)) :
    countingDecay (fun z => ∑ r ∈ S, f r z) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty => intro _;simpa only [Finset.sum_empty] using countingDecay_zero
  | @insert a S ha ih =>
    intro hf
    have hS : ∀ r ∈ S, countingDecay (f r) := fun r hr => hf r (Finset.mem_insert_of_mem hr)
    have h := countingDecay_add (hf a (Finset.mem_insert_self a S)) (ih hS)
    simpa only [Finset.sum_insert ha] using h

theorem variation_single_coeff (n r : ℤ) (s : Lib.L2Seq) (a z : ℂ) :
    p4NumeratorVariation38 n s (lp.single 2 r a) z=
      a*p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z := by
  have hs : lp.single (E := fun _ : ℤ => ℂ) 2 r a=
      a • lp.single (E := fun _ : ℤ => ℂ) 2 r (1 : ℂ) := by
    rw [← lp.single_smul]
    simp only [smul_eq_mul,mul_one]
  change variationCLM n s z (lp.single 2 r a)=a*variationCLM n s z (lp.single 2 r (1 : ℂ))
  rw [hs,map_smul,smul_eq_mul]

theorem variation_single_weighted_countingDecay (n r : ℤ) (s : Lib.L2Seq) (a : ℂ) :
    countingDecay (fun z => p4NumeratorVariation38 n s (lp.single 2 r a) z*(Lib.sigmaOf s n-z)) := by
  have hu : countingDecay (fun z => p4NumeratorVariation38 n s
      (lp.single 2 r (1 : ℂ)) z*(Lib.sigmaOf s n-z)) := by
    by_cases hr : r=n
    · subst r
      simpa only [variation_omitted_unit,zero_mul] using countingDecay_zero
    · intro ε hε
      obtain ⟨N,hN⟩ := variation_unit_weighted_decay n r hr s ε hε
      exact ⟨N,fun m hm z hz => by simpa only [norm_mul] using hN m hm z hz⟩
  have h := countingDecay_const_mul a hu
  have he : (fun z => p4NumeratorVariation38 n s (lp.single 2 r a) z*(Lib.sigmaOf s n-z))=
      (fun z => a*(p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z*(Lib.sigmaOf s n-z))) := by
    funext z
    rw [variation_single_coeff]
    ring
  rwa [he]

theorem variation_section_weighted_countingDecay (n : ℤ) (s h : Lib.L2Seq) (S : Finset ℤ) :
    countingDecay (fun z => p4NumeratorVariation38 n s
      (∑ r ∈ S, lp.single 2 r (h r)) z*(Lib.sigmaOf s n-z)) := by
  have hs := countingDecay_sum S
    (fun r z => p4NumeratorVariation38 n s (lp.single 2 r (h r)) z*(Lib.sigmaOf s n-z))
    (fun r _ => variation_single_weighted_countingDecay n r s (h r))
  have he : (fun z => p4NumeratorVariation38 n s
      (∑ r ∈ S, lp.single 2 r (h r)) z*(Lib.sigmaOf s n-z))=
      (fun z => ∑ r ∈ S, p4NumeratorVariation38 n s (lp.single 2 r (h r)) z*(Lib.sigmaOf s n-z)) := by
    funext z
    change (variationCLM n s z) (∑ r ∈ S, lp.single 2 r (h r))*(Lib.sigmaOf s n-z)=_
    rw [map_sum,Finset.sum_mul]
    rfl
  rwa [he]

theorem variation_full_weighted_countingDecay (n : ℤ) (s h : Lib.L2Seq) :
    countingDecay (fun z => p4NumeratorVariation38 n s h z*(Lib.sigmaOf s n-z)) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := variation_weighted_circle_bound n s
  have hδ : 0 < ε/(2*C) := by positivity
  have hconv := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ℝ≥0∞)) (by simp) h
  obtain ⟨S,hS⟩ := Filter.eventually_atTop.mp
    (hconv.eventually (Metric.ball_mem_nhds h hδ))
  let H : Lib.L2Seq := ∑ r ∈ S, lp.single 2 r (h r)
  have htail : ‖h-H‖ < ε/(2*C) := by
    have h0 := hS S le_rfl
    simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev,H] using h0
  have hsmall : C*‖h-H‖ ≤ ε/2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hC)).mp htail.le
    nlinarith
  obtain ⟨N,hN⟩ := variation_section_weighted_countingDecay n s h S (ε/2) (by positivity)
  refine ⟨N,?_⟩
  intro m hm z hz
  have hhead : ‖p4NumeratorVariation38 n s H z*(Lib.sigmaOf s n-z)‖ ≤
      (ε/2)*‖Complex.sin z‖ := hN m hm z hz
  have hrest : ‖p4NumeratorVariation38 n s (h-H) z*(Lib.sigmaOf s n-z)‖ ≤
      (ε/2)*‖Complex.sin z‖ := by
    rw [norm_mul]
    exact (hbound (h-H) m z hz).trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
  have he : p4NumeratorVariation38 n s h z*(Lib.sigmaOf s n-z)=
      p4NumeratorVariation38 n s H z*(Lib.sigmaOf s n-z)+
        p4NumeratorVariation38 n s (h-H) z*(Lib.sigmaOf s n-z) := by
    change variationCLM n s z h*(Lib.sigmaOf s n-z)=
      variationCLM n s z H*(Lib.sigmaOf s n-z)+variationCLM n s z (h-H)*(Lib.sigmaOf s n-z)
    rw [map_sub]
    ring
  change ‖p4NumeratorVariation38 n s h z*(Lib.sigmaOf s n-z)‖ ≤ ε*‖Complex.sin z‖
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end
end NlsGge.GK38.P4NumeratorVariation
