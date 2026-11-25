import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs
import QuantumNLS.Local020Core
import QuantumNLS.Local020Mul1
import QuantumNLS.Local020Entry
import QuantumNLS.Local020Mul2

/-! LOCAL-020 stage S4: reflection.

`W f (x) = J f(L - x)` (`J = diag(1,-1)`) on `H2 L`, an involutive linear isometric equivalence.  For `u' x = u (L - x)`
(the interval representative of `Ru`) one has `𝓛_{u'} W = - W 𝓛_u` on the graph level (`ε = -1`, `c = 0`, same parity),
`W χ_{n,0} = (-1)^n χ_{-n,0}`, `W χ_{n,1} = -(-1)^n χ_{-n,1}`, hence `B_{-n}(Ru) = -J B_n(u) J` and
`b_{-n}(Ru) = b_n(u)`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Topology QuantumNLS.LocalSpectral QuantumNLS.Local020Abs QuantumNLS.Local020Mul1
open scoped ENNReal

namespace QuantumNLS.Local020Refl

variable {L κ : ℝ}

theorem refl_mp (hL : 0 ≤ L) : MeasurePreserving (fun x : ℝ => L - x) (μI L) (μI L) := by
  have h1 := ((volume : Measure ℝ).measurePreserving_sub_left L).restrict_preimage
    (measurableSet_Ioc (a := (0 : ℝ)) (b := L))
  have h2 : (fun x : ℝ => L - x) ⁻¹' Ioc 0 L = Ico 0 L := by
    ext x; simp only [mem_preimage, mem_Ioc, mem_Ico]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [h2] at h1
  unfold μI
  have h3 : (volume : Measure ℝ).restrict (Ico 0 L) = (volume : Measure ℝ).restrict (Ioc 0 L) :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  rw [h3] at h1
  exact h1

/-- Composition with `x ↦ L - x`. -/
def reflLI (hL : 0 ≤ L) : H2 L →ₗᵢ[ℂ] H2 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => L - x) (refl_mp hL)

theorem reflLI_ae (hL : 0 ≤ L) (f : H2 L) :
    (reflLI hL f : ℝ → E2) =ᵐ[μI L] fun x => (f : ℝ → E2) (L - x) :=
  Lp.coeFn_compMeasurePreserving f (refl_mp hL)

theorem reflLI_invol (hL : 0 ≤ L) (f : H2 L) : reflLI hL (reflLI hL f) = f := by
  apply Lp.ext
  have h1 := reflLI_ae hL (reflLI hL f)
  have h2 := (refl_mp hL).quasiMeasurePreserving.ae_eq_comp (reflLI_ae hL f)
  filter_upwards [h1, h2] with x a b
  rw [a]
  have : (fun y : ℝ => (reflLI hL f : ℝ → E2) y) ∘ (fun y : ℝ => L - y) = _ := rfl
  simp only [Function.comp] at b
  rw [b]
  simp

def reflE (hL : 0 ≤ L) : H2 L ≃ₗᵢ[ℂ] H2 L :=
  LinearIsometryEquiv.ofSurjective (reflLI hL) (fun g => ⟨reflLI hL g, reflLI_invol hL g⟩)

theorem reflE_ae (hL : 0 ≤ L) (f : H2 L) :
    (reflE hL f : ℝ → E2) =ᵐ[μI L] fun x => (f : ℝ → E2) (L - x) :=
  reflLI_ae hL f

/-- Reflection preserves `H¹` representatives (with `h ↦ -h(L-·)`). -/
theorem isH1Rep_refl (hL : 0 < L) {f : H2 L} {g h : ℝ → E2} (hrep : IsH1Rep L f g h) :
    IsH1Rep L (reflE hL.le f) (fun x => g (L - x)) (fun x => -(h (L - x))) := by
  refine ⟨?_, ?_, ?_⟩
  · have h2 := (refl_mp hL.le).quasiMeasurePreserving.ae_eq_comp hrep.1
    filter_upwards [reflE_ae hL.le f, h2] with x a b
    rw [a]; exact b
  · exact (hrep.2.1.comp_measurePreserving (refl_mp hL.le)).neg
  · intro x hx
    have hi := rep_intervalIntegrable hL.le hrep
    have h0 : IntervalIntegrable h volume 0 (L - x) := hi.mono_set (by
      rw [uIcc_of_le hL.le, uIcc_of_le (by linarith [hx.2])]; exact Icc_subset_Icc_right (by linarith [hx.1]))
    have h1 : IntervalIntegrable h volume (L - x) L := hi.mono_set (by
      rw [uIcc_of_le hL.le, uIcc_of_le (by linarith [hx.1])]
      exact Icc_subset_Icc (by linarith [hx.2]) le_rfl)
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left (fun t => h t) L]
    have e1 := hrep.2.2 (L - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have e2 := hrep.2.2 L ⟨hL.le, le_rfl⟩
    have e3 := intervalIntegral.integral_interval_sub_left hi h0
    simp only [sub_zero, sub_sub_cancel] at e3 ⊢
    rw [e1, e2, ← e3]
    abel

/-! ### The constant matrices `J`, `0` and the operator `W = J ∘ refl` -/

def cA : ℝ → ℂ := fun _ => 1
def cB : ℝ → ℂ := fun _ => -1
def cZ : ℝ → ℂ := fun _ => 0

theorem unitDiag_J : UnitDiag cA cB :=
  ⟨continuous_const, continuous_const, fun _ => by simp [cA], fun _ => by simp [cB]⟩

def Wr (hL : 0 < L) : H2 L ≃ₗᵢ[ℂ] H2 L := (reflE hL.le).trans (mulU unitDiag_J)

theorem Wr_ae (hL : 0 < L) (f : H2 L) :
    (Wr hL f : ℝ → E2) =ᵐ[μI L] fun x => Jm ((f : ℝ → E2) (L - x)) := by
  filter_upwards [mulU_ae unitDiag_J (reflE hL.le f), reflE_ae hL.le f] with x h1 h2
  show (mulU unitDiag_J (reflE hL.le f) : ℝ → E2) x = _
  rw [h1, h2, dmat_eq]
  ext i; fin_cases i <;> simp [cA, cB, Jm, vec2]

theorem Wr_Wr (hL : 0 < L) (f : H2 L) : Wr hL (Wr hL f) = f := by
  apply Lp.ext
  filter_upwards [Wr_ae hL (Wr hL f), (refl_mp hL.le).quasiMeasurePreserving.ae_eq_comp (Wr_ae hL f)] with x a b
  rw [a]
  simp only [Function.comp] at b
  rw [b]
  simp only [sub_sub_cancel]
  ext i; fin_cases i <;> simp [Jm, vec2]

theorem lopPt_J (κ : ℝ) (w : ℂ) (d g : E2) :
    lopPt κ w (Jm (-d)) (Jm g) = -(Jm (lopPt κ w d g)) := by
  unfold lopPt Jm
  ext i; fin_cases i
  · simp [vec2]; ring
  · simp [vec2]

theorem lopPt_neg (κ : ℝ) (w : ℂ) (d g : E2) : lopPt κ w (-d) (-g) = -(lopPt κ w d g) := by
  unfold lopPt Jm
  ext i; fin_cases i <;> simp [vec2] <;> ring

theorem sq_unit (σ : ℤˣ) : ((σ : ℤ) : ℂ) * ((σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or σ with h | h <;> simp [h]

theorem LuGraph_neg {u : ℝ → ℂ} {σ : ℤˣ} {f φ : H2 L} (h : (f, φ) ∈ LuGraph L κ u σ) :
    (-f, -φ) ∈ LuGraph L κ u σ := by
  obtain ⟨g, d, hrep, hbc, hφ⟩ := h
  refine ⟨fun x => -(g x), fun x => -(d x), ⟨?_, hrep.2.1.neg, ?_⟩, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_neg f, hrep.1] with x a b
    rw [a, Pi.neg_apply, b]
  · intro x hx
    have := hrep.2.2 x hx
    simp only [intervalIntegral.integral_neg]
    rw [this, neg_add]
  · simp only [hbc, smul_neg]
  · filter_upwards [Lp.coeFn_neg φ, hφ] with x a b
    rw [a, Pi.neg_apply, b, lopPt_neg]

theorem fwd (hL : 0 < L) (u : ℝ → ℂ) (σ : ℤˣ) {f φ : H2 L} (h : (f, φ) ∈ LuGraph L κ u σ) :
    (Wr hL f, -(Wr hL φ)) ∈ LuGraph L κ (fun x => u (L - x)) σ := by
  obtain ⟨g, d, hrep, hbc, hφ⟩ := h
  have hr := isH1Rep_refl hL hrep
  have hm := isH1Rep_mul hL hr unitDiag_J (α' := cZ) (β' := cZ) (fun x => hasDerivAt_const x _)
    (fun x => hasDerivAt_const x _) continuous_const continuous_const
  refine ⟨_, _, hm, ?_, ?_⟩
  · simp only [dmat_eq, cA, cB, sub_self, sub_zero, vec2]
    rw [hbc]
    have hs := sq_unit σ
    ext i; fin_cases i
    · simp [vec2]; linear_combination (-(g 0).ofLp 0) * hs
    · simp [vec2]; linear_combination (-(g 0).ofLp 1) * hs
  · have hb := (refl_mp hL.le).quasiMeasurePreserving.ae_eq_comp hφ
    filter_upwards [Lp.coeFn_neg (Wr hL φ), Wr_ae hL φ, hb] with x a b c
    rw [a, Pi.neg_apply, b]
    simp only [Function.comp] at c
    rw [c]
    have hz : dmat cZ cZ x (g (L - x)) = 0 := by
      rw [dmat_eq]; ext i; fin_cases i <;> simp [cZ, vec2]
    have e1 : dmat cA cB x (-d (L - x)) = Jm (-d (L - x)) := by
      rw [dmat_eq]; ext i; fin_cases i <;> simp [cA, cB, Jm, vec2]
    have e2 : dmat cA cB x (g (L - x)) = Jm (g (L - x)) := by
      rw [dmat_eq]; ext i; fin_cases i <;> simp [cA, cB, Jm, vec2]
    rw [hz, add_zero, e1, e2, lopPt_J]

theorem pm_neg' (n : ℤ) : pm L (-n) = -pm L n := by unfold pm; push_cast; ring

theorem parity_neg' (n : ℤ) : parity (-n) = parity n := by
  unfold parity; simp [even_neg]

theorem rate_neg (n : ℤ) (j : Fin 2) : rate L (-n) j = -rate L n j := by
  unfold rate; rw [pm_neg']; push_cast; ring

theorem chiFun_refl (hL : 0 < L) (n : ℤ) (j : Fin 2) (x : ℝ) :
    Jm (chiFun L n j (L - x)) =
      (((if j = 0 then 1 else -1 : ℂ)) * (((parity n : ℤˣ) : ℤ) : ℂ)) • chiFun L (-n) j x := by
  have hE := cexp_rate_L hL.ne' n j
  have e : Complex.exp (rate L n j * ((L - x : ℝ) : ℂ)) =
      (((parity n : ℤˣ) : ℤ) : ℂ) * Complex.exp (rate L (-n) j * (x : ℂ)) := by
    rw [← hE, ← Complex.exp_add, rate_neg]; congr 1; push_cast; ring
  unfold chiFun
  fin_cases j
  · ext i; fin_cases i
    · simp [Jm, vec2, EuclideanSpace.single_apply]
      push_cast at e
      first | (rw [e]; ring) | (simp only [Fin.zero_eta, Fin.mk_one] at e; rw [e]; ring)
    · simp [Jm, vec2, EuclideanSpace.single_apply]
  · ext i; fin_cases i
    · simp [Jm, vec2, EuclideanSpace.single_apply]
    · simp [Jm, vec2, EuclideanSpace.single_apply]
      push_cast at e
      first | (rw [e]; ring) | (simp only [Fin.zero_eta, Fin.mk_one] at e; rw [e]; ring)

theorem Wr_chi (hL : 0 < L) (n : ℤ) (j : Fin 2) :
    Wr hL (chi L n j) =
      (((if j = 0 then 1 else -1 : ℂ)) * (((parity n : ℤˣ) : ℤ) : ℂ)) • chi L (-n) j := by
  apply Lp.ext
  have hb := (refl_mp hL.le).quasiMeasurePreserving.ae_eq_comp (memLp_chiFun L n j).coeFn_toLp
  filter_upwards [Wr_ae hL (chi L n j), hb,
    Lp.coeFn_smul (((if j = 0 then 1 else -1 : ℂ)) * (((parity n : ℤˣ) : ℤ) : ℂ)) (chi L (-n) j),
    (memLp_chiFun L (-n) j).coeFn_toLp] with x a b c d
  rw [a, c, Pi.smul_apply]
  simp only [Function.comp] at b
  have d' : (chi L (-n) j : ℝ → E2) x = chiFun L (-n) j x := d
  have b' : (chi L n j : ℝ → E2) (L - x) = chiFun L n j (L - x) := b
  rw [b', d', chiFun_refl hL]

theorem inter_refl (hL : 0 < L) (u : ℝ → ℂ) (σ : ℤˣ) :
    Inter (LuGraph L κ u σ) (LuGraph L κ (fun x => u (L - x)) σ) (Wr hL) (-1) 0 := by
  have hdd : ∀ (v : ℝ → ℂ), (fun x => (fun y => v (L - y)) (L - x)) = v := by
    intro v; funext x; simp
  refine ⟨by norm_num, fun f φ => ⟨fun h => ?_, fun h => ?_⟩, fun f φ h => ?_⟩
  · have := fwd hL u σ h
    simpa using this
  · have h1 : (Wr hL f, -(Wr hL φ)) ∈ LuGraph L κ (fun x => u (L - x)) σ := by simpa using h
    have h2 := fwd hL _ σ h1
    rw [hdd, Wr_Wr] at h2
    have h3 : -(Wr hL (-(Wr hL φ))) = φ := by rw [map_neg, Wr_Wr, neg_neg]
    rwa [h3] at h2
  · have := LuGraph_neg h
    simpa using this

/-- `M = diag(s, -s)`, `s = (-1)^n`. -/
def Mr (n : ℤ) : E2 ≃ₗᵢ[ℂ] E2 :=
  QuantumNLS.Local020Mul2.diagLI (fun _ => (((parity n : ℤˣ) : ℤ) : ℂ))
    (fun _ => -(((parity n : ℤˣ) : ℤ) : ℂ))
    ⟨continuous_const, continuous_const, fun _ => by rcases Int.units_eq_one_or (parity n) with h | h <;> simp [h],
      fun _ => by rcases Int.units_eq_one_or (parity n) with h | h <;> simp [h]⟩ 0

theorem Mr_apply (n : ℤ) (v : E2) :
    Mr n v = vec2 ((((parity n : ℤˣ) : ℤ) : ℂ) * v 0) (-(((parity n : ℤˣ) : ℤ) : ℂ) * v 1) :=
  (QuantumNLS.Local020Mul2.diagLI_apply _ _ _ 0 v).trans (dmat_eq _ _ 0 v)

theorem doublet_rel (hL : 0 < L) (n : ℤ) :
    QuantumNLS.Local020Core.DoubletRel (L := L) (Wr hL) (Mr n) n (-n) := by
  unfold QuantumNLS.Local020Core.DoubletRel
  ext v : 1
  simp only [ContinuousLinearMap.comp_apply, ic_apply]
  rw [embed_apply, embed_apply, map_add, map_smul, map_smul, Wr_chi, Wr_chi, Mr_apply]
  simp only [vec2_zero, vec2_one, if_true, one_ne_zero, if_false, smul_smul]
  congr 2 <;> ring

/-- **S4 (reflection).**  For `u' x = u (L - x)`: `b_{-n}(u') = b_n(u)`, and `SmallCompression` is transported. -/
theorem refl_reduced (hL : 0 < L) (n : ℤ) (r : ℝ) (u : ℝ → ℂ) :
    (SmallCompression L κ (fun x => u (L - x)) (-n) r ↔ SmallCompression L κ u n r) ∧
    ∀ (h' : SmallCompression L κ (fun x => u (L - x)) (-n) r) (hh : SmallCompression L κ u n r),
      QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ (fun x => u (L - x)) (-n) r h') =
        QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ u n r hh) := by
  have h : Inter (LuGraph L κ u (parity n)) (LuGraph L κ (fun x => u (L - x)) (parity (-n))) (Wr hL) (-1) 0 := by
    rw [parity_neg' n]; exact inter_refl hL u (parity n)
  have hn : center L (-n) = 0 + (-1) * center L n := by
    unfold QuantumNLS.LocalSpectral.center; rw [pm_neg']; push_cast; ring
  obtain ⟨hs, hr⟩ := QuantumNLS.Local020Core.reduced_transport (κ := κ) r h (Or.inr rfl) hn
    (doublet_rel hL n)
  refine ⟨hs, fun h' hh => ?_⟩
  have hB := hr h' hh
  have hs0 : starRingEnd ℂ (((parity n : ℤˣ) : ℤ) : ℂ) * (((parity n : ℤˣ) : ℤ) : ℂ) = 1 := by
    rw [map_intCast]; exact sq_unit _
  have hc := QuantumNLS.Local020Entry.bentry_transport (Mr n) _ _ (Mr_apply n) hs0 (-1) _ _ hB
  rw [hc]
  rw [map_intCast]
  have := sq_unit (parity n)
  linear_combination (QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ u n r hh)) * this

end QuantumNLS.Local020Refl

#print axioms QuantumNLS.Local020Refl.refl_reduced
#print axioms QuantumNLS.Local020Refl.inter_refl
