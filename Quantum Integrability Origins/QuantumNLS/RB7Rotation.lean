import Mathlib
import QuantumNLS.RB7Final

/-!
# R-7B122087 `thm:hierarchy`, clause (3): constant-action rotations in the chart coordinates (RB7Rotation)

Printed: "In the new coordinates they are constant-action rotations" (with the proof: `z_j(t) = e^{-i t ω_{r,j}(z)} z_j`, the active frequencies are constant on each full modulus torus).

For the chart data `C` (`ChartFacts`, coordinates `Φ`) and the order `r`, `F_r = Fd hR C r : h^{S_r} → ℝ` (`C²`, rotation invariant, `F_r (Φ f) = Re I_{r+1}(f)` for smooth `f`):

* `FreqSeq S F a n`: the coordinate frequency `ω_n(a) = freq F a n = Re(conj a_n ∇_n F(a))/|a_n|²` of a sequence `a ∈ h^S` (`0` if `a ∉ h^S`).
* `Fd_charge`: `F_r(Φ f) = Re charge L κ f (r+1)` for smooth periodic `f` (the identification of the sequence-side functional with the physical Hamiltonian).
* `coords_chartFlow` / `rotation_form`: for EVERY `HierarchyFlow.IsHamFlow` `Ψ'` of `hamiltonian L κ r` (by uniqueness it is the chart flow) and smooth `u`:
  `Φ_n(Ψ'_s u) = exp(-i s ω_{r,n}(Φ u)) Φ_n(u)`.
* `norm_rotation_form`: the moduli `|Φ_n|` are constant (constant action); `freq_flow_const`: every order's coordinate frequency `ω_{r',n}` is constant along every flow line;
  `omegaOf_congr`: frequencies are constant on full modulus tori (invariance under coordinatewise rotations).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.HierarchyFlow QuantumNLS.LossSobolev

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

open Classical in
/-- The coordinate frequency `ω_n(a) = Re(conj a_n ∇_n F(a))/|a_n|²` of a sequence `a ∈ h^S` (`0` if `a ∉ h^S`). -/
def FreqSeq (S : ℝ) (F : h02 L S → ℝ) (a : ℤ → ℂ) (n : ℤ) : ℝ :=
  if h : MemHs L S a then freq F (h02.ofMem h) n else 0

theorem FreqSeq_eq {S : ℝ} (F : h02 L S → ℝ) (z : h02 L S) (a : ℤ → ℂ) (hz : z.val = a) (n : ℤ) :
    FreqSeq S F a n = freq F z n := by
  subst hz
  have hm : MemHs L S z.val := z.summable
  unfold FreqSeq
  rw [dite_eq_left_of_eq_true (eq_true hm)]
  have : h02.ofMem hm = z := WSeq.ext rfl
  rw [this]

/-- The coordinates of a smooth profile at level `S_r`. -/
def zS (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) : h02 L ((SOf r : ℝ≥0) : ℝ) :=
  h02.ofMem (hinf_all hR C hu ((SOf r : ℝ≥0) : ℝ))

theorem zS_val (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) : (zS hR C r hu).val = fun n => C.Φ (smoothL2 hu) n := rfl

/-- The order-`r` frequency of a smooth profile. -/
def omegaOf (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (n : ℤ) : ℝ :=
  (sdata hR C r ((SOf r : ℝ≥0) : ℝ) le_rfl).D.Ω () (zS hR C r hu) n

theorem omegaOf_eq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (n : ℤ) :
    omegaOf hR C r hu n = freq (Fd hR C r) (zS hR C r hu) n := by
  unfold omegaOf
  rw [SeqData.D_Ω]
  have : (sdata hR C r ((SOf r : ℝ≥0) : ℝ) le_rfl).down () (zS hR C r hu) = zS hR C r hu := WSeq.ext rfl
  rw [this]
  rfl

theorem omegaOf_eq_FreqSeq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) (n : ℤ) :
    omegaOf hR C r hu n =
      FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fd hR C r) (fun m => C.Φ (smoothL2 hu) m) n :=
  (omegaOf_eq hR C r hu n).trans (FreqSeq_eq _ _ _ rfl n).symm

/-- `F_r(Φ f) = Re I_{r+1}(f)` for smooth periodic `f`. -/
theorem Fd_charge (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) : Fd hR C r (zS hR C r hf) = (charge L κ f (r + 1)).re := by
  have hm := memHs_of_smooth hf ((qOf r : ℝ≥0) : ℝ)
  rw [← IOf_char hR C r f hf hm]
  unfold Fd
  congr 1
  apply WField.ext
  refine (emb_val' (L := L) (qS_le r) (gOf hR C (SOf r) (zS hR C r hf))).trans ?_
  refine (gOf_val hR C (SOf r) (zS hR C r hf)).trans ?_
  have : toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 (zS hR C r hf) = C.Φ (smoothL2 hf) :=
    lp.ext (funext fun n => toBase_apply (L := L) _ (SOf r).2 _ n)
  rw [this, C.ΨΦ]
  rfl

/-- The coordinates of a flow-line of the chart flow of order `r`. -/
theorem zflow_coord (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (s : ℝ)
    (z : h02 L ((SOf r : ℝ≥0) : ℝ)) (n : ℤ) :
    (zflow hR C r _ le_rfl s z).val n =
      Complex.exp (((-(s * (sdata hR C r ((SOf r : ℝ≥0) : ℝ) le_rfl).D.Ω () z n) : ℝ) : ℂ) * Complex.I) *
        z.val n := by
  unfold zflow
  rw [flow_val]
  simp only [angle, Pi.smul_apply, smul_eq_mul, one1, mul_one, Finset.univ_unique, Finset.sum_singleton]

theorem coords_chartFlow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hf : SmoothPeriodic L (chartFlow hR C r s u)) (n : ℤ) :
    (C.Φ (smoothL2 hf) : ℤ → ℂ) n =
      Complex.exp (((-(s * omegaOf hR C r hu n) : ℝ) : ℂ) * Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n := by
  obtain ⟨hf', hfe⟩ := physFlow_slice hR C r hu s
  have h2 : (fun n => C.Φ (smoothL2 hf') n) = (zflow hR C r _ le_rfl s (zS hR C r hu)).val := by
    rw [hfe]
    funext n
    have := congrArg (fun z : lp (fun _ : ℤ => ℂ) 2 => (z : ℤ → ℂ) n) (Phi_curve hR C r u s)
    simp only at this
    rw [this, toBase_curve hR C r hu s]
    exact toBase_apply (L := L) _ (SOf r).2 _ n
  have h3 : smoothL2 hf = smoothL2 hf' := smoothL2_congr rfl hf hf'
  rw [h3]
  have h4 := congrFun h2 n
  simp only at h4
  rw [h4, zflow_coord]
  rfl

/-- **Rotation form** for every Hamiltonian flow of order `r` (uniqueness). -/
theorem rotation_form (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ) :
    (C.Φ (smoothL2 hs) : ℤ → ℂ) n =
      Complex.exp (((-(s * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fd hR C r) (fun m => C.Φ (smoothL2 hu) m) n) : ℝ) : ℂ) *
        Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n := by
  have he : Ψ' s u = chartFlow hR C r s u := isHamFlow_eq hR C r hΨ hu s
  have hs' : SmoothPeriodic L (chartFlow hR C r s u) := he ▸ hs
  have h3 : smoothL2 hs = smoothL2 hs' := smoothL2_congr he hs hs'
  rw [h3, coords_chartFlow hR C r hu s hs' n, omegaOf_eq_FreqSeq]

theorem norm_rotation_form (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ) :
    ‖(C.Φ (smoothL2 hs) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hu) : ℤ → ℂ) n‖ := by
  rw [rotation_form hR C r hΨ hu s hs n, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Frequencies are constant on full modulus tori (rotation invariance of `F_r`). -/
theorem omegaOf_congr (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {u v : ℝ → ℂ} (hu : SmoothPeriodic L u) (hv : SmoothPeriodic L v) (c : ℤ → Circle)
    (h : ∀ n, (C.Φ (smoothL2 hv) : ℤ → ℂ) n = (c n : ℂ) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n) (n : ℤ) :
    omegaOf hR C r hv n = omegaOf hR C r hu n := by
  have : zS hR C r hv = rot c (zS hR C r hu) := WSeq.ext (funext fun m => by rw [rot_val]; exact h m)
  unfold omegaOf
  rw [this]
  exact (sdata hR C r ((SOf r : ℝ≥0) : ℝ) le_rfl).D.inv () c _ n

theorem circle_exp_coe (a : ℝ) : ((Circle.exp a : Circle) : ℂ) = Complex.exp ((a : ℂ) * Complex.I) := by
  simp [Circle.coe_exp]

/-- Every order's frequency is constant along every flow line of every order. -/
theorem omegaOf_chartFlow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r r' : ℕ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hf : SmoothPeriodic L (chartFlow hR C r s u)) (n : ℤ) :
    omegaOf hR C r' hf n = omegaOf hR C r' hu n := by
  refine omegaOf_congr hR C r' hu hf (fun m => Circle.exp (-(s * omegaOf hR C r hu m))) ?_ n
  intro m
  rw [coords_chartFlow hR C r hu s hf m, circle_exp_coe]

theorem freq_flow_const (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r r' : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ) :
    FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fd hR C r') (fun m => C.Φ (smoothL2 hs) m) n =
      FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fd hR C r') (fun m => C.Φ (smoothL2 hu) m) n := by
  have he : Ψ' s u = chartFlow hR C r s u := isHamFlow_eq hR C r hΨ hu s
  have hs' : SmoothPeriodic L (chartFlow hR C r s u) := he ▸ hs
  have h3 : smoothL2 hs = smoothL2 hs' := smoothL2_congr he hs hs'
  have := omegaOf_chartFlow hR C r r' hu s hs' n
  rw [omegaOf_eq_FreqSeq, omegaOf_eq_FreqSeq] at this
  rw [h3]
  exact this

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.FreqSeq_eq
#print axioms QuantumNLS.RB7.omegaOf_eq_FreqSeq
#print axioms QuantumNLS.RB7.Fd_charge
#print axioms QuantumNLS.RB7.coords_chartFlow
#print axioms QuantumNLS.RB7.rotation_form
#print axioms QuantumNLS.RB7.norm_rotation_form
#print axioms QuantumNLS.RB7.omegaOf_congr
#print axioms QuantumNLS.RB7.freq_flow_const
