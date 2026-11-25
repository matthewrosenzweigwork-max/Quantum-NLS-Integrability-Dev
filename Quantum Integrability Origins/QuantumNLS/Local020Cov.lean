import Mathlib
import QuantumNLS.Local007Final
import QuantumNLS.Local020Rep
import QuantumNLS.Local020Trans2
import QuantumNLS.Local020Ent2
import QuantumNLS.Local020Cong
import QuantumNLS.Local020Scale

/-! LOCAL-020: covariance of the LOCAL-003/LOCAL-007 reduction data `(a_n, b_n)` (the entries of the polar-normalized
reduced matrix `B_n(u) = [[a_n, conj b_n],[b_n, a_n]]`) under translation, boost, reflection, conjugation, common phase
and scaling, in terms of the printed `Pkg` conjunction. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local020Trans2 QuantumNLS.Local020Entry QuantumNLS.Local020Ent2 QuantumNLS.Local020Mul2
open QuantumNLS.Local007Final (Pkg gcoef)

namespace QuantumNLS.Local020Cov

variable {L κ r ρ C : ℝ} [Fact (0 < L)]
variable {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ}

theorem sc_of_pkg {n : ℤ} (hP : Pkg L κ r ρ C n (a n) (b n)) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) :
    SmallCompression L κ (circleRep u) n r := hP.2.2.1 u hu

theorem ent_of_pkg {n : ℤ} (hP : Pkg L κ r ρ C n (a n) (b n)) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ)
    (h : SmallCompression L κ (circleRep u) n r) :
    aentry (reducedMatrix2 L κ (circleRep u) n r h) = ((a n u : ℝ) : ℂ) ∧
      bentry (reducedMatrix2 L κ (circleRep u) n r h) = b n u := by
  have := hP.2.2.2.1 u hu h (vec2 1 0)
  refine ⟨?_, ?_⟩
  · unfold aentry; rw [this]; simp [vec2]
  · unfold bentry; rw [this]; simp [vec2]

/-- Transfer through a relation `Rel` between the interval potentials. -/
theorem b_of_rel {m n : ℤ} (hPm : Pkg L κ r ρ C m (a m) (b m)) (hPn : Pkg L κ r ρ C n (a n) (b n))
    {u v : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (hv : v ∈ ball (0 : L2T L) ρ) {v0 : ℝ → ℂ}
    (hae : circleRep v =ᵐ[μI L] v0) {c : ℂ} (hrel : Rel L κ r n m v0 (circleRep u) c) :
    b n v = c * b m u := by
  have h1 := sc_of_pkg hPn hv
  have h2 := sc_of_pkg hPm hu
  have h3 : SmallCompression L κ v0 n r := (QuantumNLS.Local020Cong.smallCompression_congr hae n r).1 h1
  rw [← (ent_of_pkg hPn hv h1).2, ← (ent_of_pkg hPm hu h2).2,
    QuantumNLS.Local020Cong.reducedMatrix2_congr hae n r h1 h3]
  exact hrel.2 h3 h2

/-- Boost to an arbitrary index shift: `b_n(e^{ip_k x} u) = b_{n-k}(u)`. -/
theorem rel_boostk (hL : 0 < L) (n k : ℤ) (u0 : ℝ → ℂ) :
    Rel L κ r n (n - k) (upb 0 (pm L k / 2) u0) u0 1 := by
  obtain ⟨h1, h2⟩ := phaseBoost_reduced (κ := κ) hL 0 k (n - k) r u0
  have key : ∀ m : ℤ, m = (n - k) + k → Rel L κ r m (n - k) (upb 0 (pm L k / 2) u0) u0 1 := by
    intro m hm
    subst hm
    refine ⟨h1, fun h' hh => ?_⟩
    rw [h2 h' hh]
    simp
  exact key n (sub_add_cancel n k).symm

theorem cov_phase (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (φ : ℝ) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ)
    (n : ℤ) :
    b n (Complex.exp ((φ : ℂ) * Complex.I) • u) = Complex.exp ((φ : ℂ) * Complex.I) * b n u := by
  have hL : 0 < L := Fact.out
  have hv : Complex.exp ((φ : ℂ) * Complex.I) • u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact mem_ball_zero_iff.1 hu
  have hrel := rel_phase (L := L) (κ := κ) (r := r) hL n (φ / 2) (circleRep u)
  have e : (((2 * (φ / 2) : ℝ)) : ℂ) = (φ : ℂ) := by push_cast; ring
  rw [e] at hrel
  exact b_of_rel (hP n) (hP n) hu hv (QuantumNLS.Local020Rep.circleRep_smul _ u) hrel

theorem cov_boost (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (k : ℤ) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ)
    (n : ℤ) : b n (QuantumNLS.RootMassBoostSymbol.boost k u) = b (n - k) u := by
  have hL : 0 < L := Fact.out
  have hv : QuantumNLS.RootMassBoostSymbol.boost k u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, QuantumNLS.RootMassBoostSymbol.norm_boost]; exact mem_ball_zero_iff.1 hu
  have := b_of_rel (hP (n - k)) (hP n) hu hv (QuantumNLS.Local020Rep.circleRep_boost k u)
    (rel_boostk (κ := κ) (r := r) hL n k (circleRep u))
  rw [this, one_mul]

theorem cov_trans (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (y : ℝ) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ)
    (n : ℤ) :
    b n (QuantumNLS.BornTranslation.trans y u) =
      Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * b n u := by
  have hL : 0 < L := Fact.out
  have hv : QuantumNLS.BornTranslation.trans y u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, LinearIsometry.norm_map]; exact mem_ball_zero_iff.1 hu
  exact b_of_rel (hP n) (hP n) hu hv (QuantumNLS.Local020Rep.circleRep_trans y u)
    (trans_reduced (κ := κ) (r := r) hL n y (circleRep u) (QuantumNLS.Local020Rep.circleRep_periodic u))

theorem cov_scale {κ' : ℝ} {ρ' C' : ℝ} {a' : ℤ → L2T L → ℝ} {b' : ℤ → L2T L → ℂ} {s : ℝ} (hs : 0 < s)
    (hκ : κ' = κ * s ^ 2) (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (hP' : ∀ n, Pkg L κ' r ρ' C' n (a' n) (b' n))
    {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ') (hsu : ((s : ℂ) • u) ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    b n ((s : ℂ) • u) = b' n u := by
  subst hκ
  have h1 := sc_of_pkg (hP n) hsu
  have h2 := sc_of_pkg (hP' n) hu
  have hae := QuantumNLS.Local020Rep.circleRep_smul (s : ℂ) u
  have h3 : SmallCompression L κ (fun x => (s : ℂ) * circleRep u x) n r :=
    (QuantumNLS.Local020Cong.smallCompression_congr hae n r).1 h1
  rw [← (ent_of_pkg (hP n) hsu h1).2, ← (ent_of_pkg (hP' n) hu h2).2,
    QuantumNLS.Local020Cong.reducedMatrix2_congr hae n r h1 h3,
    QuantumNLS.Local020Scale.reducedMatrix2_scale hs.le (circleRep u) n r h3 h2]

theorem cov_refl (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    b (-n) (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) = b n u ∧
      a (-n) (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) = -a n u := by
  have hL : 0 < L := Fact.out
  have hv : QuantumNLS.ResetNormalizationUniqueness.reflectR L u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, LinearIsometry.norm_map]; exact mem_ball_zero_iff.1 hu
  have hae := QuantumNLS.Local020Rep.circleRep_refl u
  have h1 := sc_of_pkg (hP (-n)) hv
  have h2 := sc_of_pkg (hP n) hu
  have h3 : SmallCompression L κ (fun x => circleRep u (L - x)) (-n) r :=
    (QuantumNLS.Local020Cong.smallCompression_congr hae (-n) r).1 h1
  have hE := QuantumNLS.Local020Cong.reducedMatrix2_congr hae (-n) r h1 h3
  obtain ⟨-, hb⟩ := QuantumNLS.Local020Refl.refl_reduced (κ := κ) hL n r (circleRep u)
  have ha := QuantumNLS.Local020Ent2.refl_reduced_a (κ := κ) hL n r (circleRep u) h3 h2
  obtain ⟨e1a, e1b⟩ := ent_of_pkg (hP (-n)) hv h1
  obtain ⟨e2a, e2b⟩ := ent_of_pkg (hP n) hu h2
  refine ⟨?_, ?_⟩
  · rw [← e1b, hE, hb h3 h2, e2b]
  · have : ((a (-n) (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) : ℝ) : ℂ) = ((-a n u : ℝ) : ℂ) := by
      rw [← e1a, hE, ha, e2a]; push_cast; ring
    exact_mod_cast this

theorem cov_conj (hP : ∀ n, Pkg L κ r ρ C n (a n) (b n)) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    b (-n) (star u) = -conj (b n u) ∧ a (-n) (star u) = -a n u := by
  have hL : 0 < L := Fact.out
  have hv : star u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, QuantumNLS.ResetNormalizationUniqueness.norm_cj]; exact mem_ball_zero_iff.1 hu
  have hae := QuantumNLS.Local020Rep.circleRep_star u
  have h1 := sc_of_pkg (hP (-n)) hv
  have h2 := sc_of_pkg (hP n) hu
  have h3 : SmallCompression L κ (fun x => conj (circleRep u x)) (-n) r :=
    (QuantumNLS.Local020Cong.smallCompression_congr hae (-n) r).1 h1
  have hE := QuantumNLS.Local020Cong.reducedMatrix2_congr hae (-n) r h1 h3
  obtain ⟨-, hb⟩ := QuantumNLS.Local020Conj.conj_reduced (κ := κ) hL n r (circleRep u)
  have ha := QuantumNLS.Local020Ent2.conj_reduced_a (κ := κ) hL n r (circleRep u) h3 h2
  obtain ⟨e1a, e1b⟩ := ent_of_pkg (hP (-n)) hv h1
  obtain ⟨e2a, e2b⟩ := ent_of_pkg (hP n) hu h2
  refine ⟨?_, ?_⟩
  · rw [← e1b, hE, hb h3 h2, e2b]
  · have : ((a (-n) (star u) : ℝ) : ℂ) = ((-a n u : ℝ) : ℂ) := by
      rw [← e1a, hE, ha, e2a, Complex.conj_ofReal]; push_cast; ring
    exact_mod_cast this

end QuantumNLS.Local020Cov

#print axioms QuantumNLS.Local020Cov.cov_refl
#print axioms QuantumNLS.Local020Cov.cov_conj
#print axioms QuantumNLS.Local020Cov.cov_scale
#print axioms QuantumNLS.Local020Cov.cov_trans
#print axioms QuantumNLS.Local020Cov.cov_boost
#print axioms QuantumNLS.Local020Cov.cov_phase
