import QuantumNLS.Q07UniformDifferentialsR16

/-! The source rectangular contour functional and the integral of its actual
logarithm Hessian. The latter has the printed a^(r+1) scaling. Equality with
the second differential of the former requires the remaining interchange step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Metric
namespace QuantumNLS.Q07IntegratedHessiansR16
open PhysicalTensor (L2T)
open Q07LogDifferentialsR16
open ResolventNeighborhood (GammaN)
variable {L κ : ℝ} [Fact (0 < L)]

def windowContour (hκ : 0 < κ) (r : ℕ) (a h : ℝ) (u : L2T L) : ℝ :=
  ContourPrefactor.contourFunctional κ a h (fun z => z^r*logarithm hκ z u)

def integratedSecond (hκ : 0 < κ) (r : ℕ) (a h : ℝ) (u v w : L2T L) : ℝ :=
  ContourPrefactor.contourFunctional κ a h (fun z => z^r*second (logarithm hκ z) u v w)

theorem norm_le_of_GammaN {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) {z : ℂ}
    (hz : z ∈ GammaN a h) : ‖z‖ ≤ a+h := by
  have hi := NonvanishingD.GammaN_im_abs hh hz
  have hr : |z.re| ≤ a := by
    rcases hz with ⟨hre,-⟩ | ⟨-,hre⟩
    · rcases hre with hre | hre <;> simp [hre, abs_of_nonneg ha]
    · exact hre
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hr hi)

/-- Integration of the proved actual logarithm Hessian has exactly the
source polynomial growth, uniformly on a fixed full physical neighborhood. -/
theorem uniform_integrated_log_hessians (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) (r : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ l : ℕ, l0 ≤ l → 1 ≤ PROP017UniformN.cutSeq L l ∧
        ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
          ∀ v : L2T L, ‖v-u‖ < δ → ∀ w q : L2T L,
            |integratedSecond hκ r (PROP017UniformN.cutSeq L l) h v w q| ≤
              C*(PROP017UniformN.cutSeq L l)^(r+1)*‖w‖*‖q‖ := by
  obtain ⟨δ,hδ,l0,C0,hC0,hb⟩ := Q07UniformDifferentialsR16.uniform_log_hessians (L := L) hκ hs B hh
  obtain ⟨n,hn⟩ := exists_nat_gt L
  let K := 1/(2*Real.pi*κ)
  let C := K*4*(1+h)^(r+1)*C0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨δ,hδ,max l0 n,C,hC,?_⟩
  intro l hl
  have hl0 := le_trans (le_max_left l0 n) hl
  have hnl := le_trans (le_max_right l0 n) hl
  let a := PROP017UniformN.cutSeq L l
  have ha : 1 ≤ a := by
    dsimp [a, PROP017UniformN.cutSeq]
    apply (le_div_iff₀ (Fact.out : 0 < L)).mpr
    have hnL : L < (l : ℝ) := hn.trans_le (by exact_mod_cast hnl)
    have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hlp : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    nlinarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  refine ⟨ha,?_⟩
  intro u hu v hv w q
  have hM : 0 ≤ (1+h)^r*a^r*C0*‖w‖*‖q‖ := by positivity
  have hi : ∀ z ∈ GammaN a h, ‖z^r*second (logarithm hκ z) v w q‖ ≤
      (1+h)^r*a^r*C0*‖w‖*‖q‖ := by
    intro z hz
    have hH := (hb l hl0 u hu v hv z hz).2 w q
    have hza : ‖z‖ ≤ (1+h)*a := (norm_le_of_GammaN (by linarith) hh.le hz).trans (by nlinarith)
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ((1+h)*a)^r*(C0*‖w‖*‖q‖) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hint := ContourPrefactor.abs_contourFunctional_le
    (fun z => z^r*second (logarithm hκ z) v w q) hκ.ne' (by linarith : 0 ≤ a) hh.le hM hi
  rw [abs_of_pos hκ] at hint
  change |integratedSecond hκ r a h v w q| ≤ C*a^(r+1)*‖w‖*‖q‖
  refine hint.trans ?_
  change K*(4*(a+h)*((1+h)^r*a^r*C0*‖w‖*‖q‖)) ≤ _
  calc
    _ ≤ K*(4*((1+h)*a)*((1+h)^r*a^r*C0*‖w‖*‖q‖)) := by
      gcongr
      nlinarith
    _ = C*a^(r+1)*‖w‖*‖q‖ := by
      dsimp [C]
      rw [pow_succ, pow_succ]
      ring

end QuantumNLS.Q07IntegratedHessiansR16
