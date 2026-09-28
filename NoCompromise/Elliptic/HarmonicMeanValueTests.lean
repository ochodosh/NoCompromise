import NoCompromise.Elliptic.InteriorH2Hessian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Compact radial tests for harmonic mean values

C¹ compact radial primitives approximate the quadratic tent on a ball.
Classical integration by parts and dominated convergence then prove that
the radial gradient moment of a harmonic function vanishes. This argument
uses no boundary area formula or geometric measure theory theorem.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Continuous slopes approaching the positive-halfline indicator. -/
def harmonicBallTentSlope (j : ℕ) (s : ℝ) : ℝ := min (max (((j : ℝ) + 1) * s) 0) 1

def harmonicBallTentPrimitive (j : ℕ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, harmonicBallTentSlope j t

lemma continuous_harmonicBallTentSlope (j : ℕ) : Continuous (harmonicBallTentSlope j) := by
  unfold harmonicBallTentSlope
  fun_prop

lemma harmonicBallTentSlope_mem_Icc (j : ℕ) (s : ℝ) :
    harmonicBallTentSlope j s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma harmonicBallTentSlope_eq_zero {j : ℕ} {s : ℝ} (hs : s ≤ 0) :
    harmonicBallTentSlope j s = 0 := by
  rw [harmonicBallTentSlope, max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs)]
  norm_num

lemma hasDerivAt_harmonicBallTentPrimitive (j : ℕ) (s : ℝ) :
    HasDerivAt (harmonicBallTentPrimitive j) (harmonicBallTentSlope j s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_harmonicBallTentSlope j).intervalIntegrable 0 s)
    (continuous_harmonicBallTentSlope j).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_harmonicBallTentSlope j).continuousAt

lemma contDiff_harmonicBallTentPrimitive (j : ℕ) :
    ContDiff ℝ 1 (harmonicBallTentPrimitive j) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun s => (harmonicBallTentSlope j s) • (1 : ℝ →L[ℝ] ℝ),
    (continuous_harmonicBallTentSlope j).smul continuous_const,
    fun s => ?_⟩
  convert! (hasDerivAt_harmonicBallTentPrimitive j s).hasFDerivAt using 1
  ext
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]

lemma harmonicBallTentPrimitive_eq_zero {j : ℕ} {s : ℝ} (hs : s ≤ 0) :
    harmonicBallTentPrimitive j s = 0 := by
  unfold harmonicBallTentPrimitive
  calc
    _ = ∫ _ in (0 : ℝ)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hs] at ht
      exact harmonicBallTentSlope_eq_zero ht.2
    _ = 0 := by simp

lemma tendsto_harmonicBallTentSlope_of_pos {s : ℝ} (hs : 0 < s) :
    Tendsto (fun j => harmonicBallTentSlope j s) atTop (𝓝 1) := by
  have h : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * s) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)).atTop_mul_const hs
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1 |>.filter_mono h] with j hj
  rw [harmonicBallTentSlope, max_eq_left (le_trans zero_le_one hj), min_eq_right hj]

lemma gradient_harmonicBallTent {n : ℕ} (j : ℕ)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => harmonicBallTentPrimitive j (r ^ 2 - ‖y - c‖ ^ 2)) x =
      (-2 * harmonicBallTentSlope j (r ^ 2 - ‖x - c‖ ^ 2)) • (x - c) := by
  have hnorm := (hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const c)
  have hd := (hasDerivAt_harmonicBallTentPrimitive j (r ^ 2 - ‖x - c‖ ^ 2)).comp_hasFDerivAt x
    (hnorm.const_sub (r ^ 2))
  simp only [Function.comp_def, id_eq] at hd
  change (toDual ℝ _).symm (fderiv ℝ _ x) = _
  rw [hd.fderiv]
  apply (toDual ℝ _).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, map_smul]
  ext z
  simp [innerSL_apply_apply]
  ring

lemma tsupport_harmonicBallTent_subset {n : ℕ} (j : ℕ)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    tsupport (fun y => harmonicBallTentPrimitive j (r ^ 2 - ‖y - c‖ ^ 2)) ⊆
      closedBall c r := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  by_contra hn
  have hd : r < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
  apply hx
  exact harmonicBallTentPrimitive_eq_zero (by nlinarith [norm_nonneg (x - c)])

lemma integral_harmonicBallTentSlope_inner_gradient_eq_zero {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r)
    (hh : ∀ x ∈ ball c r, laplacianN u x = 0) (j : ℕ) :
    (∫ x in ball c r, harmonicBallTentSlope j (r ^ 2 - ‖x - c‖ ^ 2) *
      inner ℝ (gradient u x) (x - c)) = 0 := by
  let ψ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => harmonicBallTentPrimitive j (r ^ 2 - ‖x - c‖ ^ 2)
  have hψ : ContDiff ℝ 1 ψ := (contDiff_harmonicBallTentPrimitive j).comp
    (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))
  have hcψ : HasCompactSupport ψ := (isCompact_closedBall c r).of_isClosed_subset
    (isClosed_tsupport ψ) (tsupport_harmonicBallTent_subset j c hr)
  have hzero : (∫ x, ψ x * laplacianN u x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    change ψ x * laplacianN u x = 0
    by_cases hx : x ∈ ball c r
    · rw [hh x hx, mul_zero]
    · have hd : r ≤ ‖x - c‖ := by simpa only [mem_ball, dist_eq_norm, not_lt] using hx
      have hp : ψ x = 0 := harmonicBallTentPrimitive_eq_zero
        (by nlinarith [norm_nonneg (x - c)])
      rw [hp, zero_mul]
  have hg := integral_mul_laplacianN hu hψ hcψ
  rw [hzero] at hg
  have he : (∫ x, inner ℝ (gradient ψ x) (gradient u x)) =
      -2 * ∫ x, harmonicBallTentSlope j (r ^ 2 - ‖x - c‖ ^ 2) *
        inner ℝ (gradient u x) (x - c) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    change inner ℝ (gradient (fun y => harmonicBallTentPrimitive j
      (r ^ 2 - ‖y - c‖ ^ 2)) x) (gradient u x) = _
    rw [gradient_harmonicBallTent, real_inner_smul_left]
    have hi : inner ℝ (x - c) (gradient u x) = inner ℝ (gradient u x) (x - c) :=
      real_inner_comm _ _
    rw [hi]
    ring
  rw [he] at hg
  have hb : (∫ x in ball c r, harmonicBallTentSlope j (r ^ 2 - ‖x - c‖ ^ 2) *
      inner ℝ (gradient u x) (x - c)) =
      ∫ x, harmonicBallTentSlope j (r ^ 2 - ‖x - c‖ ^ 2) *
        inner ℝ (gradient u x) (x - c) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hd : r ≤ ‖x - c‖ := by simpa only [mem_ball, dist_eq_norm, not_lt] using hx
    rw [harmonicBallTentSlope_eq_zero (by nlinarith [norm_nonneg (x - c)]), zero_mul]
  rw [hb]
  linarith

/-- A compact radial C¹ test proves the vanishing of the radial gradient
moment on any ball where the classical Laplacian vanishes. -/
theorem integral_ball_inner_gradient_sub_eq_zero {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hh : ∀ x ∈ ball c r, laplacianN u x = 0) :
    (∫ x in ball c r, inner ℝ (gradient u x) (x - c)) = 0 := by
  have hG : Continuous (gradient u) :=
    continuous_gradient_of_contDiff (hu.of_le (by norm_num))
  have hI : Continuous (fun x => inner ℝ (gradient u x) (x - c)) :=
    hG.inner (continuous_id.sub continuous_const)
  have hb : IntegrableOn (fun x => ‖inner ℝ (gradient u x) (x - c)‖) (ball c r) :=
    (hI.norm.continuousOn.integrableOn_compact
      (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  have ht : Tendsto (fun j => ∫ x in ball c r,
      harmonicBallTentSlope j (r ^ 2 - ‖x - c‖ ^ 2) * inner ℝ (gradient u x) (x - c))
      atTop (𝓝 (∫ x in ball c r, inner ℝ (gradient u x) (x - c))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖inner ℝ (gradient u x) (x - c)‖)
    · intro j
      exact (((continuous_harmonicBallTentSlope j).comp
        (continuous_const.sub ((continuous_id.sub continuous_const).norm.pow 2))).mul hI
        ).aestronglyMeasurable
    · exact hb
    · intro j
      filter_upwards [] with x
      rw [norm_mul, Real.norm_eq_abs (harmonicBallTentSlope j _),
        abs_of_nonneg (harmonicBallTentSlope_mem_Icc j _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (harmonicBallTentSlope_mem_Icc j _).2
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hd : ‖x - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hx
      have hp : 0 < r ^ 2 - ‖x - c‖ ^ 2 := by nlinarith [norm_nonneg (x - c)]
      simpa only [one_mul] using (tendsto_harmonicBallTentSlope_of_pos hp).mul_const
        (inner ℝ (gradient u x) (x - c))
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (∫ x in ball c r, inner ℝ (gradient u x) (x - c))) := by
    simpa only [integral_harmonicBallTentSlope_inner_gradient_eq_zero hu c hr.le hh] using ht
  exact tendsto_nhds_unique hz tendsto_const_nhds

end LiquidDrop
