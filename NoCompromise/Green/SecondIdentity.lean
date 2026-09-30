module

public import NoCompromise.Green.IdentityCapacity
public import NoCompromise.Capacity.FluxBoundaryW
public import NoCompromise.Elliptic.InteriorH2Mollification
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section

/-!
# The second Green identity on `B_R ∖ K` (`eq:green-second`)

For a compact regular `K ⊆ B_r` with `C¹` boundary, a `C¹` function `v` on `ℝ³` whose
distributional Laplacian is a bounded function vanishing off `K`, and a `C²` function `g`
harmonic off `K`, the second Green identity holds on `B_r ∖ K`:
the flux of `v ∇g - g ∇v` through the sphere equals its flux through `∂K`.
The function `v` need not be `C²` up to `∂K`; the proof mollifies `v`, applies the classical
Gauss–Green theorem on the annulus to `vₙ ∇g - g ∇vₙ`, and passes to the limit: the interior term
`∫ g Δvₙ` vanishes in the limit because `Δvₙ` is eventually zero at every point off `K`.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Convolution
namespace LiquidDrop

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The mollifier bumps, with outer radius `1/(n+2)`. -/
def greenBump (n : ℕ) : ContDiffBump (0 : E₃) where
  rIn := ((n : ℝ) + 2)⁻¹ / 2
  rOut := ((n : ℝ) + 2)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

lemma greenBump_rOut_tendsto : Tendsto (fun n : ℕ => (greenBump n).rOut) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

lemma greenBump_rOut_le (n : ℕ) : (greenBump n).rOut ≤ 1 := by
  change ((n : ℝ) + 2)⁻¹ ≤ 1
  exact inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])

/-- The mollification `ρₙ ⋆ w`. -/
def greenMollify (w : E₃ → ℝ) (n : ℕ) : E₃ → ℝ :=
  (greenBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w

lemma contDiff_greenMollify {w : E₃ → ℝ} (hw : LocallyIntegrable w volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (greenMollify w n) :=
  (greenBump n).hasCompactSupport_normed.contDiff_convolution_left _
    (greenBump n).contDiff_normed hw

lemma hasFDerivAt_greenMollify {w : E₃ → ℝ} (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w)
    (n : ℕ) (x : E₃) :
    HasFDerivAt (greenMollify w n)
      (((greenBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ w) x) x := by
  have h := hcw.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (((greenBump n).continuous_normed (μ := volume)).locallyIntegrable (μ := volume)) hw x
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompR E₃ =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a f
    simp
  rw [hL] at h
  exact h

lemma tendsto_greenMollify {w : E₃ → ℝ} (hw : Continuous w) (x : E₃) :
    Tendsto (fun n => greenMollify w n x) atTop (𝓝 (w x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous greenBump_rOut_tendsto hw x

lemma tendsto_fderiv_greenMollify {w : E₃ → ℝ} (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w)
    (x : E₃) :
    Tendsto (fun n => fderiv ℝ (greenMollify w n) x) atTop (𝓝 (fderiv ℝ w x)) := by
  simp_rw [fun n => (hasFDerivAt_greenMollify hw hcw n x).fderiv]
  exact ContDiffBump.convolution_tendsto_right_of_continuous greenBump_rOut_tendsto
    (hw.continuous_fderiv one_ne_zero) x

/-- A normalised bump convolution of a bounded continuous function is bounded by `3 M`. -/
lemma norm_normed_convolution_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {g : E₃ → F} (hg : Continuous g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M)
    (φ : ContDiffBump (0 : E₃)) (x : E₃) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ 3 * M := by
  have h := φ.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 2 * M)
    hg.aestronglyMeasurable
    (fun y _ => (dist_le_norm_add_norm _ _).trans (by linarith [hM y, hM x]))
  have h2 := norm_le_insert' ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
    (g x)
  rw [← dist_eq_norm] at h2
  linarith [hM x]

/-- The Laplacian of the mollification, where `w` agrees with `v` near `x`, is the mollified
distributional Laplacian of `v`. -/
lemma laplacianN_greenMollify_eq {w v f : E₃ → ℝ} (hw : LocallyIntegrable w volume)
    (hΔ : HasDistributionalLaplacianOn v f univ) {x : E₃} {n : ℕ}
    (hwv : ∀ y ∈ closedBall x (greenBump n).rOut, w y = v y) :
    laplacianN (greenMollify w n) x = ∫ y, f y * (greenBump n).normed volume (x - y) := by
  rw [greenMollify, laplacianN_convolution hw (greenBump n).contDiff_normed
    (greenBump n).hasCompactSupport_normed x]
  have htest := hΔ.test_eq (fun y => (greenBump n).normed volume (x - y))
    ((greenBump n).contDiff_normed.comp (contDiff_const.sub contDiff_id))
    ((greenBump n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x))
    (subset_univ _)
  simp only [Measure.restrict_univ] at htest
  simp_rw [laplacianN_comp_const_sub ((greenBump n).contDiff_normed (n := 2))] at htest
  rw [← htest]
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  by_cases hy : y ∈ closedBall x (greenBump n).rOut
  · simp only [hwv y hy]
  · have hz : laplacianN ((greenBump n).normed volume) (x - y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have := tsupport_laplacianN_subset _ hs
      rw [ContDiffBump.tsupport_normed_eq] at this
      apply hy
      rw [mem_closedBall, dist_comm, dist_eq_norm]
      simpa using this
    simp only [hz, mul_zero]

lemma abs_integral_bump_le {f : E₃ → ℝ} {B : ℝ} (hfB : ∀ y, |f y| ≤ B) (n : ℕ) (x : E₃) :
    |∫ y, f y * (greenBump n).normed volume (x - y)| ≤ B := by
  have hint : Integrable (fun y => B * (greenBump n).normed volume (x - y)) := by
    refine Integrable.const_mul ?_ B
    exact ((greenBump n).integrable_normed).comp_sub_left x
  have hone : ∫ y, (greenBump n).normed volume (x - y) = 1 := by
    rw [integral_sub_left_eq_self (fun y => (greenBump n).normed volume y) volume x]
    exact (greenBump n).integral_normed
  calc
    |∫ y, f y * (greenBump n).normed volume (x - y)| ≤
        ∫ y, B * (greenBump n).normed volume (x - y) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Real.norm_of_nonneg ((greenBump n).nonneg_normed _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hfB y) ((greenBump n).nonneg_normed _)
    _ = B := by rw [integral_const_mul, hone, mul_one]

lemma eventually_integral_bump_eq_zero {K : Set E₃} (hKc : IsClosed K) {f : E₃ → ℝ}
    (hf0 : ∀ y ∉ K, f y = 0) {x : E₃} (hx : x ∉ K) :
    ∀ᶠ n in atTop, (∫ y, f y * (greenBump n).normed volume (x - y)) = 0 := by
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.mp hKc.isOpen_compl x hx
  filter_upwards [greenBump_rOut_tendsto.eventually (gt_mem_nhds hε)] with n hn
  apply integral_eq_zero_of_ae
  refine Eventually.of_forall fun y => ?_
  by_cases hy : y ∈ K
  · have hyb : y ∉ ball x ε := fun h => hεK h hy
    have hz : (greenBump n).normed volume (x - y) = 0 := by
      apply Function.notMem_support.mp
      rw [ContDiffBump.support_normed_eq, mem_ball, dist_zero_right]
      intro hlt
      apply hyb
      rw [mem_ball, dist_comm, dist_eq_norm]
      linarith
    simp [hz]
  · simp [hf0 y hy]

lemma abs_pair_le {a c : ℝ} {b d e : E₃} (he : ‖e‖ ≤ 1) :
    |a * inner ℝ b e - c * inner ℝ d e| ≤ |a| * ‖b‖ + |c| * ‖d‖ := by
  have h1 : |inner ℝ b e| ≤ ‖b‖ := (abs_real_inner_le_norm b e).trans
    (by nlinarith [norm_nonneg b, norm_nonneg e])
  have h2 : |inner ℝ d e| ≤ ‖d‖ := (abs_real_inner_le_norm d e).trans
    (by nlinarith [norm_nonneg d, norm_nonneg e])
  calc
    _ ≤ |a * inner ℝ b e| + |c * inner ℝ d e| := abs_sub _ _
    _ = |a| * |inner ℝ b e| + |c| * |inner ℝ d e| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg a))
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg c))

/-- Blueprint `eq:green-second`, the second Green identity on `B_r ∖ K`: for a compact regular
`K ⊆ B_r` with `C¹` boundary, a `C¹` function `v` whose distributional Laplacian on `ℝ³` is a
bounded function vanishing off `K`, and a `C²` function `g` harmonic off `K`, the flux of
`v ∇g - g ∇v` through `∂B_r` equals its flux through `∂K` (outward normal of `K`). -/
theorem green_second_annulus {K : Set E₃} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r)
    {v f : E₃ → ℝ} (hv : ContDiff ℝ 1 v) (hΔv : HasDistributionalLaplacianOn v f univ)
    {B : ℝ} (hfB : ∀ y, |f y| ≤ B) (hf0 : ∀ y ∉ K, f y = 0)
    {g : E₃ → ℝ} (hg : ContDiff ℝ 2 g) (hΔg : ∀ x ∈ Kᶜ, laplacianN g x = 0) :
    (∫ x in sphere (0 : E₃) r, (v x * inner ℝ (gradient g x) (r⁻¹ • x) -
        g x * inner ℝ (gradient v x) (r⁻¹ • x)) ∂hausdorffMeasure2 3) =
      ∫ x in frontier K, (v x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
        g x * inner ℝ (gradient v x) (hC1.outwardNormal x)) ∂hausdorffMeasure2 3 := by
  -- cutoff and localisation
  let χb : ContDiffBump (0 : E₃) := ⟨r + 1, r + 2, by linarith, by linarith⟩
  let w : E₃ → ℝ := fun y => χb y * v y
  have hw1 : ContDiff ℝ 1 w := (χb.contDiff).mul hv
  have hcw : HasCompactSupport w := χb.hasCompactSupport.mul_right
  have hwli : LocallyIntegrable w volume := hw1.continuous.locallyIntegrable
  have hwv : ∀ y ∈ closedBall (0 : E₃) (r + 1), w y = v y := fun y hy => by
    simp only [w, χb.one_of_mem_closedBall hy, one_mul]
  have hwv' : ∀ x ∈ closedBall (0 : E₃) r, ∀ n : ℕ,
      ∀ y ∈ closedBall x (greenBump n).rOut, w y = v y := by
    intro x hx n y hy
    apply hwv
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    rw [mem_closedBall, dist_eq_norm] at hy
    have := norm_le_insert' y x
    linarith [greenBump_rOut_le n, norm_sub_rev y x]
  set vn : ℕ → E₃ → ℝ := fun n => greenMollify w n with hvn
  have hvns : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (vn n) := fun n => contDiff_greenMollify hwli n
  -- pointwise convergence on the closed ball
  have hlim0 : ∀ x ∈ closedBall (0 : E₃) r, Tendsto (fun n => vn n x) atTop (𝓝 (v x)) := by
    intro x hx
    have := tendsto_greenMollify hw1.continuous x
    rwa [hwv x (closedBall_subset_closedBall (by linarith) hx)] at this
  have hlim1 : ∀ x ∈ closedBall (0 : E₃) r,
      Tendsto (fun n => gradient (vn n) x) atTop (𝓝 (gradient v x)) := by
    intro x hx
    have hfd : fderiv ℝ w x = fderiv ℝ v x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : E₃) (r + 1) from
        closedBall_subset_ball (by linarith) hx)] with y hy
      exact hwv y (ball_subset_closedBall hy)
    have := tendsto_fderiv_greenMollify hw1 hcw x
    rw [hfd] at this
    exact ((toDual ℝ E₃).symm.continuous.tendsto _).comp this
  -- uniform bounds
  obtain ⟨M0, hM0⟩ := hw1.continuous.bounded_above_of_compact_support hcw
  obtain ⟨M1, hM1⟩ := (hw1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hcw.fderiv (𝕜 := ℝ))
  have hb0 : ∀ n x, |vn n x| ≤ 3 * M0 := fun n x => by
    rw [← Real.norm_eq_abs]; exact norm_normed_convolution_le hw1.continuous hM0 _ x
  have hb1 : ∀ n x, ‖gradient (vn n) x‖ ≤ 3 * M1 := fun n x => by
    change ‖(toDual ℝ E₃).symm (fderiv ℝ (vn n) x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map, (hasFDerivAt_greenMollify hw1 hcw n x).fderiv]
    exact norm_normed_convolution_le (hw1.continuous_fderiv one_ne_zero) hM1 _ x
  obtain ⟨Gg, hGg⟩ := (isCompact_closedBall (0 : E₃) r).exists_bound_of_continuousOn
    ((contDiff_gradient_of_contDiff_succ (r := 1) hg).continuous.continuousOn)
  obtain ⟨G0, hG0⟩ := (isCompact_closedBall (0 : E₃) r).exists_bound_of_continuousOn
    (hg.continuous.continuousOn)
  -- the annulus and its boundary
  set A : Set E₃ := ball (0 : E₃) r ∩ Kᶜ with hA
  have hAo : IsOpen A := isOpen_ball.inter hK.isClosed.isOpen_compl
  have hAb : Bornology.IsBounded A := isBounded_ball.subset inter_subset_left
  have hAC1 := annulus_hasC1Boundary hK hreg hC1 hr hKr
  have hfin : hausdorffMeasure2 3 (sphere (0 : E₃) r ∪ frontier K) < ⊤ := by
    rw [← annulus_frontier hK hr hKr]
    exact capacity_boundary_measure_lt_top hAo hAb hAC1
  have hfinS : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (sphere (0 : E₃) r)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_union_left).trans_lt hfin).ne
  have hfinK : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (frontier K)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_union_right).trans_lt hfin).ne
  have hfinA : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr hAb.measure_lt_top.ne
  -- Gauss-Green for each mollified field
  have hGG : ∀ n : ℕ, (∫ x in A, -(g x * laplacianN (vn n) x)) =
      (∫ x in sphere (0 : E₃) r, (vn n x * inner ℝ (gradient g x) (r⁻¹ • x) -
        g x * inner ℝ (gradient (vn n) x) (r⁻¹ • x)) ∂hausdorffMeasure2 3) -
      ∫ x in frontier K, (vn n x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
        g x * inner ℝ (gradient (vn n) x) (hC1.outwardNormal x)) ∂hausdorffMeasure2 3 := by
    intro n
    have hv2 : ContDiff ℝ 2 (vn n) :=
      (hvns n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have hgv : ContDiff ℝ 1 (gradient (vn n)) :=
      contDiff_gradient_of_contDiff_succ (r := 1) hv2
    have hgg : ContDiff ℝ 1 (gradient g) := contDiff_gradient_of_contDiff_succ (r := 1) hg
    have hv1 : ContDiff ℝ 1 (vn n) := hv2.of_le (by norm_num)
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
    have hng : ContDiff ℝ 1 (fun y => -g y) := hg1.neg
    let X : E₃ → E₃ := fun y => vn n y • gradient g y
    let Y : E₃ → E₃ := fun y => (-g y) • gradient (vn n) y
    have hX : ContDiff ℝ 1 X := hv1.smul hgg
    have hY : ContDiff ℝ 1 Y := hng.smul hgv
    have h := capacity_annulus_gauss_green hK hreg hC1 hr hKr (Z := X + Y) (hX.add hY)
    have hgneg : ∀ x, gradient (fun y => -g y) x = -gradient g x := fun x => by
      change (toDual ℝ E₃).symm (fderiv ℝ (fun y => -g y) x) = _
      rw [fderiv_fun_neg, map_neg]
      rfl
    have hdiv : ∀ x ∈ A, divergenceN (X + Y) x = -(g x * laplacianN (vn n) x) := by
      intro x hx
      rw [divergenceN_add hX hY, divergenceN_smul hv1 hgg, divergenceN_smul hng hgv,
        ← laplacianN_eq_divergenceN_gradient hg, ← laplacianN_eq_divergenceN_gradient hv2,
        hΔg x hx.2, hgneg, inner_neg_left, real_inner_comm]
      ring
    rw [setIntegral_congr_fun hAo.measurableSet hdiv] at h
    rw [h]
    congr 1
    · apply setIntegral_congr_fun isClosed_sphere.measurableSet
      intro x _
      simp only [X, Y, Pi.add_apply, inner_add_left, real_inner_smul_left]
      ring
    · apply setIntegral_congr_fun isClosed_frontier.measurableSet
      intro x _
      simp only [X, Y, Pi.add_apply, inner_add_left, real_inner_smul_left]
      ring
  have hv2' : ∀ n, ContDiff ℝ 2 (vn n) := fun n =>
    (hvns n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hgvc : ∀ n, Continuous (gradient (vn n)) := fun n =>
    (contDiff_gradient_of_contDiff_succ (r := 1) (hv2' n)).continuous
  have hggc : Continuous (gradient g) :=
    (contDiff_gradient_of_contDiff_succ (r := 1) hg).continuous
  have hpair : ∀ n x (e : E₃), ‖e‖ ≤ 1 → x ∈ closedBall (0 : E₃) r →
      |vn n x * inner ℝ (gradient g x) e - g x * inner ℝ (gradient (vn n) x) e| ≤
        3 * M0 * Gg + G0 * (3 * M1) := by
    intro n x e he hx
    refine (abs_pair_le he).trans (add_le_add ?_ ?_)
    · exact mul_le_mul (hb0 n x) (hGg x hx) (norm_nonneg _) ((abs_nonneg _).trans (hb0 n x))
    · rw [← Real.norm_eq_abs]
      exact mul_le_mul (hG0 x hx) (hb1 n x) (norm_nonneg _) ((norm_nonneg _).trans (hG0 x hx))
  -- the interior term tends to zero
  have hL : Tendsto (fun n : ℕ => ∫ x in A, -(g x * laplacianN (vn n) x)) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict A)
      (l := atTop) (F := fun (n : ℕ) x => -(g x * laplacianN (vn n) x)) (f := fun _ => (0 : ℝ))
      (fun _ => G0 * B) (Eventually.of_forall fun n =>
        (hg.continuous.mul (sobolevChain_contDiff_laplacianN (hvns n)).continuous).neg
          |>.aestronglyMeasurable)
      (Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem hAo.measurableSet] with x hx
        have hxb : x ∈ closedBall (0 : E₃) r := ball_subset_closedBall hx.1
        rw [norm_neg, norm_mul, laplacianN_greenMollify_eq hwli hΔv (hwv' x hxb n),
          Real.norm_eq_abs (∫ y, _)]
        exact mul_le_mul (hG0 x hxb) (abs_integral_bump_le hfB n x) (abs_nonneg _)
          ((norm_nonneg _).trans (hG0 x hxb)))
      (integrable_const _)
      (by
        filter_upwards [ae_restrict_mem hAo.measurableSet] with x hx
        have hxb : x ∈ closedBall (0 : E₃) r := ball_subset_closedBall hx.1
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_integral_bump_eq_zero hK.isClosed hf0 hx.2] with n hn
        rw [laplacianN_greenMollify_eq hwli hΔv (hwv' x hxb n), hn, mul_zero, neg_zero])
    simpa only [integral_zero] using h
  -- the sphere term
  have hS : Tendsto (fun n : ℕ => ∫ x in sphere (0 : E₃) r,
      (vn n x * inner ℝ (gradient g x) (r⁻¹ • x) -
        g x * inner ℝ (gradient (vn n) x) (r⁻¹ • x)) ∂hausdorffMeasure2 3) atTop
      (𝓝 (∫ x in sphere (0 : E₃) r, (v x * inner ℝ (gradient g x) (r⁻¹ • x) -
        g x * inner ℝ (gradient v x) (r⁻¹ • x)) ∂hausdorffMeasure2 3)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 3 * M0 * Gg + G0 * (3 * M1))
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
      (integrable_const _) ?_
    · have hc1 : Continuous (fun x : E₃ => inner ℝ (gradient g x) (r⁻¹ • x)) :=
        hggc.inner (continuous_id.const_smul r⁻¹)
      have hc2 : Continuous (fun x : E₃ => inner ℝ (gradient (vn n) x) (r⁻¹ • x)) :=
        (hgvc n).inner (continuous_id.const_smul r⁻¹)
      have hc : Continuous (fun x : E₃ => vn n x * inner ℝ (gradient g x) (r⁻¹ • x) -
          g x * inner ℝ (gradient (vn n) x) (r⁻¹ • x)) :=
        ((hvns n).continuous.mul hc1).sub (hg.continuous.mul hc2)
      exact hc.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with x hx
      have he : ‖r⁻¹ • x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, mem_sphere_zero_iff_norm.mp hx,
          inv_mul_cancel₀ hr.ne']
      exact (Real.norm_eq_abs _).trans_le (hpair n x _ he (sphere_subset_closedBall hx))
    · filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with x hx
      have hxb := sphere_subset_closedBall hx
      exact ((hlim0 x hxb).mul_const _).sub
        (tendsto_const_nhds.mul ((hlim1 x hxb).inner tendsto_const_nhds))
  -- the inner boundary term
  have hνc : ContinuousOn hC1.outwardNormal (frontier K) := by
    rw [← capacity_frontier_interior hK hreg]
    exact hC1.continuousOn_outwardNormal
  have hKb : frontier K ⊆ closedBall (0 : E₃) r :=
    (hK.isClosed.frontier_subset.trans hKr).trans ball_subset_closedBall
  have hKt : Tendsto (fun n : ℕ => ∫ x in frontier K,
      (vn n x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
        g x * inner ℝ (gradient (vn n) x) (hC1.outwardNormal x)) ∂hausdorffMeasure2 3) atTop
      (𝓝 (∫ x in frontier K, (v x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
        g x * inner ℝ (gradient v x) (hC1.outwardNormal x)) ∂hausdorffMeasure2 3)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 3 * M0 * Gg + G0 * (3 * M1))
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
      (integrable_const _) ?_
    · have hc1 : ContinuousOn (fun x : E₃ => inner ℝ (gradient g x) (hC1.outwardNormal x))
          (frontier K) := hggc.continuousOn.inner hνc
      have hc2 : ContinuousOn (fun x : E₃ => inner ℝ (gradient (vn n) x) (hC1.outwardNormal x))
          (frontier K) := (hgvc n).continuousOn.inner hνc
      have hc : ContinuousOn (fun x : E₃ => vn n x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
          g x * inner ℝ (gradient (vn n) x) (hC1.outwardNormal x)) (frontier K) :=
        ((hvns n).continuous.continuousOn.mul hc1).sub (hg.continuous.continuousOn.mul hc2)
      exact hc.aestronglyMeasurable isClosed_frontier.measurableSet
    · filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      exact (Real.norm_eq_abs _).trans_le (hpair n x _ (hC1.norm_outwardNormal_le x) (hKb hx))
    · filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      exact ((hlim0 x (hKb hx)).mul_const _).sub
        (tendsto_const_nhds.mul ((hlim1 x (hKb hx)).inner tendsto_const_nhds))
  have h1 := hS.sub hKt
  have h2 : Tendsto (fun n : ℕ => (∫ x in sphere (0 : E₃) r,
      (vn n x * inner ℝ (gradient g x) (r⁻¹ • x) -
        g x * inner ℝ (gradient (vn n) x) (r⁻¹ • x)) ∂hausdorffMeasure2 3) -
      ∫ x in frontier K, (vn n x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
        g x * inner ℝ (gradient (vn n) x) (hC1.outwardNormal x)) ∂hausdorffMeasure2 3)
      atTop (𝓝 0) := by
    refine hL.congr' (Eventually.of_forall fun n => ?_)
    exact hGG n
  exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)

/-- `eq:w-boundary`, direction part, with only `C¹` boundary charts: if `u = 1` on `K`,
`u ≤ 1` off `K`, and `g` is a `C²` function agreeing with `u` on the closed exterior, then on
`∂K` the gradient of `g` is `-|∇g| ν_K`. (Positivity of `|∇g|`, the Hopf half, is not claimed.) -/
theorem gradient_eq_neg_norm_smul_normal_of_le_one {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u : AmbientSpace → ℝ} (hb : ∀ x ∈ K, u x = 1) (hle : ∀ x ∈ Kᶜ, u x ≤ 1)
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) :
    ∀ p ∈ frontier K, gradient g p = -‖gradient g p‖ • hC1.outwardNormal p := by
  intro p hp
  have hpi : p ∈ frontier (interior K) := by
    rwa [capacity_frontier_interior hK hreg]
  have hpcl : p ∈ closure Kᶜ :=
    frontier_subset_closure (show p ∈ frontier Kᶜ by simpa using hp)
  have hup : u p = 1 := hb p (hK.isClosed.frontier_subset hp)
  have hgp : g p = 1 := (hug hpcl).symm.trans hup
  have hdg := (hg.differentiable (by norm_num) p).hasFDerivAt
  obtain ⟨c, hc, hpc⟩ := hC1 p hpi
  have hn := hC1.outwardNormal_eq_chart hc hpi hpc
  by_cases h0 : gradient g p = 0
  · rw [h0]; simp
  have hpos : 0 < ‖gradient g p‖ := norm_pos_iff.mpr h0
  rw [hn]
  by_contra hne
  let v := gradient g p + ‖gradient g p‖ • c.outwardNormal p
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    exact (eq_neg_of_add_eq_zero_left hz).trans (neg_smul _ _).symm
  have hi : 0 < inner ℝ (gradient g p) (c.outwardNormal p) + ‖gradient g p‖ := by
    have hs := sq_pos_of_pos (norm_pos_iff.mpr hv)
    dsimp only [v] at hs
    rw [norm_add_sq_real, norm_smul, c.norm_outwardNormal,
      Real.norm_of_nonneg (norm_nonneg _), mul_one, inner_smul_right] at hs
    nlinarith
  have hcv : 0 < inner ℝ v (c.outwardNormal p) := by
    simpa only [v, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      c.norm_outwardNormal, one_pow, mul_one] using hi
  have hgv : 0 < fderiv ℝ g p v := by
    rw [← inner_gradient_left]
    dsimp only [v]
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [mul_pos hpos hi]
  have hext := classicalNormal_eventually_pos_of_hasDerivAt
    (c.hasDerivAt_definingFunction_line p v)
    (by simpa using hc.definingFunction_eq_zero hpi hpc)
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) hcv)
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hgline : HasDerivAt (fun t : ℝ => g (p + t • v) - 1) (fderiv ℝ g p v) 0 := by
    have hdg' : HasFDerivAt g (fderiv ℝ g p) (p + (0 : ℝ) • v) := by
      simpa using hdg
    exact (hdg'.comp_hasDerivAt 0 hline).sub_const 1
  have hinc := classicalNormal_eventually_pos_of_hasDerivAt hgline
    (by simp [hgp]) hgv
  have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨t, hte, htg, htr⟩ :=
    (hext.and (hinc.and (ht (c.isOpen_region.mem_nhds hpc)))).exists
  have hout : p + t • v ∈ Kᶜ := by
    intro hin
    have hin' : p + t • v ∈ closure (interior K) := by rwa [← hreg]
    have hgraph : p + t • v ∈ closure c.graphDomain :=
      (hc.closure_inter_eq ▸ (show p + t • v ∈ closure (interior K) ∩ c.region
        from ⟨hin', htr⟩)).1
    have hle' := (c.mem_closure_graphDomain_iff _).mp hgraph
    exact (not_lt_of_ge hle') (sub_pos.mp hte)
  have hlt : g (p + t • v) ≤ 1 := by
    rw [← hug (subset_closure hout)]
    exact hle _ hout
  linarith

variable {Ω : Set AmbientSpace}

/-- Blueprint `eq:green-second` for the capacitary potential `u` of the filled hull `K` of a
bounded open `Ω ∋ 0` with `C¹` boundary and `v = v_Ω`: for all large `R`,
`∫_{∂K} (v w + ∂_{ν_K} v) + ∫_{∂B_R} (v ∂_r u - u ∂_r v) = 0`, where `w = |∇g|` for a `C²`
function `g` agreeing with `u` on the closed exterior (the named stand-in for
`thm:boundary-C2a`, as in `lem:flux-identity`). This is exactly the input
`hgreen_second_of_W11_gauss_green` of `filledHull_green_identity`. -/
theorem filledHull_green_second (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h1 : HasC1Boundary Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure (filledHull Ω)ᶜ)) :
    ∀ᶠ R in atTop,
      (∫ x in frontier (filledHull Ω), (coulombPotentialReal Ω x * ‖gradient g x‖ +
          inner ℝ (gradient (coulombPotentialReal Ω) x)
            ((filledHull_hasC1Boundary_interior ho h1).outwardNormal x))
          ∂hausdorffMeasure2 3) +
        outerWronskian u (coulombPotentialReal Ω) R = 0 := by
  have hK := filledHull_isCompact hbd
  have hreg := filledHull_eq_closure_interior ho
  have hC1 := filledHull_hasC1Boundary_interior ho h1
  have hzero : (0 : AmbientSpace) ∈ interior (filledHull Ω) := filledHull_subset_interior ho h0
  have hΩK : Ω ⊆ filledHull Ω := subset_closure.trans (filledHull_closure_subset Ω)
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : AmbientSpace)
  have heq : coulombPotentialReal Ω = fun a => (coulombPotential Ω a).toReal := by
    funext a
    rw [coulombPotentialReal_eq_setIntegral Ω ho.measurableSet a,
      coulombPotential_toReal Ω hbd.measure_lt_top a]
    simp only [one_div]
  have hv : ContDiff ℝ 1 (coulombPotentialReal Ω) := by
    rw [heq]; exact contDiff_one_coulombPotential_of_isBounded hbd
  have hcf : HasCompactSupport (Ω.indicator fun _ => (1 : ℝ)) :=
    hbd.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
      (closure_mono Set.support_indicator_subset)
  have hΔv : HasDistributionalLaplacianOn (coulombPotentialReal Ω)
      (fun x => -(4 * Real.pi) * Ω.indicator (fun _ => (1 : ℝ)) x) univ :=
    hasDistributionalLaplacianOn_scalarNewtonianPotential
      ((aestronglyMeasurable_const.indicator ho.measurableSet)) hcf (B := 1) (fun x => by
        by_cases hx : x ∈ Ω <;> simp [hx])
  have hfB : ∀ y, |-(4 * Real.pi) * Ω.indicator (fun _ => (1 : ℝ)) y| ≤ 4 * Real.pi := by
    intro y
    by_cases hy : y ∈ Ω
    · simp [hy, abs_of_pos Real.pi_pos]
    · rw [Set.indicator_of_notMem hy, mul_zero, abs_zero]; positivity
  have hf0 : ∀ y ∉ filledHull Ω, -(4 * Real.pi) * Ω.indicator (fun _ => (1 : ℝ)) y = 0 := by
    intro y hy
    simp [Set.indicator_of_notMem (fun h => hy (hΩK h))]
  have hΔg := capacity_laplacian_eq_zero_of_boundary_C2 hK hg hug hh
  have hdir := gradient_eq_neg_norm_smul_normal_of_le_one hK hreg hC1 hb
    (fun x hx => ((capacitary_signs hK hzero hu hh hb hinf).1 x hx).2) hg hug
  filter_upwards [eventually_gt_atTop (max R₀ 0)] with R hR
  have hRpos : 0 < R := (le_max_right _ _).trans_lt hR
  have hKR : filledHull Ω ⊆ ball 0 R := hR₀.trans (ball_subset_ball ((le_max_left _ _).trans hR.le))
  have h := green_second_annulus hK hreg hC1 hRpos hKR hv hΔv hfB hf0 hg hΔg
  have hW : outerWronskian u (coulombPotentialReal Ω) R =
      ∫ x in sphere (0 : AmbientSpace) R,
        (coulombPotentialReal Ω x * inner ℝ (gradient g x) (R⁻¹ • x) -
          g x * inner ℝ (gradient (coulombPotentialReal Ω) x) (R⁻¹ • x)) ∂hausdorffMeasure2 3 := by
    unfold outerWronskian
    apply setIntegral_congr_fun isClosed_sphere.measurableSet
    intro x hx
    have hxK : x ∈ (filledHull Ω)ᶜ := fun hxK =>
      (mem_ball.mp (hKR hxK)).ne (mem_sphere.mp hx)
    simp only
    rw [capacity_gradient_eq_of_boundary_C2 hK hug hxK, hug (subset_closure hxK),
      real_inner_smul_right, real_inner_smul_right]
    ring
  have hKt : (∫ x in frontier (filledHull Ω),
      (coulombPotentialReal Ω x * inner ℝ (gradient g x) (hC1.outwardNormal x) -
        g x * inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x))
        ∂hausdorffMeasure2 3) =
      -∫ x in frontier (filledHull Ω), (coulombPotentialReal Ω x * ‖gradient g x‖ +
          inner ℝ (gradient (coulombPotentialReal Ω) x) (hC1.outwardNormal x))
          ∂hausdorffMeasure2 3 := by
    rw [← integral_neg]
    apply setIntegral_congr_fun isClosed_frontier.measurableSet
    intro x hx
    have hpcl : x ∈ closure (filledHull Ω)ᶜ :=
      frontier_subset_closure (show x ∈ frontier (filledHull Ω)ᶜ by simpa using hx)
    have hgx : g x = 1 := (hug hpcl).symm.trans (hb x ((filledHull_isClosed Ω).frontier_subset hx))
    have hnx : ‖hC1.outwardNormal x‖ = 1 :=
      hC1.norm_outwardNormal (by rwa [capacity_frontier_interior hK hreg])
    have hinner : inner ℝ (gradient g x) (hC1.outwardNormal x) = -‖gradient g x‖ := by
      conv_lhs => rw [hdir x hx]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnx]
      ring
    simp only [hgx, hinner]
    ring
  rw [hW, h, hKt]
  ring

/-- Blueprint `thm:green-identity` (`eq:green-identity`) for the capacitary potential of the
filled hull, with `eq:green-second` discharged: the only remaining input is the named `C²`
boundary-extension hypothesis `(g, hg, hug)` standing in for `thm:boundary-C2a`, with
`w = |∇g|` the one-sided `|∇u|` on `∂K`. -/
theorem filledHull_green_identity_of_boundary_C2 (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h1 : HasC1Boundary Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure (filledHull Ω)ᶜ)) :
    (4 * Real.pi)⁻¹ * (∫ x in frontier (filledHull Ω),
      coulombPotentialReal Ω x * ‖gradient g x‖ ∂hausdorffMeasure2 3) = (volume Ω).toReal :=
  filledHull_green_identity ho hbd h1 h0 hu hh hb hinf hg
    (filledHull_green_second ho hbd h1 h0 hu hh hb hinf hg hug)

end LiquidDrop
