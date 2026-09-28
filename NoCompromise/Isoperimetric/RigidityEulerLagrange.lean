import NoCompromise.Isoperimetric.RigidityMinimal
import NoCompromise.Stationary.EulerLagrange

/-!
# The Euler--Lagrange equation of a perimeter minimiser

Blueprint `thm:isoperimetric-rigidity`, Step 2: `thm:constrained-first-var` and
`lem:graph-PMC` of chapter 28 with the Coulomb term deleted (`v_Ω` replaced by `0`).
The volume constraint is restored by the dilation `r(t) = (V / |F_t|)^{1/3}` of the
straight image `F_t`, so `r(t)² P(F_t)` has a local minimum at `t = 0`. The first
variations of perimeter and volume then give the weak Euler--Lagrange equation with
the explicit multiplier `2P / (3V)`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The Lagrange multiplier of a fixed-volume perimeter minimiser, `2 P / (3 V)`. -/
noncomputable def perimeterMinimizerMultiplier (V : ℝ) (Ω : Set AmbientSpace) : ℝ :=
  2 * (perimeter Ω).toReal / (3 * V)

/-- Blueprint `thm:constrained-first-var` with the Coulomb term deleted, reduced-boundary
form: for a fixed-volume perimeter minimiser the first variation of perimeter is the
multiplier `2P / (3V)` times the first variation of volume. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.first_variation_eq {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    (hP : HasLocallyFinitePerimeter Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in reducedBoundary Ω hP hmin.1,
        tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
      perimeterMinimizerMultiplier V Ω *
        ∫ x in reducedBoundary Ω hP hmin.1,
          inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3 := by
  set Pd := ∫ x in reducedBoundary Ω hP hmin.1,
    tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3
  set B := ∫ x in reducedBoundary Ω hP hmin.1,
    inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3
  have hvolfin : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have hdP : HasDerivAt (fun t : ℝ => (perimeter (straightPerturbation X t '' Ω)).toReal)
      Pd 0 := first_variation_perimeter_global Ω hP hmin.1 hmin.2.2.1 hX hcX
  have hdV : HasDerivAt (fun t : ℝ => (volume (straightPerturbation X t '' Ω)).toReal)
      B 0 := first_variation_volume Ω hP hmin.1 hvolfin hX hcX
  set per := fun t : ℝ => (perimeter (straightPerturbation X t '' Ω)).toReal
  set vol := fun t : ℝ => (volume (straightPerturbation X t '' Ω)).toReal
  have hvol0 : vol 0 = V := by
    simp only [vol, straightPerturbation_zero_image, hmin.2.1, ENNReal.toReal_ofReal hV.le]
  have hper0 : per 0 = (perimeter Ω).toReal := by simp only [per, straightPerturbation_zero_image]
  set q := fun t : ℝ => V / vol t
  have hq0 : q 0 = 1 := by simp only [q, hvol0, div_self hV.ne']
  have hq : HasDerivAt q ((0 * vol 0 - V * B) / vol 0 ^ 2) 0 :=
    (hasDerivAt_const (0 : ℝ) V).div hdV (by rw [hvol0]; exact hV.ne')
  set r := fun t : ℝ => q t ^ (1 / 3 : ℝ)
  have hr0 : r 0 = 1 := by simp only [r, hq0, Real.one_rpow]
  have hr : HasDerivAt r ((0 * vol 0 - V * B) / vol 0 ^ 2 * (1 / 3 : ℝ) *
      q 0 ^ ((1 / 3 : ℝ) - 1)) 0 :=
    hq.rpow_const (Or.inl (by rw [hq0]; exact one_ne_zero))
  set g := fun t : ℝ => r t ^ 2 * per t
  have hg := (hr.pow 2).mul hdP
  have hmin0 : IsLocalMin g 0 := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hX hcX‖ < 1 :=
      (continuous_abs.mul_const _).continuousAt.eventually
        (gt_mem_nhds (by simp : |(0 : ℝ)| * ‖straightDerivativeField hX hcX‖ < 1))
    have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < vol t :=
      hdV.continuousAt.eventually (lt_mem_nhds (by rw [hvol0]; exact hV))
    filter_upwards [hsmall, hpos] with t ht hvt
    obtain ⟨hi, _⟩ := straightPerturbation_bijective
      (lipschitzWith_straightDerivativeField hX hcX) ht
    have hmF := nullMeasurableSet_image_of_differentiable
      ((contDiff_straightPerturbation hX t).differentiable one_ne_zero) hi hmin.1
    set F := straightPerturbation X t '' Ω with hFdef
    have hFfin : volume F ≠ ∞ := by
      intro h
      have : vol t = 0 := by
        change (volume F).toReal = 0
        rw [h, ENNReal.toReal_top]
      linarith
    have hPF : perimeter F < ∞ := perimeter_straight_image_lt_top Ω hP hmin.1 hmin.2.2.1 hX hcX ht
    have hqt : 0 < q t := div_pos hV hvt
    have hrt : 0 < r t := Real.rpow_pos_of_pos hqt _
    have hr3 : r t ^ 3 = q t := by
      simp only [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqt.le]
      norm_num
    have hGvol : volume ((fun x => r t • x) '' F) = ENNReal.ofReal V := by
      rw [volume_image_smul F hrt, ← ENNReal.ofReal_toReal hFfin,
        ← ENNReal.ofReal_mul (pow_nonneg hrt.le 3), hr3]
      change ENNReal.ofReal (V / vol t * vol t) = _
      rw [div_mul_cancel₀ _ hvt.ne']
    have hmG := nullMeasurableSet_image_of_differentiable
      (by fun_prop : Differentiable ℝ (fun x : AmbientSpace => r t • x))
      (smul_right_injective _ hrt.ne') hmF
    have hE := hmin.2.2.2 _ hmG hGvol
    rw [perimeter_image_smul hmF hrt] at hE
    have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPF.ne) hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hrt.le 2)] at hR
    change r 0 ^ 2 * per 0 ≤ r t ^ 2 * per t
    rw [hr0, hper0]
    simpa only [one_pow, one_mul] using hR
  have hzero := hmin0.hasDerivAt_eq_zero hg
  have hk : (0 * V - V * B) / V ^ 2 * (1 / 3 : ℝ) = -(B / (3 * V)) := by
    rw [zero_mul, zero_sub, neg_div, sq, mul_div_mul_left B V hV.ne']
    ring
  simp only [Pi.pow_apply] at hzero
  rw [hr0, hq0, hvol0, hper0, Real.one_rpow, hk] at hzero
  rw [perimeterMinimizerMultiplier]
  linear_combination hzero

/-- Existence of a Lagrange multiplier for the weak Euler--Lagrange equation of a
perimeter minimiser. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.exists_first_variation {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    (hP : HasLocallyFinitePerimeter Ω) :
    ∃ lam : ℝ, ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x in reducedBoundary Ω hP hmin.1,
          tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
        lam * ∫ x in reducedBoundary Ω hP hmin.1,
          inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3 :=
  ⟨perimeterMinimizerMultiplier V Ω, fun _ hX hcX => hmin.first_variation_eq hV hP hX hcX⟩

/-- The constrained first variation of a perimeter minimiser with open `C¹` representative,
integrated over the whole frontier with the canonical outward normal. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.first_variation_frontier {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in frontier Ω, tangentialDivergence X
        (reducedNormal Ω (hC1.hasLocallyFinitePerimeter hΩo) hmin.1) x
        ∂hausdorffMeasure2 3) =
      ∫ x in frontier Ω, perimeterMinimizerMultiplier V Ω *
        inner ℝ (X x) (reducedNormal Ω (hC1.hasLocallyFinitePerimeter hΩo) hmin.1 x)
        ∂hausdorffMeasure2 3 := by
  rw [Measure.restrict_congr_set
    (hC1.boundary_ae_eq_reducedBoundary hΩo (hC1.hasLocallyFinitePerimeter hΩo)),
    integral_const_mul]
  exact hmin.first_variation_eq hV (hC1.hasLocallyFinitePerimeter hΩo) hX hcX

/-- The weak first variation of a perimeter minimiser localized to a single rigid graph
chart, expressed using its classical outward normal. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.first_variation_chart {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    (hsX : tsupport X ⊆ c.region) :
    (∫ x in c.graphSurface, tangentialDivergence X c.outwardNormal x ∂hausdorffMeasure2 3) =
      ∫ x in c.graphSurface, perimeterMinimizerMultiplier V Ω *
        inner ℝ (X x) (c.outwardNormal x) ∂hausdorffMeasure2 3 := by
  have hzero (x : AmbientSpace) (hx : x ∉ c.region) : x ∉ tsupport X :=
    fun hx' => hx (hsX hx')
  have hleft := hc.integral_frontier_eq_graphSurface
    (g := tangentialDivergence X c.outwardNormal)
    (fun x hx => tangentialDivergence_eq_zero_of_notMem_tsupport (hzero x hx))
  have hright := hc.integral_frontier_eq_graphSurface
    (g := fun x => perimeterMinimizerMultiplier V Ω * inner ℝ (X x) (c.outwardNormal x))
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (hzero x hx), inner_zero_left, mul_zero])
  rw [← hleft, ← hright]
  have hn := hc.reduced_normal_eq_ae hC1 hΩo (hC1.hasLocallyFinitePerimeter hΩo)
  calc
    _ = ∫ x in frontier Ω, tangentialDivergence X
        (reducedNormal Ω (hC1.hasLocallyFinitePerimeter hΩo) hmin.1) x
        ∂hausdorffMeasure2 3 := by
      apply integral_congr_ae
      filter_upwards [hn] with x hx
      by_cases hr : x ∈ c.region
      · simp only [tangentialDivergence, hx hr]
      · rw [tangentialDivergence_eq_zero_of_notMem_tsupport (hzero x hr),
          tangentialDivergence_eq_zero_of_notMem_tsupport (hzero x hr)]
    _ = _ := hmin.first_variation_frontier hV hΩo hC1 hX hcX
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hn] with x hx
      by_cases hr : x ∈ c.region
      · rw [hx hr]
      · rw [image_eq_zero_of_notMem_tsupport (hzero x hr), inner_zero_left, inner_zero_left]

/-- The graph area weight cancels the normal component of a vertical field
(a copy of the corresponding private lemma of `NoCompromise.Stationary.EulerLagrange`). -/
lemma graph_vertical_normal_flux_perim
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Real.sqrt (1 + ‖gradient f y‖ ^ 2) *
      inner ℝ (r • EuclideanSpace.single (Fin.last 2) 1)
        (smoothSubgraphNormal f (graphMapN f y)) = r := by
  rw [smoothSubgraphNormal]
  have hp : graphProjectionN 2 (graphMapN f y) = y := by
    change graphProjectionN 2 (graphAppendN y (f y)) = y
    simp
  rw [hp, inner_smoothGraphUnitNormal]
  have hv : graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) (1 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [graphProjectionN_apply]
  have hvr : graphProjectionN 2
      (r • EuclideanSpace.single (Fin.last 2) (1 : ℝ)) = 0 := by
    rw [map_smul, hv, smul_zero]
  rw [hvr, inner_zero_right, sub_zero]
  simp

/-- The same flux identity in the coordinates of a rigid boundary chart. -/
lemma C1BoundaryChart.graph_vertical_normal_flux_perim
    (c : C1BoundaryChart) (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
      inner ℝ (r • c.placement.linearIsometryEquiv
        (EuclideanSpace.single (Fin.last 2) 1))
        (c.outwardNormal (c.placement (graphMapN c.height y))) = r := by
  rw [C1BoundaryChart.outwardNormal, c.placement.symm_apply_apply,
    ← map_smul, c.placement.linearIsometryEquiv.inner_map_map]
  exact LiquidDrop.graph_vertical_normal_flux_perim c.height y r

/-- Applying the localized first variation of a perimeter minimiser to a vertical graph
test cancels the entire area weight on the forcing side. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.verticalTest_first_variation {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {η : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hη : ContDiff ℝ 1 η) (hη0 : η 0 = 1)
    (hcX : HasCompactSupport (c.verticalTest ζ η))
    (hsX : tsupport (c.verticalTest ζ η) ⊆ c.region) :
    (∫ y, Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
      tangentialDivergence (c.verticalTest ζ η) c.outwardNormal
        (c.placement (graphMapN c.height y))) =
      ∫ y, perimeterMinimizerMultiplier V Ω * ζ y := by
  have he := hmin.first_variation_chart hV hΩo hC1 hc (c.contDiff_verticalTest hζ hη) hcX hsX
  rw [c.integral_graphSurface, c.integral_graphSurface] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with y
  rw [c.verticalTest_graph ζ hη0]
  calc
    _ = perimeterMinimizerMultiplier V Ω *
        (Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
          inner ℝ (ζ y • c.placement.linearIsometryEquiv
            (EuclideanSpace.single (Fin.last 2) 1))
            (c.outwardNormal (c.placement (graphMapN c.height y)))) := by ring
    _ = _ := by rw [c.graph_vertical_normal_flux_perim]

/-- Blueprint `lem:graph-PMC` with `v_Ω = 0`, forward direction: for a perimeter
minimiser every closed-slab-supported smooth graph variation satisfies the weak
constant-mean-curvature equation with multiplier `2P / (3V)`. -/
theorem IsLebesgueFixedVolumePerimeterMinimizer.graph_prescribed_mean_curvature {V : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (hΩo : IsOpen Ω) (hC1 : HasC1Boundary Ω)
    (hmin : IsLebesgueFixedVolumePerimeterMinimizer V Ω)
    (c : C1BoundaryChart) (hc : c.IsChartFor Ω)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (_hcζ : HasCompactSupport ζ) {δ : ℝ} (hδ : 0 < δ)
    (hslab : ∀ y ∈ tsupport ζ, ∀ t : ℝ, |t - c.height y| ≤ δ →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈
        c.region) :
    (∫ y, inner ℝ (gradient c.height y) (gradient ζ y) /
      Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) =
      ∫ y, perimeterMinimizerMultiplier V Ω * ζ y := by
  obtain ⟨η, hη, hflat, _, hcX, hsX⟩ := c.exists_verticalTest hζ hδ hslab
  have hz : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have he := hmin.verticalTest_first_variation hV hΩo hC1 hc hz hη hflat.eq_of_nhds hcX hsX
  simpa only [c.tangentialDivergence_verticalTest_graph hz hflat] using he

end LiquidDrop
