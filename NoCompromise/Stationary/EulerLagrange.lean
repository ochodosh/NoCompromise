module

public import NoCompromise.Stationary.MinimizerContext
public import NoCompromise.Variation.Perimeter
public import NoCompromise.Variation.VolumeBoundary
public import NoCompromise.Variation.CoulombBoundary
public import NoCompromise.Energy.Scaling

@[expose] public section

/-!
# The constrained first variation

Blueprint `thm:constrained-first-var`. Instead of the implicit-function argument,
the volume constraint is restored by a dilation: for small `t`, the straight image
`F_t` is rescaled by `r(t) = (V / |F_t|)^{1/3}`. The rescaled set is an admissible
competitor, so `r(t)² P(F_t) + r(t)⁵ D(F_t)` has a local minimum at `t = 0`. The
first variations of perimeter, Coulomb energy and volume then give the weak
Euler--Lagrange equation with the explicit multiplier `(2P + 5D) / (3V)`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The Lagrange multiplier of a fixed-volume minimizer, given by the scaling identity. -/
noncomputable def minimizerMultiplier (V : ℝ) (Ω : Set AmbientSpace) : ℝ :=
  (2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal) / (3 * V)

lemma straightPerturbation_zero_image (X : AmbientSpace → AmbientSpace) (E : Set AmbientSpace) :
    straightPerturbation X 0 '' E = E := by
  have h : straightPerturbation X 0 = id := funext fun x => by simp [straightPerturbation]
  rw [h, image_id]

/-- A small straight perturbation of a finite-perimeter set has finite perimeter. -/
lemma perimeter_straight_image_lt_top
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hfin : perimeter E < ∞)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {t : ℝ} (ht : |t| * ‖straightDerivativeField hX hcX‖ < 1) :
    perimeter (straightPerturbation X t '' E) < ∞ := by
  obtain ⟨Φ, heq, hΦ, hiΦ, hD, _, _⟩ :=
    straightPerturbation_compactlySupported_diffeomorphism hX hcX ht
  have hcoe : (Φ : AmbientSpace → AmbientSpace) = straightPerturbation X t := funext heq
  have hF := hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Φ hΦ hiΦ E hE hmE
  have hmF := nullMeasurableSet_image_of_differentiable
    (hΦ.differentiable one_ne_zero) Φ.injective hmE
  obtain ⟨s, hs, hsgn⟩ := exists_fixed_orientation_of_continuous_det hΦ
    (det_fderiv_ne_zero_of_differentiable_inverse Φ
      (hΦ.differentiable one_ne_zero) (hiΦ.differentiable one_ne_zero))
  have hp := perimeter_transport_C1 Φ hΦ hiΦ E hE hmE hF hmF hs hsgn MeasurableSet.univ
  rw [image_univ, Φ.surjective.range_eq, canonicalPerimeterMeasure_open _ hF hmF isOpen_univ,
    Measure.restrict_univ] at hp
  have hper : perimeter (Φ '' E) = perimeterIn (Φ '' E) univ := by
    rw [← perimeterN_eq_perimeter _ hmF]; rfl
  rw [← hcoe, hper, hp]
  let μ := canonicalPerimeterMeasure E hE hmE
  have hμ : μ univ < ∞ := by
    rw [canonicalPerimeterMeasure_open E hE hmE isOpen_univ]
    change perimeterN E < ∞
    rwa [perimeterN_eq_perimeter E hmE]
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : AmbientSpace →L[ℝ] AmbientSpace) 2).exists_bound_of_continuousOn
      continuous_cofactor3.continuousOn
  have hbound : ∀ᵐ x ∂μ, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
      (canonicalOutwardPolarDensity E hE hmE x)‖ ≤ ENNReal.ofReal C := by
    filter_upwards [(canonicalPerimeterPolar E hE hmE).norm_ae] with x hx
    apply ENNReal.ofReal_le_ofReal
    have hA : fderiv ℝ Φ x ∈ closedBall (0 : AmbientSpace →L[ℝ] AmbientSpace) 2 := by
      rw [mem_closedBall, dist_zero_right, (hD x).1]
      calc
        ‖ContinuousLinearMap.id ℝ AmbientSpace + t • fderiv ℝ X x‖ ≤
            ‖ContinuousLinearMap.id ℝ AmbientSpace‖ + ‖t • fderiv ℝ X x‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by
          gcongr
          · exact ContinuousLinearMap.norm_id_le
          · rw [norm_smul, Real.norm_eq_abs]
            calc
              |t| * ‖fderiv ℝ X x‖ ≤ |t| * ‖straightDerivativeField hX hcX‖ := by
                gcongr; exact norm_fderiv_le_straightDerivativeField hX hcX x
              _ ≤ 1 := ht.le
        _ = 2 := by norm_num
    calc
      ‖cofactor3 (fderiv ℝ Φ x) (canonicalOutwardPolarDensity E hE hmE x)‖ ≤
          ‖cofactor3 (fderiv ℝ Φ x)‖ * ‖canonicalOutwardPolarDensity E hE hmE x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by rw [hx, mul_one]; exact hC _ hA
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal C ∂μ := lintegral_mono_ae hbound
    _ = ENNReal.ofReal C * μ univ := lintegral_const _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ

/-- The normal flux of a continuous compactly supported field is integrable on the
reduced boundary. -/
lemma integrableOn_normal_flux {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {X : AmbientSpace → AmbientSpace} (hX : Continuous X) (hcX : HasCompactSupport X) :
    IntegrableOn (fun x => inner ℝ (X x) (reducedNormal E hE hmE x))
      (reducedBoundary E hE hmE) (hausdorffMeasure2 3) := by
  have h := reducedBoundary_outwardPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  have hm : Measurable (fun x => inner ℝ (X x) (reducedNormal E hE hmE x)) :=
    (continuous_inner (𝕜 := ℝ)).measurable.comp (hX.measurable.prodMk h.measurable)
  apply (hX.norm.integrable_of_hasCompactSupport hcX.norm).mono' hm.aestronglyMeasurable
  filter_upwards [h.norm_ae] with x hx
  simpa only [hx, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (X x) (reducedNormal E hE hmE x)

/-- The reduced-boundary area measure of a set of finite perimeter is finite. -/
lemma isFiniteMeasure_reducedBoundary {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hfin : perimeter E < ∞) :
    IsFiniteMeasure ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area]
  constructor
  rw [canonicalPerimeterMeasure_open _ _ _ isOpen_univ]
  change perimeterN E < ∞
  rwa [perimeterN_eq_perimeter _ hmE]

/-- The tangential divergence of a compactly supported `C¹` field is integrable on
the reduced boundary of a finite-perimeter set. -/
lemma integrableOn_tangentialDivergence_reducedBoundary {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hfin : perimeter E < ∞)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    IntegrableOn (tangentialDivergence X (reducedNormal E hE hmE))
      (reducedBoundary E hE hmE) (hausdorffMeasure2 3) := by
  have h := reducedBoundary_outwardPerimeterPolar E hE hmE
  let := isFiniteMeasure_reducedBoundary hE hmE hfin
  exact integrable_tangentialDivergence hX hcX h.measurable h.norm_ae

/-- The dilation-corrected first variation: for a fixed-volume minimizer the
perimeter and Coulomb first variations sum to the multiplier times the volume
first variation. -/
theorem first_variation_perimeter_add_coulomb_eq {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in reducedBoundary Ω hP hmin.1,
        tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) +
      (∫ x in reducedBoundary Ω hP hmin.1, (coulombPotential Ω x).toReal *
        inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3) =
      minimizerMultiplier V Ω *
        ∫ x in reducedBoundary Ω hP hmin.1,
          inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3 := by
  set Pd := ∫ x in reducedBoundary Ω hP hmin.1,
    tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3
  set Dd := ∫ x in reducedBoundary Ω hP hmin.1, (coulombPotential Ω x).toReal *
    inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3
  set B := ∫ x in reducedBoundary Ω hP hmin.1,
    inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3
  have hvolfin : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have hdP : HasDerivAt (fun t : ℝ => (perimeter (straightPerturbation X t '' Ω)).toReal)
      Pd 0 := first_variation_perimeter_global Ω hP hmin.1 hmin.2.2.1 hX hcX
  have hdD : HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' Ω)).toReal)
      Dd 0 := first_variation_coulomb hP hmin.1 hb hX hcX
  have hdV : HasDerivAt (fun t : ℝ => (volume (straightPerturbation X t '' Ω)).toReal)
      B 0 := first_variation_volume Ω hP hmin.1 hvolfin hX hcX
  set per := fun t : ℝ => (perimeter (straightPerturbation X t '' Ω)).toReal
  set cou := fun t : ℝ => (coulombEnergy (straightPerturbation X t '' Ω)).toReal
  set vol := fun t : ℝ => (volume (straightPerturbation X t '' Ω)).toReal
  have hvol0 : vol 0 = V := by
    simp only [vol, straightPerturbation_zero_image, hmin.2.1, ENNReal.toReal_ofReal hV.le]
  have hper0 : per 0 = (perimeter Ω).toReal := by simp only [per, straightPerturbation_zero_image]
  have hcou0 : cou 0 = (coulombEnergy Ω).toReal := by
    simp only [cou, straightPerturbation_zero_image]
  set q := fun t : ℝ => V / vol t
  have hq0 : q 0 = 1 := by simp only [q, hvol0, div_self hV.ne']
  have hq : HasDerivAt q ((0 * vol 0 - V * B) / vol 0 ^ 2) 0 :=
    (hasDerivAt_const (0 : ℝ) V).div hdV (by rw [hvol0]; exact hV.ne')
  set r := fun t : ℝ => q t ^ (1 / 3 : ℝ)
  have hr0 : r 0 = 1 := by simp only [r, hq0, Real.one_rpow]
  have hr : HasDerivAt r ((0 * vol 0 - V * B) / vol 0 ^ 2 * (1 / 3 : ℝ) *
      q 0 ^ ((1 / 3 : ℝ) - 1)) 0 :=
    hq.rpow_const (Or.inl (by rw [hq0]; exact one_ne_zero))
  set g := fun t : ℝ => r t ^ 2 * per t + r t ^ 5 * cou t
  have hg := ((hr.pow 2).mul hdP).add ((hr.pow 5).mul hdD)
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
    have hDF := coulombEnergy_lt_top F (lt_top_iff_ne_top.2 hFfin)
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
    rw [energy_smul hmF hrt, energy] at hE
    have hfinR : ENNReal.ofReal (r t ^ 2) * perimeter F +
        ENNReal.ofReal (r t ^ 5) * coulombEnergy F ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPF.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDF.ne⟩
    have hR := ENNReal.toReal_mono hfinR hE
    rw [ENNReal.toReal_add hmin.2.2.1.ne
        (coulombEnergy_lt_top Ω hvolfin).ne,
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPF.ne)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDF.ne),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hrt.le 2),
      ENNReal.toReal_ofReal (pow_nonneg hrt.le 5)] at hR
    change r 0 ^ 2 * per 0 + r 0 ^ 5 * cou 0 ≤ r t ^ 2 * per t + r t ^ 5 * cou t
    rw [hr0, hper0, hcou0]
    simpa only [one_pow, one_mul] using hR
  have hzero := hmin0.hasDerivAt_eq_zero hg
  have hk : (0 * V - V * B) / V ^ 2 * (1 / 3 : ℝ) = -(B / (3 * V)) := by
    rw [zero_mul, zero_sub, neg_div, sq, mul_div_mul_left B V hV.ne']
    ring
  simp only [Pi.pow_apply] at hzero
  rw [hr0, hq0, hvol0, hper0, hcou0, Real.one_rpow, hk] at hzero
  rw [minimizerMultiplier]
  linear_combination hzero

/-- Blueprint `thm:constrained-first-var`, reduced-boundary form, with the explicit
multiplier `λ = (2P + 5D) / (3V)`. -/
theorem constrained_first_variation_eq {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in reducedBoundary Ω hP hmin.1,
        tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
      ∫ x in reducedBoundary Ω hP hmin.1,
        (minimizerMultiplier V Ω - (coulombPotential Ω x).toReal) *
          inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3 := by
  have hkey := first_variation_perimeter_add_coulomb_eq hV hmin hb hP hX hcX
  have hiB := integrableOn_normal_flux hP hmin.1 hX.continuous hcX
  have hiD := integrableOn_coulomb_boundary_flux hP hmin.1 hb hX.continuous hcX
  simp_rw [sub_mul]
  rw [integral_sub (Integrable.const_mul hiB _) hiD, integral_const_mul]
  linarith

/-- The `A(X) = λ B(X)` form of the constrained first variation. -/
theorem constrained_first_variation_multiplier {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in reducedBoundary Ω hP hmin.1,
        (tangentialDivergence X (reducedNormal Ω hP hmin.1) x +
          (coulombPotential Ω x).toReal * inner ℝ (X x) (reducedNormal Ω hP hmin.1 x))
        ∂hausdorffMeasure2 3) =
      minimizerMultiplier V Ω *
        ∫ x in reducedBoundary Ω hP hmin.1,
          inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3 := by
  rw [integral_add (integrableOn_tangentialDivergence_reducedBoundary hP hmin.1 hmin.2.2.1 hX hcX)
    (integrableOn_coulomb_boundary_flux hP hmin.1 hb hX.continuous hcX)]
  exact first_variation_perimeter_add_coulomb_eq hV hmin hb hP hX hcX

/-- Existence of a Lagrange multiplier for the weak Euler--Lagrange equation. -/
theorem exists_constrained_first_variation {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω) :
    ∃ lam : ℝ, ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x in reducedBoundary Ω hP hmin.1,
          tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
        ∫ x in reducedBoundary Ω hP hmin.1,
          (lam - (coulombPotential Ω x).toReal) *
            inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3 :=
  ⟨minimizerMultiplier V Ω, fun _ hX hcX => constrained_first_variation_eq hV hmin hb hP hX hcX⟩

/-- The constrained first variation for the fixed minimizer representative, integrated
over the whole `C¹` frontier with the canonical outward normal. -/
theorem MinimizerRep.constrained_first_variation {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in frontier Ω, tangentialDivergence X
        (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet) x
        ∂hausdorffMeasure2 3) =
      ∫ x in frontier Ω, (minimizerMultiplier V Ω - (coulombPotential Ω x).toReal) *
        inner ℝ (X x) (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet x)
        ∂hausdorffMeasure2 3 := by
  rw [Measure.restrict_congr_set
    (h.c1Boundary.boundary_ae_eq_reducedBoundary h.isOpen h.hasLocallyFinitePerimeter)]
  exact constrained_first_variation_eq h.volume_pos h.minimizer h.bounded
    h.hasLocallyFinitePerimeter hX hcX

/-- The graph area weight cancels the normal component of a vertical field.
This is the flux calculation needed for the right side of the graph equation. -/
private lemma graph_vertical_normal_flux
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
private lemma C1BoundaryChart.graph_vertical_normal_flux
    (c : C1BoundaryChart) (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
      inner ℝ (r • c.placement.linearIsometryEquiv
        (EuclideanSpace.single (Fin.last 2) 1))
        (c.outwardNormal (c.placement (graphMapN c.height y))) = r := by
  rw [C1BoundaryChart.outwardNormal, c.placement.symm_apply_apply,
    ← map_smul, c.placement.linearIsometryEquiv.inner_map_map]
  exact LiquidDrop.graph_vertical_normal_flux c.height y r

/-- The vertical variation in a rigid graph chart, with a cutoff in distance
along the vertical coordinate from the graph. -/
def C1BoundaryChart.verticalTest (c : C1BoundaryChart)
    (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) (η : ℝ → ℝ) (x : AmbientSpace) : AmbientSpace :=
  (ζ (graphProjectionN 2 (c.placement.symm x)) *
    η ((c.placement.symm x) (Fin.last 2) -
      c.height (graphProjectionN 2 (c.placement.symm x)))) •
    c.placement.linearIsometryEquiv (EuclideanSpace.single (Fin.last 2) 1)

lemma C1BoundaryChart.contDiff_verticalTest (c : C1BoundaryChart)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {η : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hη : ContDiff ℝ 1 η) :
    ContDiff ℝ 1 (c.verticalTest ζ η) := by
  have hp := contDiff_rigidPlacement c.placement.symm
  have hb := (graphProjectionN 2).contDiff.comp hp
  have ht := (EuclideanSpace.proj (Fin.last 2)).contDiff.comp hp
  exact ((hζ.comp hb).mul (hη.comp (ht.sub (c.height_contDiff.comp hb)))).smul
    contDiff_const

lemma C1BoundaryChart.verticalTest_graph (c : C1BoundaryChart)
    (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) {η : ℝ → ℝ} (hη : η 0 = 1)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c.verticalTest ζ η (c.placement (graphMapN c.height y)) =
      ζ y • c.placement.linearIsometryEquiv (EuclideanSpace.single (Fin.last 2) 1) := by
  have hp : graphProjectionN 2 (graphMapN c.height y) = y :=
    graphProjectionN_append y (c.height y)
  simp only [verticalTest, c.placement.symm_apply_apply, hp, graphMapN_last,
    sub_self, hη, mul_one]

/-- The support of the vertical test is contained in the closed chart slab. -/
lemma C1BoundaryChart.tsupport_verticalTest_subset (c : C1BoundaryChart)
    (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) {η : ℝ → ℝ} {δ : ℝ}
    (hη : tsupport η ⊆ Set.Icc (-δ) δ)
    (hslab : ∀ y ∈ tsupport ζ, ∀ t : ℝ, |t - c.height y| ≤ δ →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈
        c.region) :
    tsupport (c.verticalTest ζ η) ⊆ c.region := by
  let b := fun x : AmbientSpace => graphProjectionN 2 (c.placement.symm x)
  let t := fun x : AmbientSpace =>
    (c.placement.symm x) (Fin.last 2) - c.height (b x)
  have hb : Continuous b := (graphProjectionN 2).continuous.comp c.placement.symm.continuous
  have ht : Continuous t :=
    ((EuclideanSpace.proj (Fin.last 2)).continuous.comp c.placement.symm.continuous).sub
      (c.height_contDiff.continuous.comp hb)
  have hs : tsupport (c.verticalTest ζ η) ⊆
      b ⁻¹' tsupport ζ ∩ t ⁻¹' tsupport η := by
    apply closure_minimal
    · intro x hx
      have hz : ζ (b x) ≠ 0 := by
        intro hz
        exact hx (by simp [verticalTest, b, hz])
      have he : η (t x) ≠ 0 := by
        intro he
        exact hx (by simp [verticalTest, b, t] at he ⊢; simp_all)
      exact ⟨subset_tsupport _ hz, subset_tsupport _ he⟩
    · exact ((isClosed_tsupport ζ).preimage hb).inter ((isClosed_tsupport η).preimage ht)
  intro x hx
  have hx' := hs hx
  have h := hslab (b x) hx'.1 ((c.placement.symm x) (Fin.last 2))
    (abs_le.mpr (hη hx'.2))
  change c.placement (graphAppendN (graphProjectionN 2 (c.placement.symm x))
    ((c.placement.symm x) (Fin.last 2))) ∈ c.region at h
  simpa only [graphAppendN_projection, c.placement.apply_symm_apply] using h

/-- Boundedness of the chart makes a slab-supported vertical test compactly supported. -/
lemma C1BoundaryChart.hasCompactSupport_verticalTest (c : C1BoundaryChart)
    (ζ : EuclideanSpace ℝ (Fin 2) → ℝ) {η : ℝ → ℝ} {δ : ℝ}
    (hη : tsupport η ⊆ Set.Icc (-δ) δ)
    (hslab : ∀ y ∈ tsupport ζ, ∀ t : ℝ, |t - c.height y| ≤ δ →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈
        c.region) :
    HasCompactSupport (c.verticalTest ζ η) :=
  (c.bounded_region.subset
      (c.tsupport_verticalTest_subset ζ hη hslab)).isCompact_closure.of_isClosed_subset
    (isClosed_tsupport _) subset_closure

/-- A scalar integrand vanishing outside a chart has the same integral on the
actual frontier and on the complete placed graph. -/
lemma C1BoundaryChart.IsChartFor.integral_frontier_eq_graphSurface
    {c : C1BoundaryChart} {Ω : Set AmbientSpace} (hc : c.IsChartFor Ω)
    {g : AmbientSpace → ℝ} (hg : ∀ x, x ∉ c.region → g x = 0) :
    (∫ x in frontier Ω, g x ∂hausdorffMeasure2 3) =
      ∫ x in c.graphSurface, g x ∂hausdorffMeasure2 3 := by
  calc
    _ = ∫ x in c.region, g x ∂(hausdorffMeasure2 3).restrict (frontier Ω) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hg).symm
    _ = ∫ x in c.region, g x ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
      rw [hc.boundaryArea_restrict]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hg

/-- The weak first variation localized to a single rigid graph chart, expressed
using its classical outward normal. -/
theorem MinimizerRep.constrained_first_variation_chart {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    (hsX : tsupport X ⊆ c.region) :
    (∫ x in c.graphSurface, tangentialDivergence X c.outwardNormal x ∂hausdorffMeasure2 3) =
      ∫ x in c.graphSurface, (minimizerMultiplier V Ω - (coulombPotential Ω x).toReal) *
        inner ℝ (X x) (c.outwardNormal x) ∂hausdorffMeasure2 3 := by
  have hzero (x : AmbientSpace) (hx : x ∉ c.region) : x ∉ tsupport X :=
    fun hx' => hx (hsX hx')
  have hleft := hc.integral_frontier_eq_graphSurface
    (g := tangentialDivergence X c.outwardNormal)
    (fun x hx => tangentialDivergence_eq_zero_of_notMem_tsupport (hzero x hx))
  have hright := hc.integral_frontier_eq_graphSurface
    (g := fun x => (minimizerMultiplier V Ω - (coulombPotential Ω x).toReal) *
      inner ℝ (X x) (c.outwardNormal x))
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (hzero x hx), inner_zero_left, mul_zero])
  rw [← hleft, ← hright]
  have hn := hc.reduced_normal_eq_ae h.c1Boundary h.isOpen h.hasLocallyFinitePerimeter
  calc
    _ = ∫ x in frontier Ω, tangentialDivergence X
        (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet) x
        ∂hausdorffMeasure2 3 := by
      apply integral_congr_ae
      filter_upwards [hn] with x hx
      by_cases hr : x ∈ c.region
      · simp only [tangentialDivergence, hx hr]
      · rw [tangentialDivergence_eq_zero_of_notMem_tsupport (hzero x hr),
          tangentialDivergence_eq_zero_of_notMem_tsupport (hzero x hr)]
    _ = _ := h.constrained_first_variation hX hcX
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hn] with x hx
      by_cases hr : x ∈ c.region
      · rw [hx hr]
      · rw [image_eq_zero_of_notMem_tsupport (hzero x hr), inner_zero_left, inner_zero_left]

/-- Integration on a rigidly placed graph in its base coordinates. -/
lemma C1BoundaryChart.integral_graphSurface (c : C1BoundaryChart)
    (g : AmbientSpace → ℝ) :
    (∫ x in c.graphSurface, g x ∂hausdorffMeasure2 3) =
      ∫ y, Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
        g (c.placement (graphMapN c.height y)) := by
  have ha : MeasurableEmbedding (c.placement : AmbientSpace → AmbientSpace) :=
    c.placement.toHomeomorph.measurableEmbedding
  rw [graphSurface, hausdorffMeasure2_restrict_affineIsometry_image, ha.integral_map]
  exact integral_smoothGraphArea c.height_contDiff (fun z => g (c.placement z))

/-- A smooth vertical cutoff with the exact slab support and a flat neighborhood
of the graph. -/
lemma exists_vertical_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ tsupport η ⊆ Set.Icc (-δ) δ ∧
      η =ᶠ[𝓝 0] (fun _ => 1) := by
  let η : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨η, η.contDiff, ?_, η.eventuallyEq_one⟩
  intro t ht
  rw [η.tsupport_eq] at ht
  exact abs_le.mp (by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht)

/-- Admissible vertical tests exist under precisely the closed-slab hypothesis. -/
theorem C1BoundaryChart.exists_verticalTest (c : C1BoundaryChart)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    {δ : ℝ} (hδ : 0 < δ)
    (hslab : ∀ y ∈ tsupport ζ, ∀ t : ℝ, |t - c.height y| ≤ δ →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈
        c.region) :
    ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ η =ᶠ[𝓝 0] (fun _ => 1) ∧
      ContDiff ℝ 1 (c.verticalTest ζ η) ∧ HasCompactSupport (c.verticalTest ζ η) ∧
      tsupport (c.verticalTest ζ η) ⊆ c.region := by
  obtain ⟨η, hη, hsη, hflat⟩ := exists_vertical_cutoff hδ
  exact ⟨η, hη, hflat, c.contDiff_verticalTest (hζ.of_le (by simp)) hη,
    c.hasCompactSupport_verticalTest ζ hsη hslab,
    c.tsupport_verticalTest_subset ζ hsη hslab⟩

/-- Applying the localized first variation to a vertical graph test cancels the
entire area weight on the forcing side. -/
theorem MinimizerRep.verticalTest_first_variation {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {η : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hη : ContDiff ℝ 1 η) (hη0 : η 0 = 1)
    (hcX : HasCompactSupport (c.verticalTest ζ η))
    (hsX : tsupport (c.verticalTest ζ η) ⊆ c.region) :
    (∫ y, Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
      tangentialDivergence (c.verticalTest ζ η) c.outwardNormal
        (c.placement (graphMapN c.height y))) =
      ∫ y, (minimizerMultiplier V Ω -
        (coulombPotential Ω (c.placement (graphMapN c.height y))).toReal) * ζ y := by
  have he := h.constrained_first_variation_chart hc (c.contDiff_verticalTest hζ hη) hcX hsX
  rw [c.integral_graphSurface, c.integral_graphSurface] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with y
  rw [c.verticalTest_graph ζ hη0]
  calc
    _ = (minimizerMultiplier V Ω -
        (coulombPotential Ω (c.placement (graphMapN c.height y))).toReal) *
        (Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
          inner ℝ (ζ y • c.placement.linearIsometryEquiv
            (EuclideanSpace.single (Fin.last 2) 1))
            (c.outwardNormal (c.placement (graphMapN c.height y)))) := by ring
    _ = _ := by rw [c.graph_vertical_normal_flux]

/-- The derivative of a vertical test on the graph does not see the flat cutoff. -/
lemma C1BoundaryChart.fderiv_verticalTest_graph (c : C1BoundaryChart)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {η : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hflat : η =ᶠ[𝓝 0] (fun _ => 1))
    (y : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (c.verticalTest ζ η) (c.placement (graphMapN c.height y)) =
      ((fderiv ℝ ζ y).comp ((graphProjectionN 2).comp
        c.placement.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap)
          ).smulRight
        (c.placement.linearIsometryEquiv (EuclideanSpace.single (Fin.last 2) 1)) := by
  let b := fun x : AmbientSpace => graphProjectionN 2 (c.placement.symm x)
  let t := fun x : AmbientSpace =>
    (c.placement.symm x) (Fin.last 2) - c.height (b x)
  have hb : b (c.placement (graphMapN c.height y)) = y := by
    simp only [b, c.placement.symm_apply_apply]
    exact graphProjectionN_append y (c.height y)
  have ht : t (c.placement (graphMapN c.height y)) = 0 := by
    simp only [t, hb, c.placement.symm_apply_apply, graphMapN_last, sub_self]
  have hct : Continuous t :=
    ((EuclideanSpace.proj (Fin.last 2)).continuous.comp c.placement.symm.continuous).sub
      (c.height_contDiff.continuous.comp
        ((graphProjectionN 2).continuous.comp c.placement.symm.continuous))
  have he : (fun x => η (t x)) =ᶠ[𝓝 (c.placement (graphMapN c.height y))] (fun _ => 1) :=
    hflat.comp_tendsto (ht ▸ hct.continuousAt.tendsto)
  have hd := (graphProjectionN 2).hasFDerivAt.comp
    (c.placement (graphMapN c.height y))
    (hasFDerivAt_rigidPlacement c.placement.symm (c.placement (graphMapN c.height y)))
  have hz := ((hζ.differentiable one_ne_zero
      (b (c.placement (graphMapN c.height y)))).hasFDerivAt.comp
    (c.placement (graphMapN c.height y)) (show HasFDerivAt b _ _ from hd))
  rw [hb] at hz
  have hv := hz.smul_const
    (c.placement.linearIsometryEquiv (EuclideanSpace.single (Fin.last 2) 1))
  apply HasFDerivAt.fderiv
  apply hv.congr_of_eventuallyEq
  filter_upwards [he] with x hx
  change (ζ (b x) * η (t x)) • _ = ζ (b x) • _
  rw [hx, mul_one]

/-- The trace of a rank-one derivative is its defining functional applied to
its defining vector. -/
lemma divergenceN_of_fderiv_smulRight {X : AmbientSpace → AmbientSpace}
    {x : AmbientSpace} (l : AmbientSpace →L[ℝ] ℝ) (v : AmbientSpace)
    (hD : fderiv ℝ X x = l.smulRight v) : divergenceN X x = l v := by
  have he := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at he
  conv_rhs => rw [← he]
  rw [divergenceN, hD]
  simp only [ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, smul_eq_mul,
    map_sum, map_smul]
  simp [mul_comm]

/-- On the graph, tangential divergence of the flat vertical test gives the
weak mean-curvature integrand, including the graph area factor. -/
lemma C1BoundaryChart.tangentialDivergence_verticalTest_graph (c : C1BoundaryChart)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} {η : ℝ → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hflat : η =ᶠ[𝓝 0] (fun _ => 1))
    (y : EuclideanSpace ℝ (Fin 2)) :
    Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) *
      tangentialDivergence (c.verticalTest ζ η) c.outwardNormal
        (c.placement (graphMapN c.height y)) =
      inner ℝ (gradient c.height y) (gradient ζ y) /
        Real.sqrt (1 + ‖gradient c.height y‖ ^ 2) := by
  let L := c.placement.linearIsometryEquiv
  let v : AmbientSpace := L (EuclideanSpace.single (Fin.last 2) 1)
  let n := c.outwardNormal (c.placement (graphMapN c.height y))
  let Q := Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)
  have hd := c.fderiv_verticalTest_graph hζ hflat y
  have he : graphProjectionN 2 (EuclideanSpace.single (Fin.last 2) (1 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [graphProjectionN_apply]
  have hdiv : divergenceN (c.verticalTest ζ η) (c.placement (graphMapN c.height y)) = 0 := by
    rw [divergenceN_of_fderiv_smulRight _ _ hd]
    change fderiv ℝ ζ y (graphProjectionN 2
      (L.symm (L (EuclideanSpace.single (Fin.last 2) 1)))) = 0
    rw [L.symm_apply_apply, he, map_zero]
  have hp : graphProjectionN 2 (L.symm n) = Q⁻¹ • (-gradient c.height y) := by
    change graphProjectionN 2 (L.symm (L
      (smoothSubgraphNormal c.height (c.placement.symm (c.placement (graphMapN c.height y)))))) = _
    rw [L.symm_apply_apply, c.placement.symm_apply_apply]
    have hbase : graphProjectionN 2 (graphMapN c.height y) = y :=
      graphProjectionN_append y (c.height y)
    simp only [smoothSubgraphNormal, hbase, smoothGraphUnitNormal, map_smul,
      graphProjectionN_append, Q]
  have hn : Q * inner ℝ n v = 1 := by
    have h := c.graph_vertical_normal_flux y 1
    simpa only [one_smul, Q, n, v, L, real_inner_comm] using h
  rw [tangentialDivergence, hdiv, zero_sub, hd]
  change Q * -inner ℝ n ((fderiv ℝ ζ y (graphProjectionN 2 (L.symm n))) • v) = _
  rw [hp, map_smul, map_neg, real_inner_smul_right]
  have hg : fderiv ℝ ζ y (gradient c.height y) =
      inner ℝ (gradient c.height y) (gradient ζ y) := by
    rw [real_inner_comm, inner_gradient_left]
  change Q * -((Q⁻¹ * -fderiv ℝ ζ y (gradient c.height y)) * inner ℝ n v) = _
  calc
    _ = Q⁻¹ * fderiv ℝ ζ y (gradient c.height y) * (Q * inner ℝ n v) := by ring
    _ = _ := by rw [hn, hg]; change _ = _ / Q; ring

/-- Blueprint `lem:graph-PMC`, forward direction: every closed-slab-supported
smooth graph variation satisfies the weak prescribed-mean-curvature equation. -/
theorem MinimizerRep.graph_prescribed_mean_curvature {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) (c : C1BoundaryChart) (hc : c.IsChartFor Ω)
    {ζ : EuclideanSpace ℝ (Fin 2) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (_hcζ : HasCompactSupport ζ) {δ : ℝ} (hδ : 0 < δ)
    (hslab : ∀ y ∈ tsupport ζ, ∀ t : ℝ, |t - c.height y| ≤ δ →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈
        c.region) :
    (∫ y, inner ℝ (gradient c.height y) (gradient ζ y) /
      Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) =
      ∫ y, (minimizerMultiplier V Ω -
        (coulombPotential Ω (c.placement (graphMapN c.height y))).toReal) * ζ y := by
  obtain ⟨η, hη, hflat, _, hcX, hsX⟩ := c.exists_verticalTest hζ hδ hslab
  have hz : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have he := h.verticalTest_first_variation hc hz hη hflat.eq_of_nhds hcX hsX
  simpa only [c.tangentialDivergence_verticalTest_graph hz hflat] using he

end LiquidDrop
