module

public import NoCompromise.Regularity.TiltAnalyticData
public import NoCompromise.Regularity.GraphAffineHeightBound
public import NoCompromise.Regularity.TiltSmallness
public import NoCompromise.Regularity.TiltReversePoincare
public import NoCompromise.Regularity.TiltZero
public import NoCompromise.Regularity.HeightBound
public import NoCompromise.Regularity.ExcessDecayCoordinates
public import NoCompromise.Regularity.ExcessDecayScale

@[expose] public section

/-! # Uniform tilt improvement and fixed-scale excess decay -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

/-- Full blueprint `lem:tilt-improvement`. The actual graph, harmonic
approximant, boundary height moment, and tilted slab-and-cap configuration
are constructed from quasiminimality and small excess. -/
theorem tilt_improvement :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 / 32 → ∃ ε > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧
        ‖ν - EuclideanSpace.single 2 1‖ ≤
          C * Real.sqrt (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) + ω) ∧
        cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 θ ν ≤
          C * θ ^ 2 * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
            (EuclideanSpace.single 2 1) + C * θ * ω := by
  obtain ⟨Cg, hCg, Cb, hCb, Ch, hCh, hdata⟩ := exists_tilt_analytic_data
  obtain ⟨Ca, hCa, haffine⟩ := harmonic_affine_integral
  let K := 4 * (1 + Ca * Cb) + 8 * (256 * Cg) * (1 + Ch ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := max 1 (max (2 * Ch) (reversePoincareConstant * (K + 2)))
  have hC : 1 ≤ C := le_max_left _ _
  have hChC : 2 * Ch ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : reversePoincareConstant * (K + 2) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, fun θ hθ hθ32 => ?_⟩
  let τ := θ ^ 3 / 1024
  obtain ⟨hτ, hτsmall, hτsq, hτθ, hτ4⟩ := tilt_slab_width hθ (by linarith)
  obtain ⟨εa, hεa, hda⟩ := hdata θ hθ τ hτ
  obtain ⟨εh, hεh, hheight⟩ := height_bound hτ
  let ε := min εa (min εh (min (θ ^ 6) ((θ / (1024 * Ch)) ^ 2)))
  have hCh0 : 0 < Ch := by linarith
  have hε : 0 < ε := lt_min hεa (lt_min hεh (lt_min (by positivity) (by positivity)))
  refine ⟨ε, hε, fun E ω hE h0 hsmall => ?_⟩
  let e := cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
    (EuclideanSpace.single 2 1)
  have he : 0 ≤ e := by
    simpa only [e, cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable
        (cylinder 0 1 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
  have hs : 0 ≤ e + ω := add_nonneg he hE.nonneg
  by_cases hz : e + ω = 0
  · obtain ⟨_, hzero⟩ := hE.excess_zero_of_sum_zero
      (by simp : ‖(EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ = 1) hz
      (by linarith : θ ≤ 1)
    refine ⟨EuclideanSpace.single 2 1, by simp, ?_, ?_⟩
    · simp only [sub_self, norm_zero]
      exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    · rw [hzero]
      exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg θ)) he)
        (mul_nonneg (mul_nonneg (by linarith) hθ.le) hE.nonneg)
  have hspos : 0 < e + ω := lt_of_le_of_ne hs (Ne.symm hz)
  have hsmall_a : e + ω ≤ εa := hsmall.trans (min_le_left _ _)
  have hsmall_h : e + ω ≤ εh := hsmall.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall_θ : e + ω ≤ θ ^ 6 := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall_Ch : e + ω ≤ (θ / (1024 * Ch)) ^ 2 := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hphase, _, G, f, h, hG, hGB, hf, hfheight, hgraph, hloss,
      hif, hfenergy, hm, hcs, hh1, hdh, hlap, hnorm, hhenergy, hhcenter⟩ :=
    hda E ω hE h0 hspos hsmall_a
  let a := Real.sqrt (e + ω)
  have ha : 0 < a := Real.sqrt_pos.mpr hspos
  have hasq : a ^ 2 = e + ω := Real.sq_sqrt hs
  have ha2 : a ^ 2 ≤ θ ^ 6 := by rwa [hasq]
  have hac : a * Ch ≤ θ / 1024 := tilt_sqrt_smallness hθ hCh0 hsmall_Ch
  have hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < τ := by
    have ht := hheight E ω hE h0 1 (by norm_num) (by norm_num)
      (by simpa only [mul_one] using hsmall_h)
    simpa only [mul_one] using ht
  let p := a • gradient h 0
  let b := (⨍ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f x) + a * h 0
  let Q := verticalAxisIsometry (graphUnitNormal p)
  have hQ : Q (EuclideanSpace.single 2 1) = graphUnitNormal p :=
    verticalAxisIsometry_apply_vertical (norm_graphUnitNormal p)
  obtain ⟨_, _, hclose, hclear, hslab⟩ := tilt_affine_smallness (gradient h 0)
    hθ (by linarith) ha.le hτsmall hac hm hhcenter
  have hconfig := hphase.tilted_slab_cap_configuration hE p Q hQ hθ
    (by linarith) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    hτ hτ4 hτθ hclose hclear hslab hh
  have hgradint : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
      ‖gradient h x‖ ^ 2) ≤ Cb := by
    have hi := hh1.memLp_function.integrable_norm_pow (by norm_num : 2 ≠ 0)
    have hj := hh1.memLp_gradient.integrable_norm_pow (by norm_num : 2 ≠ 0)
    have ht := setIntegral_mono hj (hi.add hj) (fun x =>
      le_add_of_nonneg_left (sq_nonneg ‖h x‖))
    exact ht.trans (by simpa only [Real.norm_eq_abs, Pi.add_apply] using hhenergy)
  have haff : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (4 * θ),
      ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2) ≤ (Ca * Cb) * θ ^ 6 := by
    apply (haffine h hdh hcs.continuousOn hh1.memLp_gradient θ hθ hθ32).trans
    have ht := mul_le_mul_of_nonneg_left hgradint
      (mul_nonneg hCa.le (pow_nonneg hθ.le 6))
    nlinarith only [ht]
  have hloss' : (hausdorffMeasure2 3).real
      ((reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) \
        graphMap f '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) ≤ (256 * Cg) * a ^ 2 := by
    have ht := (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans hloss
    rw [hasq]
    exact ht.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE.nonneg)
      (by positivity))
  have hboundary : ∀ z ∈ reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩
      standardCylinder (1 / 2), |z 2| ≤ τ := by
    intro z hz
    exact (hh z ⟨hE.reducedBoundary_subset_frontier hz.1,
      ⟨hz.2.1.trans_le (by norm_num), hz.2.2.trans_le (by norm_num)⟩⟩).le
  have hmoment := graphAffineHeight_tilt_moment E hE.locallyFinite hE.nullMeasurable
    hf (by change (1 / 16 : ℝ) ≤ 1; norm_num) hh1 hcs.continuousOn ha hτ.le
    (by linarith only [hCh] : 0 ≤ Ch)
    (by positivity : 0 ≤ 256 * Cg) hθ hθ32 ha2 hτsq hfheight hboundary
    (by linarith [norm_nonneg (gradient h 0)] : |h 0| ≤ Ch)
    (by linarith [abs_nonneg (h 0)] : ‖gradient h 0‖ ≤ Ch) hloss' hnorm haff
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area,
    Measure.restrict_restrict (isOpen_cylinder _ _ _).measurableSet] at hmoment
  have hmoment' : (∫ y in cylinder 0 (2 * θ) (Q (EuclideanSpace.single 2 1)) ∩
      reducedBoundary E hE.locallyFinite hE.nullMeasurable,
      (inner ℝ (Q (EuclideanSpace.single 2 1)) y - b / Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2
        ∂hausdorffMeasure2 3) ≤ K * (e + ω) * θ ^ 6 := by
    rw [hQ, ← hasq]
    exact hmoment
  have himprove := hE.tilt_excess_of_height_bound Q hθ hθ32 hK hconfig hmoment'
  rw [hQ] at himprove
  refine ⟨graphUnitNormal p, norm_graphUnitNormal p, ?_, himprove.trans ?_⟩
  · have hp : ‖p‖ ≤ a * Ch := by
      dsimp only [p]
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      apply mul_le_mul_of_nonneg_left _ ha.le
      linarith only [hhcenter, abs_nonneg (h 0)]
    have hb := graphUnitNormal_sub_vertical_le p
    have hc := mul_le_mul_of_nonneg_right hChC ha.le
    change ‖graphUnitNormal p - EuclideanSpace.single 2 1‖ ≤ C * a
    nlinarith only [hb, hp, hc]
  · have h1 := mul_le_mul_of_nonneg_right hKC (mul_nonneg (sq_nonneg θ) he)
    have h2 := mul_le_mul_of_nonneg_right hKC (mul_nonneg hθ.le hE.nonneg)
    nlinarith only [h1, h2]

/-- Blueprint `cor:excess-decay`, at every boundary center and unit axis.
The fixed contraction scale is chosen after the universal tilt constant, and
the smallness threshold precedes the set, center, radius, and axis. The normal
increment from tilt improvement is retained for the subsequent iteration. -/
theorem excess_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν + ω * r ≤ ε →
      ∃ ν' : AmbientSpace, ‖ν'‖ = 1 ∧
        ‖ν' - ν‖ ≤ C * Real.sqrt
          (cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν + ω * r) ∧
        cylindricalExcess E hE.locallyFinite hE.nullMeasurable x
            (excessDecayScale C * r) ν' ≤
          excessDecayScale C / 2 * cylindricalExcess E hE.locallyFinite hE.nullMeasurable
            x r ν + C * excessDecayScale C * ω * r := by
  obtain ⟨C, hC, htilt⟩ := tilt_improvement
  obtain ⟨hθ, hθ32, hθsq, _⟩ := excessDecayScale_bounds hC
  obtain ⟨ε, hε, hstep⟩ := htilt (excessDecayScale C) hθ hθ32
  refine ⟨C, hC, ε, hε, ?_⟩
  intro E ω hE x r ν hr hr1 hν hx hsmall
  have hF := hE.excessDecayCoordinates x hr hr1 ν
  have h0 : (0 : AmbientSpace) ∈ frontier (densityOne (excessDecayCoordinates E x r ν)) :=
    (excessDecayCoordinates_origin_frontier E x ν hr).mpr hx
  have hunit := cylindricalExcess_excessDecayCoordinates_unit hE x ν hr hr1 hν
  have hsmall' : cylindricalExcess (excessDecayCoordinates E x r ν)
      hF.locallyFinite hF.nullMeasurable 0 1 (EuclideanSpace.single 2 1) + ω * r ≤ ε := by
    rw [hunit]
    exact hsmall
  obtain ⟨ξ, hξ, hclose, hdecay⟩ := hstep _ (ω * r) hF h0 hsmall'
  rw [hunit] at hclose hdecay
  rw [cylindricalExcess_excessDecayCoordinates hE x ν hr hr1,
    mul_comm r (excessDecayScale C)] at hdecay
  refine ⟨verticalAxisIsometry ν ξ, ?_, ?_, hdecay.trans ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map] using hξ
  · calc
      ‖verticalAxisIsometry ν ξ - ν‖ = ‖ξ - EuclideanSpace.single 2 1‖ := by
        simpa only [verticalAxisIsometry_apply_vertical hν, dist_eq_norm] using
          (verticalAxisIsometry ν).dist_map ξ (EuclideanSpace.single 2 1)
      _ ≤ _ := hclose
  · have he : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν :=
      div_nonneg (normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable _ _)
        (sq_nonneg r)
    have hcoef : C * excessDecayScale C ^ 2 ≤ excessDecayScale C / 2 :=
      hθsq.trans (by linarith only [hθ])
    have hb := mul_le_mul_of_nonneg_right hcoef he
    nlinarith only [hb]

end LiquidDrop
