module

public import NoCompromise.BV.LineDistribution
public import NoCompromise.DeGiorgi.HalfspaceRigidity
public import NoCompromise.Area.PlaneSections
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# The actual distributional derivative of a halfspace indicator

Orthogonal line coordinates and the compact one-dimensional fundamental theorem
of calculus give the normal test pairing. Tangential pairings vanish. Linearity
then identifies the complete distributional polar with normalized Hausdorff
area on the boundary plane.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace Function
open scoped Topology ENNReal Gradient CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The negative halfspace with outward normal `ν`. -/
def negativeHalfspace (ν : AmbientSpace) : Set AmbientSpace := {x | inner ℝ ν x < 0}

/-- Normalized area on the plane through the origin perpendicular to `ν`. -/
def halfspacePlaneMeasure (ν : AmbientSpace) : Measure AmbientSpace :=
  (hausdorffMeasure2 3).restrict {x | inner ℝ ν x = 0}

lemma isOpen_negativeHalfspace (ν : AmbientSpace) : IsOpen (negativeHalfspace ν) :=
  isOpen_lt (continuous_const.inner continuous_id) continuous_const

lemma measurableSet_halfspacePlane (ν : AmbientSpace) :
    MeasurableSet {x : AmbientSpace | inner ℝ ν x = 0} :=
  (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet

/-- The horizontal inclusion preserves Euclidean distance. -/
lemma isometry_graphBaseN (n : ℕ) : Isometry (graphBaseN n) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := norm_graphTangentN_sq (0 : EuclideanSpace ℝ (Fin n)) (x - y)
  simpa [graphTangentN] using h

/-- Height in a frame whose final axis is `ν` is its final coordinate. -/
lemma inner_frame_eq_last {n : ℕ}
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {ν : EuclideanSpace ℝ (Fin (n + 1))}
    (he : e (EuclideanSpace.single (Fin.last n) 1) = ν)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : inner ℝ ν (e x) = x (Fin.last n) := by
  rw [← he, e.inner_map_map]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The plane measure is the pushforward of ordinary planar volume by any orthogonal frame. -/
lemma halfspacePlaneMeasure_eq_map {ν : AmbientSpace}
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (he : e (EuclideanSpace.single (Fin.last 2) 1) = ν) :
    halfspacePlaneMeasure ν = Measure.map (e ∘ graphBaseN 2) volume := by
  have hiso : Isometry (e ∘ graphBaseN 2) := e.isometry.comp (isometry_graphBaseN 2)
  apply Measure.ext
  intro A hA
  rw [halfspacePlaneMeasure, Measure.restrict_apply hA,
    Measure.map_apply hiso.continuous.measurable hA]
  have hset : A ∩ {x | inner ℝ ν x = 0} =
      (e ∘ graphBaseN 2) '' ((e ∘ graphBaseN 2) ⁻¹' A) := by
    apply Subset.antisymm
    · intro x hx
      have hlast : e.symm x (Fin.last 2) = 0 := by
        rw [← inner_frame_eq_last e he, e.apply_symm_apply]
        exact hx.2
      have hbase : graphBaseN 2 (graphProjectionN 2 (e.symm x)) = e.symm x := by
        have h := graphAppendN_projection (e.symm x)
        simpa only [hlast, graphAppendN, zero_smul, add_zero] using h
      refine ⟨graphProjectionN 2 (e.symm x), ?_, ?_⟩
      · change e (graphBaseN 2 (graphProjectionN 2 (e.symm x))) ∈ A
        simpa only [hbase, e.apply_symm_apply] using hx.1
      · simp only [comp_apply, hbase, e.apply_symm_apply]
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨hp, ?_⟩
      change inner ℝ ν (e (graphBaseN 2 p)) = 0
      rw [inner_frame_eq_last e he, graphBaseN_last]
  rw [hset]
  exact (hiso.euclideanHausdorffMeasure_image _).trans
    (congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) =>
      μ ((e ∘ graphBaseN 2) ⁻¹' A)) hausdorffMeasure2_plane)

/-- Scalar differentiation under the isometric identification of the line with `ℝ`. -/
lemma deriv_euclideanOneReal_scalar {ψ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (t : ℝ) :
    deriv (ψ ∘ euclideanOneReal.symm) t = gradient ψ (euclideanOneReal.symm t) 0 := by
  have hd := (hψ.differentiable one_ne_zero _).hasFDerivAt.comp t
    euclideanOneReal.symm.toContinuousLinearEquiv.hasFDerivAt
  have h := hd.hasDerivAt.deriv
  rw [gradient_apply_eq_fderiv_single]
  have hone : euclideanOneReal.symm 1 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i
    rfl
  change deriv (ψ ∘ euclideanOneReal.symm) t =
    fderiv ℝ ψ (euclideanOneReal.symm t) (euclideanOneReal.symm 1) at h
  rwa [hone] at h

/-- The negative half-line indicator pairs with a compact C¹ derivative by evaluation at zero. -/
lemma integral_negative_line_gradient {ψ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ t : EuclideanSpace ℝ (Fin 1),
      {s : EuclideanSpace ℝ (Fin 1) | s 0 < 0}.indicator (fun _ => (1 : ℝ)) t *
        gradient ψ t 0) = ψ 0 := by
  let F := ψ ∘ euclideanOneReal.symm
  have hF : ContDiff ℝ 1 F := hψ.comp euclideanOneReal.symm.toContinuousLinearEquiv.contDiff
  have hcF : HasCompactSupport F := hcψ.comp_homeomorph euclideanOneReal.symm.toHomeomorph
  rw [← euclideanOneReal.symm.measurePreserving.integral_comp
    euclideanOneReal.symm.toHomeomorph.measurableEmbedding]
  have heq (t : ℝ) :
      {s : EuclideanSpace ℝ (Fin 1) | s 0 < 0}.indicator (fun _ => (1 : ℝ))
        (euclideanOneReal.symm t) * gradient ψ (euclideanOneReal.symm t) 0 =
        (Iio (0 : ℝ)).indicator (deriv F) t := by
    have hm : euclideanOneReal.symm t ∈ {s : EuclideanSpace ℝ (Fin 1) | s 0 < 0} ↔ t < 0 := by
      change euclideanOneReal.symm t 0 < 0 ↔ t < 0
      rw [euclideanOneReal_symm_apply]
    by_cases ht : t < 0
    · rw [indicator_of_mem (hm.mpr ht), one_mul, indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht)]
      exact (deriv_euclideanOneReal_scalar hψ t).symm
    · rw [indicator_of_notMem (mt hm.mp ht), zero_mul,
        indicator_of_notMem (show t ∉ Iio (0 : ℝ) from ht)]
  simp_rw [heq]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    HasCompactSupport.integral_Iic_deriv_eq hF hcF]
  simp [F]

/-- A compact C¹ derivative integrates to zero along the entire line. -/
lemma integral_line_gradient_eq_zero {ψ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ t : EuclideanSpace ℝ (Fin 1), gradient ψ t 0) = 0 := by
  let F := ψ ∘ euclideanOneReal.symm
  have hF : ContDiff ℝ 1 F := hψ.comp euclideanOneReal.symm.toContinuousLinearEquiv.contDiff
  have hcF : HasCompactSupport F := hcψ.comp_homeomorph euclideanOneReal.symm.toHomeomorph
  have hi : Integrable (deriv F) :=
    hF.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hcF.deriv
  rw [← euclideanOneReal.symm.measurePreserving.integral_comp
    euclideanOneReal.symm.toHomeomorph.measurableEmbedding]
  simp_rw [← deriv_euclideanOneReal_scalar hψ]
  change (∫ t : ℝ, deriv F t) = 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic,
    HasCompactSupport.integral_Iic_deriv_eq hF hcF 0,
    HasCompactSupport.integral_Ioi_deriv_eq hF hcF 0, add_neg_cancel]

/-- The normal compact-test pairing is minus the planar boundary integral. -/
lemma negativeHalfspace_normal_pairing {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    -(∫ x, (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x ν) =
      -(∫ x, φ x ∂halfspacePlaneMeasure ν) := by
  obtain ⟨e, he⟩ := exists_line_direction_frame hν
  have hf := locallyIntegrable_indicator_one
    (isOpen_negativeHalfspace ν).measurableSet.nullMeasurableSet
  have hp := frame_pairing_eq_integral_lineDerivativePairing hf hφ hcφ e
  rw [he] at hp
  rw [hp]
  have hψ : ContDiff ℝ 1 (φ ∘ e) := hφ.comp e.toContinuousLinearEquiv.contDiff
  have hcψ : HasCompactSupport (φ ∘ e) := hcφ.comp_homeomorph e.toHomeomorph
  have hline (x : EuclideanSpace ℝ (Fin 2)) :
      lineSlice ((negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) ∘ e) x =
        {t : EuclideanSpace ℝ (Fin 1) | t 0 < 0}.indicator (fun _ => (1 : ℝ)) := by
    funext t
    have hm : e (graphAppendN x (t 0)) ∈ negativeHalfspace ν ↔ t 0 < 0 := by
      change inner ℝ ν (e (graphAppendN x (t 0))) < 0 ↔ t 0 < 0
      rw [inner_frame_eq_last e he, graphAppendN_last]
    change (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) (e (graphAppendN x (t 0))) = _
    by_cases ht : t 0 < 0
    · rw [indicator_of_mem (hm.mpr ht),
        indicator_of_mem (show t ∈ {s : EuclideanSpace ℝ (Fin 1) | s 0 < 0} from ht)]
    · rw [indicator_of_notMem (mt hm.mp ht),
        indicator_of_notMem (show t ∉ {s : EuclideanSpace ℝ (Fin 1) | s 0 < 0} from ht)]
  have hl (x : EuclideanSpace ℝ (Fin 2)) :
      lineDerivativePairing ((negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) ∘ e)
        (φ ∘ e) x = -φ (e (graphBaseN 2 x)) := by
    rw [lineDerivativePairing, hline,
      integral_negative_line_gradient (contDiff_lineSlice hψ x) (hasCompactSupport_lineSlice hcψ x)]
    simp only [lineSlice, comp_apply, PiLp.zero_apply, graphAppendN, zero_smul, add_zero]
  simp_rw [hl]
  rw [integral_neg, halfspacePlaneMeasure_eq_map e he,
    (e.isometry.comp (isometry_graphBaseN 2)).isClosedEmbedding.measurableEmbedding.integral_map]
  rfl

/-- A tangential unit direction pairs to zero, because the sliced indicator is constant. -/
lemma negativeHalfspace_tangent_unit_pairing {ν v : AmbientSpace}
    (hv : ‖v‖ = 1) (hperp : inner ℝ ν v = 0)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    -(∫ x, (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) = 0 := by
  obtain ⟨e, he⟩ := exists_line_direction_frame hv
  have hf := locallyIntegrable_indicator_one
    (isOpen_negativeHalfspace ν).measurableSet.nullMeasurableSet
  have hp := frame_pairing_eq_integral_lineDerivativePairing hf hφ hcφ e
  rw [he] at hp
  rw [hp]
  have hψ : ContDiff ℝ 1 (φ ∘ e) := hφ.comp e.toContinuousLinearEquiv.contDiff
  have hcψ : HasCompactSupport (φ ∘ e) := hcφ.comp_homeomorph e.toHomeomorph
  have hline (x : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 1)) :
      lineSlice ((negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) ∘ e) x t =
        (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) (e (graphBaseN 2 x)) := by
    have hi : inner ℝ ν (e (graphAppendN x (t 0))) = inner ℝ ν (e (graphBaseN 2 x)) := by
      simp only [graphAppendN, map_add, map_smul, inner_add_right, inner_smul_right,
        he, hperp, mul_zero, add_zero]
    have hm : e (graphAppendN x (t 0)) ∈ negativeHalfspace ν ↔
        e (graphBaseN 2 x) ∈ negativeHalfspace ν := by
      change inner ℝ ν (e (graphAppendN x (t 0))) < 0 ↔
        inner ℝ ν (e (graphBaseN 2 x)) < 0
      rw [hi]
    change (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) (e (graphAppendN x (t 0))) = _
    by_cases ht : e (graphBaseN 2 x) ∈ negativeHalfspace ν
    · rw [indicator_of_mem (hm.mpr ht), indicator_of_mem ht]
    · rw [indicator_of_notMem (mt hm.mp ht), indicator_of_notMem ht]
  have hl (x : EuclideanSpace ℝ (Fin 2)) :
      lineDerivativePairing ((negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) ∘ e)
        (φ ∘ e) x = 0 := by
    simp_rw [lineDerivativePairing, hline]
    rw [integral_const_mul,
      integral_line_gradient_eq_zero (contDiff_lineSlice hψ x) (hasCompactSupport_lineSlice hcψ x),
      mul_zero, neg_zero]
  simp_rw [hl]
  exact integral_zero _ _

/-- Every tangential direction has zero distributional pairing, including the zero vector. -/
lemma negativeHalfspace_tangent_pairing {ν v : AmbientSpace} (hperp : inner ℝ ν v = 0)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    -(∫ x, (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  let w := ‖v‖⁻¹ • v
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, norm_inv, hnv]
  have hwp : inner ℝ ν w = 0 := by simp only [w, inner_smul_right, hperp, mul_zero]
  have hvw : v = ‖v‖ • w := by simp [w, smul_smul, hnv]
  have hz := negativeHalfspace_tangent_unit_pairing hw hwp hφ hcφ
  calc
    -(∫ x, (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) =
        ‖v‖ * (-(∫ x, (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x w)) := by
      rw [← integral_neg, ← integral_neg, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        conv_lhs => rw [hvw, map_smul, smul_eq_mul]
        ring
    _ = 0 := by rw [hz, mul_zero]

/-- The complete directional test identity for a unit-normal halfspace. -/
theorem negativeHalfspace_directional_pairing {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : AmbientSpace) :
    -(∫ x, (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) =
      -(inner ℝ ν v) * (∫ x, φ x ∂halfspacePlaneMeasure ν) := by
  let a := inner ℝ ν v
  let w := v - a • ν
  have hp : inner ℝ ν w = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hν,
      one_pow, mul_one, a, sub_self]
  have hv : v = a • ν + w := by dsimp [w]; abel
  have hi (z : AmbientSpace) : Integrable (fun x =>
      (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x z) := by
    have hd : Continuous (fun x => fderiv ℝ φ x z) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hi : Integrable (fun x => fderiv ℝ φ x z) volume :=
      hd.integrable_of_hasCompactSupport (hcφ.fderiv_apply ℝ z)
    have hind : (fun x => (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x z) = (negativeHalfspace ν).indicator (fun x => fderiv ℝ φ x z) := by
      funext x
      by_cases hx : x ∈ negativeHalfspace ν <;> simp [hx]
    rw [hind]
    exact hi.indicator (isOpen_negativeHalfspace ν).measurableSet
  have heq : (fun x => (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x v) =
      (fun x => a * ((negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x ν) +
        (negativeHalfspace ν).indicator (fun _ => (1 : ℝ)) x * fderiv ℝ φ x w) := by
    funext x
    rw [hv, map_add, map_smul, smul_eq_mul]
    ring
  rw [heq, integral_add ((hi ν).const_mul a) (hi w), integral_const_mul]
  have hn := negativeHalfspace_normal_pairing hν hφ hcφ
  have ht := negativeHalfspace_tangent_pairing hp hφ hcφ
  rw [neg_inj] at hn
  rw [neg_eq_zero] at ht
  rw [hn, ht, add_zero]
  ring

/-- Exact outward normal and positive boundary-area measure for the halfspace indicator. -/
theorem negativeHalfspace_hasConstantIndicatorPolar {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    HasConstantIndicatorPolar (negativeHalfspace ν) (halfspacePlaneMeasure ν) ν := by
  intro i φ hφ
  rw [negativeHalfspace_directional_pairing hν hφ φ.hasCompactSupport,
    EuclideanSpace.inner_single_right, integral_mul_const]
  simp only [starRingEnd_apply, star_trivial]
  ring

end LiquidDrop
