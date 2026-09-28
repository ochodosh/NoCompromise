import NoCompromise.Elliptic.ClassicalCubeW11
import NoCompromise.Sobolev.W11Classical

/-!
# Translated and rotated cubes

Affine isometries transport the classical cube faces, their outward normals,
and the elementary divergence identity. Smooth density then gives Gauss–Green
on every placed cube for the genuine bounded W¹,¹ trace.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- An arbitrary translated and rotated cube of side length `2 * R`. -/
def placedCoordinateCube (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (R : ℝ) :
    Set AmbientSpace :=
  a '' coordinateCube 3 R

/-- The transported classical face normal; edges still receive the value zero. -/
def placedCubeOutwardNormal (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (R : ℝ)
    (x : AmbientSpace) : AmbientSpace :=
  a.linearIsometryEquiv (cubeOutwardNormal R (a.symm x))

lemma isOpen_placedCoordinateCube (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (R : ℝ) :
    IsOpen (placedCoordinateCube a R) :=
  a.toHomeomorph.isOpenMap _ (isOpen_coordinateCube 3 R)

lemma isBounded_placedCoordinateCube (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (R : ℝ) :
    Bornology.IsBounded (placedCoordinateCube a R) :=
  a.isometry.lipschitzWith.isBounded_image (isBounded_coordinateCube 3 R)

lemma hasLipschitzBoundary_placedCoordinateCube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R) :
    HasLipschitzBoundary (placedCoordinateCube a R) := by
  intro x hx
  have hf : frontier (placedCoordinateCube a R) = a '' frontier (coordinateCube 3 R) :=
    (a.toHomeomorph.image_frontier _).symm
  rw [hf] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc, hyc⟩ := hasLipschitzBoundary_coordinateCube 3 hR y hy
  let d : LipschitzGraphChart 3 := { c with placement := c.placement.trans a }
  have hd (z : AmbientSpace) : d.homeomorph z = a (c.homeomorph z) := rfl
  have hdreg : d.region = a '' c.region := by
    change d.homeomorph '' coordinateCube 3 c.radius = _
    simp only [LipschitzGraphChart.region, image_image, hd]
  have hdup : d.upperRegion = a '' c.upperRegion := by
    change d.homeomorph '' coordinateHalfCube c.normal c.radius = _
    simp only [LipschitzGraphChart.upperRegion, image_image, hd]
  refine ⟨d, ?_, ?_⟩
  · change d.upperRegion = placedCoordinateCube a R ∩ d.region
    rw [hdup, hc, image_inter a.injective, hdreg]
    rfl
  · rw [hdreg]
    exact mem_image_of_mem a hyc

lemma map_cube_boundaryMeasure_affine
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (R : ℝ) :
    Measure.map a ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))) =
      (hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
  have hm : Measure.map a (hausdorffMeasure2 3) = hausdorffMeasure2 3 := by
    ext S hS
    rw [Measure.map_apply a.continuous.measurable hS]
    have h := a.isometry.euclideanHausdorffMeasure_image (a ⁻¹' S) (d := 2)
    rw [image_preimage_eq S a.surjective] at h
    exact h.symm
  have hfront : a '' frontier (coordinateCube 3 R) =
      frontier (placedCoordinateCube a R) := a.toHomeomorph.image_frontier _
  have hf : a ⁻¹' frontier (placedCoordinateCube a R) = frontier (coordinateCube 3 R) := by
    rw [← hfront, preimage_image_eq _ a.injective]
  have hme : MeasurableEmbedding (a : AmbientSpace → AmbientSpace) :=
    a.toHomeomorph.measurableEmbedding
  rw [← hf, ← hme.restrict_map, hm]

lemma measurable_placedCubeOutwardNormal (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (R : ℝ) :
    Measurable (placedCubeOutwardNormal a R) :=
  a.linearIsometryEquiv.continuous.measurable.comp
    ((measurable_cubeOutwardNormal R).comp a.symm.continuous.measurable)

lemma norm_placedCubeOutwardNormal_le_one (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace)
    {R : ℝ} (hR : 0 < R) (x : AmbientSpace) : ‖placedCubeOutwardNormal a R x‖ ≤ 1 := by
  rw [placedCubeOutwardNormal, a.linearIsometryEquiv.norm_map]
  exact norm_cubeOutwardNormal_le_one hR _

lemma norm_placedCubeOutwardNormal_ae (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)),
      ‖placedCubeOutwardNormal a R x‖ = 1 := by
  have hme : MeasurableEmbedding (a : AmbientSpace → AmbientSpace) :=
    a.toHomeomorph.measurableEmbedding
  rw [← map_cube_boundaryMeasure_affine, hme.ae_map_iff]
  simpa only [placedCubeOutwardNormal, a.symm_apply_apply, a.linearIsometryEquiv.norm_map]
    using norm_cubeOutwardNormal_ae hR

lemma hausdorffMeasure2_frontier_placedCoordinateCube_lt_top
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R) :
    hausdorffMeasure2 3 (frontier (placedCoordinateCube a R)) < ∞ := by
  have hfront : a '' frontier (coordinateCube 3 R) =
      frontier (placedCoordinateCube a R) := a.toHomeomorph.image_frontier _
  rw [← hfront]
  exact (a.isometry.euclideanHausdorffMeasure_image _).trans_lt
    (hausdorffMeasure2_frontier_coordinateCube_lt_top hR)

theorem classical_directional_gauss_green_placedCube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (v : AmbientSpace) :
    (∫ x in placedCoordinateCube a R, fderiv ℝ φ x v) =
      ∫ x, φ x * inner ℝ v (placedCubeOutwardNormal a R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
  let L := a.linearIsometryEquiv
  have hder (z : AmbientSpace) : fderiv ℝ (φ ∘ a) z (L.symm v) =
      fderiv ℝ φ (a z) v := by
    have hd := (hφ.differentiable one_ne_zero (a z)).hasFDerivAt.comp z
      (hasFDerivAt_rigidPlacement a z)
    have hh := congrArg (fun M => M (L.symm v)) hd.fderiv
    change fderiv ℝ (φ ∘ a) z (L.symm v) = fderiv ℝ φ (a z) (L (L.symm v)) at hh
    simpa only [L.apply_symm_apply] using hh
  have hinner (w : AmbientSpace) : inner ℝ (L.symm v) w = inner ℝ v (L w) := by
    simpa only [L.apply_symm_apply] using (L.inner_map_map (L.symm v) w).symm
  have h := classical_directional_gauss_green_cube hR
    (hφ.comp (contDiff_rigidPlacement a)) (L.symm v)
  simp only [hder, Function.comp_apply, hinner] at h
  have hb := (measurePreserving_affineIsometry a).setIntegral_preimage_emb
    a.toHomeomorph.measurableEmbedding (fun x => fderiv ℝ φ x v) (placedCoordinateCube a R)
  have hp : a ⁻¹' placedCoordinateCube a R = coordinateCube 3 R :=
    preimage_image_eq _ a.injective
  rw [hp] at hb
  have hme : MeasurableEmbedding (a : AmbientSpace → AmbientSpace) :=
    a.toHomeomorph.measurableEmbedding
  rw [← hb, h, ← map_cube_boundaryMeasure_affine, hme.integral_map]
  simp only [placedCubeOutwardNormal, a.symm_apply_apply]
  rfl

theorem w11_directional_gauss_green_placedCube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R)
    (T : W11Space (placedCoordinateCube a R) →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))))
    (hT : ∀ f G (hf : HasW11GradientOn f G (placedCoordinateCube a R)), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf))
        =ᵐ[(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))] f)
    (u : W11Space (placedCoordinateCube a R)) (v : AmbientSpace) :
    (∫ x in placedCoordinateCube a R, inner ℝ (u.gradientLp x) v) =
      ∫ x, T u x * inner ℝ v (placedCubeOutwardNormal a R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
  have hνm := (measurable_placedCubeOutwardNormal a R).aestronglyMeasurable
    (μ := (hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)))
  have hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)),
      ‖placedCubeOutwardNormal a R x‖ ≤ 1 :=
    Eventually.of_forall (norm_placedCubeOutwardNormal_le_one a hR)
  let L : W11Space (placedCoordinateCube a R) →L[ℝ] ℝ :=
    (lpOneInnerPairing (V := fun _ : AmbientSpace => v) aestronglyMeasurable_const
      (Eventually.of_forall fun _ => le_refl ‖v‖)).comp W11Space.gradientCLM
  have hnv : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)),
      ‖inner ℝ v (placedCubeOutwardNormal a R x)‖ ≤ ‖v‖ := by
    filter_upwards [hn] with x hx
    exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg v])
  let B : W11Space (placedCoordinateCube a R) →L[ℝ] ℝ :=
    (lpOneInnerPairing (hνm.const_inner (c := v)) hnv).comp T
  have hL (w : W11Space (placedCoordinateCube a R)) :
      L w = ∫ x in placedCoordinateCube a R, inner ℝ (w.gradientLp x) v := rfl
  have hB (w : W11Space (placedCoordinateCube a R)) : B w =
      ∫ x, T w x * inner ℝ v (placedCubeOutwardNormal a R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
    simp only [B, ContinuousLinearMap.comp_apply, lpOneInnerPairing_apply,
      RCLike.inner_apply, conj_trivial, mul_comm]
  obtain ⟨φ, hφ, hcφ, hconv⟩ := W11Space.exists_smooth_approx_on_domain
    (isOpen_placedCoordinateCube a R) (isBounded_placedCoordinateCube a R)
    (hasLipschitzBoundary_placedCoordinateCube a hR) u
  let q (j : ℕ) := W11Space.ofFunction (φ j) (gradient (φ j)) (hφ j)
  have heq (j : ℕ) : L (q j) = B (q j) := by
    rw [hL, hB]
    calc
      _ = ∫ x in placedCoordinateCube a R, fderiv ℝ (φ j) x v := by
        apply integral_congr_ae
        filter_upwards [W11Space.gradientLp_ofFunction (φ j) (gradient (φ j)) (hφ j)]
          with x hx
        rw [hx, inner_gradient_left]
      _ = ∫ x, φ j x * inner ℝ v (placedCubeOutwardNormal a R x)
          ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) :=
        classical_directional_gauss_green_placedCube a hR
          ((hcφ j).of_le (by simp)) v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hT (φ j) (gradient (φ j)) (hφ j) (hcφ j).continuous] with x hx
        rw [hx]
  have htL : Tendsto (fun j => L (q j)) atTop (𝓝 (L u)) :=
    (L.continuous.tendsto u).comp hconv
  have htR : Tendsto (fun j => L (q j)) atTop (𝓝 (B u)) := by
    simpa only [heq, q, Function.comp_def] using (B.continuous.tendsto u).comp hconv
  simpa only [hL, hB] using tendsto_nhds_unique htL htR

theorem w11_gauss_green_placedCube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R)
    (T : W11Space (placedCoordinateCube a R) →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))))
    (hT : ∀ f G (hf : HasW11GradientOn f G (placedCoordinateCube a R)), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf))
        =ᵐ[(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))] f)
    {Z : AmbientSpace → AmbientSpace} {J : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace}
    (hZ : HasW11VectorGradientOn Z J (placedCoordinateCube a R)) :
    (∫ x in placedCoordinateCube a R, w11Divergence J x) =
      ∫ x, inner ℝ (w11VectorTrace T hZ x) (placedCubeOutwardNormal a R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
  have hνm := (measurable_placedCubeOutwardNormal a R).aestronglyMeasurable
    (μ := (hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)))
  have hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)),
      ‖placedCubeOutwardNormal a R x‖ ≤ 1 :=
    Eventually.of_forall (norm_placedCubeOutwardNormal_le_one a hR)
  classical
  let e (i : Fin 3) : AmbientSpace := EuclideanSpace.single i 1
  let u (i : Fin 3) := W11Space.ofFunction _ _ (hZ.component i)
  have hj (i : Fin 3) : IntegrableOn (fun x => J x (e i) i) (placedCoordinateCube a R) := by
    have h := ((hZ.component i).integrable_gradient.inner_const (𝕜 := ℝ) (e i))
    simpa only [IntegrableOn, e, ContinuousLinearMap.adjoint_inner_left,
      EuclideanSpace.inner_single_left, map_one, one_mul] using h
  have ht (i : Fin 3) : Integrable (fun x => T (u i) x * placedCubeOutwardNormal a R x i)
      ((hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))) := by
    have hi := memLp_one_iff_integrable.mp (Lp.memLp (T (u i)))
    have hb : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)),
        ‖placedCubeOutwardNormal a R x i‖ ≤ 1 :=
      hn.mono fun x hx => (PiLp.norm_apply_le (placedCubeOutwardNormal a R x) i).trans hx
    have hm : AEStronglyMeasurable (fun x => placedCubeOutwardNormal a R x i)
        ((hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))) := by
      exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hνm
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      integrable_inner_of_ae_bound hi hm hb
  have heq (i : Fin 3) : (∫ x in placedCoordinateCube a R, J x (e i) i) =
      ∫ x, T (u i) x * placedCubeOutwardNormal a R x i
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
    have h := w11_directional_gauss_green_placedCube a hR T hT (u i) (e i)
    have he : (∫ x in placedCoordinateCube a R, inner ℝ ((u i).gradientLp x) (e i)) =
        ∫ x in placedCoordinateCube a R, J x (e i) i := by
      apply integral_congr_ae
      filter_upwards [W11Space.gradientLp_ofFunction _ _ (hZ.component i)] with x hx
      rw [hx, ContinuousLinearMap.adjoint_inner_left]
      simp only [e, EuclideanSpace.inner_single_left, map_one, one_mul]
    simpa only [he, e, EuclideanSpace.inner_single_left, map_one, one_mul] using h
  calc
    _ = ∑ i : Fin 3, ∫ x in placedCoordinateCube a R, J x (e i) i :=
      integral_finsetSum _ fun i _ => hj i
    _ = ∑ i : Fin 3, ∫ x, T (u i) x * placedCubeOutwardNormal a R x i
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) :=
      Finset.sum_congr rfl fun i _ => heq i
    _ = ∫ x, ∑ i : Fin 3, T (u i) x * placedCubeOutwardNormal a R x i
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) :=
      (integral_finsetSum _ fun i _ => ht i).symm
    _ = _ := by
      congr 1
      funext x
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
        w11VectorTrace, u, mul_comm]

/-- The trace operator is constructed once, before the vector field is specified. -/
theorem exists_w11_gauss_green_placedCube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R) :
    ∃ T : W11Space (placedCoordinateCube a R) →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))),
    ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧
      (∀ f G (hf : HasW11GradientOn f G (placedCoordinateCube a R)), Continuous f →
        ⇑(T (W11Space.ofFunction f G hf))
          =ᵐ[(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))] f) ∧
      ∀ Z J (hZ : HasW11VectorGradientOn Z J (placedCoordinateCube a R)),
        (∫ x in placedCoordinateCube a R, w11Divergence J x) =
          ∫ x, inner ℝ (w11VectorTrace T hZ x) (placedCubeOutwardNormal a R x)
            ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
  obtain ⟨T, C, hC, hTC, hT⟩ := exists_w11_trace_operator
    (isOpen_placedCoordinateCube a R) (isBounded_placedCoordinateCube a R)
    (hasLipschitzBoundary_placedCoordinateCube a hR)
  exact ⟨T, C, hC, hTC, hT, fun _ _ hZ => w11_gauss_green_placedCube a hR T hT hZ⟩

theorem classical_gauss_green_placedCube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R)
    {Z : AmbientSpace → AmbientSpace} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in placedCoordinateCube a R, divergenceN Z x) =
      ∫ x, inner ℝ (Z x) (placedCubeOutwardNormal a R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) := by
  obtain ⟨T, _, _, _, hT, hGG⟩ := exists_w11_gauss_green_placedCube a hR
  let hW := hasW11VectorGradientOn_of_contDiff (isOpen_placedCoordinateCube a R)
    (isBounded_placedCoordinateCube a R) hZ
  have ht : w11VectorTrace T hW
      =ᵐ[(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))] Z := by
    have hi (i : Fin 3) := hT (fun x => Z x i)
      (fun x => (fderiv ℝ Z x).adjoint (EuclideanSpace.single i 1)) (hW.component i)
      ((EuclideanSpace.proj i).continuous.comp hZ.continuous)
    filter_upwards [ae_all_iff.mpr hi] with x hx
    exact PiLp.ext fun i => hx i
  calc
    _ = ∫ x, inner ℝ (w11VectorTrace T hW x) (placedCubeOutwardNormal a R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R)) :=
      hGG Z (fderiv ℝ Z) hW
    _ = _ := integral_congr_ae (ht.mono fun x hx =>
      congrArg (fun z => inner ℝ z (placedCubeOutwardNormal a R x)) hx)

/-- The elementary position-field flux, valid for every translated or rotated cube. -/
theorem integral_position_placedCube_normal_eq_three_volume
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R) :
    (∫ x, inner ℝ x (placedCubeOutwardNormal a R x)
      ∂(hausdorffMeasure2 3).restrict (frontier (placedCoordinateCube a R))) =
        3 * volume.real (placedCoordinateCube a R) := by
  have h := classical_gauss_green_placedCube a hR (Z := id) contDiff_id
  simp only [id_eq] at h
  rw [← h]
  have hd (x : AmbientSpace) : divergenceN id x = 3 := by
    simp [divergenceN, fderiv_id]
  simp only [hd, setIntegral_const, smul_eq_mul, mul_comm]

end LiquidDrop
