module

public import NoCompromise.BV.Slicing
public import NoCompromise.Area.Sphere

@[expose] public section

/-!
# Spherical slicing and weighted radial disintegration

The explicit radial-longitude-colatitude map has determinant `-r² sin φ`, is
injective away from the angular seam and poles, and has conull image. Ordinary
three-dimensional change of variables and Fubini give radial integration in
parameters. The already-proved planar area formula identifies the corresponding
surface measure, first for Borel sections and then for arbitrary weights.

The resulting spherical slicing identity uses the density-one representative on
spheres and the original Lebesgue-measurable set in the annulus. It assumes only
`0 ≤ a`; no finite-perimeter or finite-volume hypothesis is used. The weighted
endpoints include nonnegative Borel functions with infinite values and integrable
Banach-valued strongly measurable functions. No packaged lower-dimensional
coarea theorem or perimeter formula enters the proof.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxRecDepth 3000

/-- The angular projection in radial-longitude-colatitude coordinates. -/
def sphericalAngles : AmbientSpace →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 0 1) +
    (EuclideanSpace.proj 2).smulRight (EuclideanSpace.single 1 1)

@[simp] lemma sphericalAngles_zero (x : AmbientSpace) : sphericalAngles x 0 = x 1 := by
  simp [sphericalAngles]
@[simp] lemma sphericalAngles_one (x : AmbientSpace) : sphericalAngles x 1 = x 2 := by
  simp [sphericalAngles]

lemma sphericalAngles_eq_slicingCoordinates (x : AmbientSpace) :
    sphericalAngles x = (slicingCoordinates x).2 := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change sphericalAngles x 0 = x 1
    exact sphericalAngles_zero x
  · change sphericalAngles x 1 = x 2
    exact sphericalAngles_one x

/-- The usual three-dimensional spherical coordinate map. -/
def sphericalMap (x : AmbientSpace) : AmbientSpace := x 0 • sphereParam (sphericalAngles x)

/-- Its explicitly differentiated continuous linear map. -/
def sphericalMapDeriv (x : AmbientSpace) : AmbientSpace →L[ℝ] AmbientSpace :=
  (EuclideanSpace.proj 0).smulRight (sphereParam (sphericalAngles x)) +
    x 0 • (sphereParamDeriv (sphericalAngles x)).comp sphericalAngles

lemma hasFDerivAt_sphericalMap (x : AmbientSpace) :
    HasFDerivAt sphericalMap (sphericalMapDeriv x) x := by
  convert! (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt.smul
    ((hasFDerivAt_sphereParam _).comp x sphericalAngles.hasFDerivAt) using 1
  exact add_comm _ _

lemma det_sphericalMapDeriv (x : AmbientSpace) :
    (sphericalMapDeriv x).det = -(x 0)^2 * Real.sin (x 2) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hentry (i j : Fin 3) :
      LinearMap.toMatrix b.toBasis b.toBasis (sphericalMapDeriv x).toLinearMap i j =
        sphericalMapDeriv x (EuclideanSpace.single j 1) i := by
    rw [LinearMap.toMatrix_apply]
    simp [b, OrthonormalBasis.coe_toBasis_repr_apply]
  change LinearMap.det (sphericalMapDeriv x).toLinearMap = _
  rw [← LinearMap.det_toMatrix b.toBasis, Matrix.det_fin_three]
  simp only [hentry]
  calc
    _ = -(x 0)^2 * Real.sin (x 2) *
        ((Real.sin (x 1)^2 + Real.cos (x 1)^2) *
          (Real.sin (x 2)^2 + Real.cos (x 2)^2)) := by
      simp [sphericalMapDeriv, sphereParamDeriv, sphereParam, sphericalAngles,
        -Real.sin_sq_add_cos_sq, -Real.cos_sq_add_sin_sq]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

/-- Positive radii, longitude away from the seam, and colatitude away from the poles. -/
def sphericalDomain : Set AmbientSpace :=
  {x | 0 < x 0 ∧ sphericalAngles x ∈ sphereParamDomain}

lemma measurableSet_sphericalDomain : MeasurableSet sphericalDomain :=
  (measurableSet_Ioi.preimage (EuclideanSpace.proj 0).continuous.measurable).inter
    (measurableSet_sphereParamDomain.preimage sphericalAngles.continuous.measurable)

lemma sphericalMap_injOn : InjOn sphericalMap sphericalDomain := by
  intro x hx y hy heq
  have hr : x 0 = y 0 := by
    have hn := congrArg norm heq
    simpa only [sphericalMap, norm_smul, norm_sphereParam, mul_one, Real.norm_eq_abs,
      abs_of_pos hx.1, abs_of_pos hy.1] using hn
  have ha : sphericalAngles x = sphericalAngles y := by
    apply sphereParam_injOn hx.2 hy.2
    have heq' : x 0 • sphereParam (sphericalAngles x) =
        x 0 • sphereParam (sphericalAngles y) := by simpa only [sphericalMap, ← hr] using heq
    exact (smul_right_injective _ hx.1.ne') heq'
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hr
  · simpa using congrArg (fun p => p 0) ha
  · simpa using congrArg (fun p => p 1) ha

@[simp] lemma sphericalAngles_coordinatePlaneParam (r : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    sphericalAngles (coordinatePlaneParam r p) = p := by
  rw [sphericalAngles_eq_slicingCoordinates]
  exact congrArg Prod.snd (slicingCoordinates.apply_symm_apply (r, p))

lemma mem_image_sphericalMap_of_coordinate_ne {y : AmbientSpace} (hy : y 1 ≠ 0) :
    y ∈ sphericalMap '' sphericalDomain := by
  have hy0 : y ≠ 0 := by intro h; apply hy; simp [h]
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hu : ‖y‖⁻¹ • y ∈ sphere (0 : AmbientSpace) 1 := by
    simp [norm_smul, hr.ne']
  rw [← sphereParam_image_closedDomain] at hu
  obtain ⟨p, hp, he⟩ := hu
  have hpne : sphereParam p 1 ≠ 0 := by
    rw [he]
    change ‖y‖⁻¹ * y 1 ≠ 0
    exact mul_ne_zero (inv_ne_zero hr.ne') hy
  have hp0l : p 0 ≠ -Real.pi := by intro h; apply hpne; simp [h]
  have hp0r : p 0 ≠ Real.pi := by intro h; apply hpne; simp [h]
  have hp1l : p 1 ≠ 0 := by intro h; apply hpne; simp [h]
  have hp1r : p 1 ≠ Real.pi := by intro h; apply hpne; simp [h]
  have hpo : p ∈ sphereParamDomain :=
    ⟨⟨lt_of_le_of_ne hp.1.1 hp0l.symm, lt_of_le_of_ne hp.1.2 hp0r⟩,
      ⟨lt_of_le_of_ne hp.2.1 hp1l.symm, lt_of_le_of_ne hp.2.2 hp1r⟩⟩
  refine ⟨coordinatePlaneParam ‖y‖ p, ⟨by simpa using hr, by simpa using hpo⟩, ?_⟩
  simp [sphericalMap, he, smul_smul, hr.ne']

lemma sphericalMap_image_ae_eq_univ : sphericalMap '' sphericalDomain =ᵐ[volume] univ := by
  have hn : ∀ᵐ y : AmbientSpace ∂volume, y 1 ≠ 0 :=
    (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) 1 0)
  filter_upwards [hn] with y hy
  exact propext ⟨fun _ => mem_univ y, fun _ => mem_image_sphericalMap_of_coordinate_ne hy⟩

/-- The three-dimensional spherical-coordinate change of variables, derived
from the ordinary equidimensional change-of-variables theorem. -/
lemma lintegral_sphericalMap (g : AmbientSpace → ℝ≥0∞) :
    ∫⁻ y, g y = ∫⁻ x in sphericalDomain,
      ENNReal.ofReal ((x 0)^2 * Real.sin (x 2)) * g (sphericalMap x) := by
  calc
    _ = ∫⁻ y in sphericalMap '' sphericalDomain, g y := by
      rw [setLIntegral_congr sphericalMap_image_ae_eq_univ, setLIntegral_univ]
    _ = ∫⁻ x in sphericalDomain, ENNReal.ofReal |(sphericalMapDeriv x).det| *
        g (sphericalMap x) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_sphericalDomain
        (fun x _ => (hasFDerivAt_sphericalMap x).hasFDerivWithinAt) sphericalMap_injOn g
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_sphericalDomain
      intro x hx
      dsimp only
      have hsin : 0 < Real.sin (x 2) := by
        simpa only [sphericalAngles_one] using
          Real.sin_pos_of_pos_of_lt_pi hx.2.2.1 hx.2.2.2
      rw [det_sphericalMapDeriv, abs_mul, abs_neg, abs_pow, sq_abs, abs_of_pos hsin]

lemma hausdorffMeasure2_unit_sphere_section {A : Set AmbientSpace} (hA : MeasurableSet A) :
    hausdorffMeasure2 3 (A ∩ sphere (0 : AmbientSpace) 1) =
      ∫⁻ p in sphereParamDomain, ENNReal.ofReal |Real.sin (p 1)| *
        A.indicator (fun _ => (1 : ℝ≥0∞)) (sphereParam p) := by
  have hn : hausdorffMeasure2 3
      (sphereParam '' (sphereParamClosedDomain \ sphereParamDomain)) = 0 :=
    hausdorffMeasure2_image_null lipschitzWith_sphereParam
      (ae_le_set.mp sphereParamClosedDomain_ae_eq.le)
  have hsub : sphereParamDomain ⊆ sphereParamClosedDomain :=
    fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩
  have heq : sphereParamClosedDomain =
      sphereParamDomain ∪ (sphereParamClosedDomain \ sphereParamDomain) :=
    by rw [union_sdiff_self, union_eq_self_of_subset_left hsub]
  have hn' : hausdorffMeasure2 3
      (A ∩ sphereParam '' (sphereParamClosedDomain \ sphereParamDomain)) = 0 :=
    measure_mono_null inter_subset_right hn
  rw [← sphereParam_image_closedDomain, heq, image_union, inter_union_distrib_left,
    measure_congr (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hn'))]
  have him : A ∩ sphereParam '' sphereParamDomain =
      sphereParam '' ((sphereParam ⁻¹' A) ∩ sphereParamDomain) := by
    rw [image_preimage_inter]
  rw [him, hausdorffMeasure2_image_eq_lintegral_jacobian_of_lipschitz
    lipschitzWith_sphereParam
    ((hA.preimage lipschitzWith_sphereParam.continuous.measurable).inter
      measurableSet_sphereParamDomain) (sphereParam_injOn.mono inter_subset_right)]
  rw [← setLIntegral_indicator (hA.preimage lipschitzWith_sphereParam.continuous.measurable)]
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  by_cases hp : sphereParam p ∈ A <;> simp [hp, jacobian2_sphereParam]

open scoped Pointwise in
lemma hausdorffMeasure2_sphere_section_zero {A : Set AmbientSpace} (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 < r) :
    hausdorffMeasure2 3 (A ∩ sphere (0 : AmbientSpace) r) =
      ∫⁻ p in sphereParamDomain, ENNReal.ofReal (r ^ 2 * |Real.sin (p 1)|) *
        A.indicator (fun _ => (1 : ℝ≥0∞)) (r • sphereParam p) := by
  have hs : r • sphere (0 : AmbientSpace) 1 = sphere 0 r := by
    simpa only [smul_zero, Real.norm_of_nonneg hr.le, mul_one] using
      smul_sphere' hr.ne' (0 : AmbientSpace) 1
  have heq : A ∩ sphere (0 : AmbientSpace) r =
      r • (((fun x : AmbientSpace => r • x) ⁻¹' A) ∩ sphere 0 1) := by
    rw [← hs]
    exact (image_preimage_inter (fun x : AmbientSpace => r • x) (sphere 0 1) A).symm
  rw [heq]
  change Measure.euclideanHausdorffMeasure 2 (r • _) = _
  rw [Measure.euclideanHausdorffMeasure_smul₀ 2 hr.ne']
  change (‖r‖₊ ^ 2 : ℝ≥0∞) * hausdorffMeasure2 3
    (((fun x : AmbientSpace => r • x) ⁻¹' A) ∩ sphere 0 1) = _
  have hn : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal ‖r‖ = ENNReal.ofReal r
    rw [Real.norm_of_nonneg hr.le]
  rw [hn, ← ENNReal.ofReal_pow hr.le,
    hausdorffMeasure2_unit_sphere_section (hA.preimage (by fun_prop)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  dsimp only
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1

lemma continuous_sphericalMap : Continuous sphericalMap :=
  (EuclideanSpace.proj 0).continuous.smul
    (lipschitzWith_sphereParam.continuous.comp sphericalAngles.continuous)

/-- Spherical coordinates in iterated-integral form. -/
lemma lintegral_spherical_coordinates {g : AmbientSpace → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ p in sphereParamDomain,
      ENNReal.ofReal (r ^ 2 * Real.sin (p 1)) * g (r • sphereParam p) := by
  rw [lintegral_sphericalMap]
  have hset : slicingCoordinates.symm ⁻¹' sphericalDomain =
      Ioi (0 : ℝ) ×ˢ sphereParamDomain := by
    ext z
    rcases z with ⟨r, p⟩
    change (0 < coordinatePlaneParam r p 0 ∧
      sphericalAngles (coordinatePlaneParam r p) ∈ sphereParamDomain) ↔ _
    simp
  have h := measurePreserving_slicingCoordinates.symm.setLIntegral_comp_preimage_emb
    slicingCoordinates.symm.measurableEmbedding
    (fun x => ENNReal.ofReal ((x 0)^2 * Real.sin (x 2)) * g (sphericalMap x)) sphericalDomain
  rw [hset] at h
  rw [← h]
  change (∫⁻ z in Ioi (0 : ℝ) ×ˢ sphereParamDomain,
    ENNReal.ofReal ((slicingCoordinates.symm z 0)^2 * Real.sin (slicingCoordinates.symm z 2)) *
      g (sphericalMap (slicingCoordinates.symm z)) ∂volume.prod volume) = _
  rw [setLIntegral_prod _ (by
    apply Measurable.aemeasurable
    exact (by fun_prop : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((slicingCoordinates.symm z 0)^2 *
        Real.sin (slicingCoordinates.symm z 2)))) |>.mul
      (hg.comp (continuous_sphericalMap.measurable.comp slicingCoordinates.symm.measurable)))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r _
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  change ENNReal.ofReal ((coordinatePlaneParam r p 0)^2 *
      Real.sin (coordinatePlaneParam r p 2)) * g (sphericalMap (coordinatePlaneParam r p)) = _
  simp [sphericalMap]
  rfl

/-- Radial disintegration of volume into normalized surface areas. -/
theorem volume_eq_lintegral_sphere_sections_zero {A : Set AmbientSpace} (hA : MeasurableSet A) :
    volume A = ∫⁻ r in Ioi (0 : ℝ), hausdorffMeasure2 3 (A ∩ sphere 0 r) := by
  rw [← lintegral_indicator_one hA]
  rw [lintegral_spherical_coordinates (show Measurable (A.indicator 1) from
    measurable_const.indicator hA)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [hausdorffMeasure2_sphere_section_zero hA hr]
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p hp
  have hs : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
  simp only [abs_of_pos hs]
  rfl

/-- Spherical slicing at the origin for Borel sets, written using an open radial slab. -/
theorem spherical_slicing_zero_measurable {A : Set AmbientSpace} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ r in Ioo a b, hausdorffMeasure2 3 (A ∩ sphere (0 : AmbientSpace) r) =
      volume (A ∩ {x | a < ‖x‖ ∧ ‖x‖ < b}) := by
  have hm : MeasurableSet (A ∩ {x | a < ‖x‖ ∧ ‖x‖ < b}) :=
    hA.inter (measurableSet_Ioo.preimage continuous_norm.measurable)
  rw [volume_eq_lintegral_sphere_sections_zero hm]
  have heq (r : ℝ) : hausdorffMeasure2 3
      ((A ∩ {x | a < ‖x‖ ∧ ‖x‖ < b}) ∩ sphere 0 r) =
      (Ioo a b).indicator (fun s => hausdorffMeasure2 3 (A ∩ sphere 0 s)) r := by
    by_cases hr : r ∈ Ioo a b
    · rw [indicator_of_mem hr]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_sphere_zero_iff_norm]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2 ▸ hr⟩, h.2⟩
    · rw [indicator_of_notMem hr]
      have hs : (A ∩ {x | a < ‖x‖ ∧ ‖x‖ < b}) ∩ sphere 0 r = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨_, hx⟩, hs⟩
        exact hr ((mem_sphere_zero_iff_norm.mp hs) ▸ hx)
      rw [hs, measure_empty]
  simp_rw [heq]
  rw [setLIntegral_indicator measurableSet_Ioo]
  rw [inter_eq_left.mpr (show Ioo a b ⊆ Ioi 0 from fun r hr => ha.trans_lt hr.1)]

lemma hausdorffMeasure2_sphere_section_translate (A : Set AmbientSpace) (c : AmbientSpace)
    (r : ℝ) :
    hausdorffMeasure2 3 (A ∩ sphere c r) =
      hausdorffMeasure2 3 (((fun x => c + x) ⁻¹' A) ∩ sphere (0 : AmbientSpace) r) := by
  have him : (fun x : AmbientSpace => c + x) ''
      (((fun x => c + x) ⁻¹' A) ∩ sphere (0 : AmbientSpace) r) = A ∩ sphere c r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hx.1, ?_⟩
      simpa only [mem_sphere, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx.2
    · intro hy
      refine ⟨y - c, ⟨?_, ?_⟩, by abel_nf⟩
      · change c + (y - c) ∈ A
        convert hy.1 using 1
        abel_nf
      · simpa only [mem_sphere, dist_eq_norm, sub_zero] using hy.2
  rw [← him]
  exact (isometry_add_left c).euclideanHausdorffMeasure_image _

/-- Spherical slicing at any center for Borel sets. -/
theorem spherical_slicing_measurable {A : Set AmbientSpace} (hA : MeasurableSet A)
    (c : AmbientSpace) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ r in Ioo a b, hausdorffMeasure2 3 (A ∩ sphere c r) =
      volume (A ∩ {x | a < dist x c ∧ dist x c < b}) := by
  simp_rw [hausdorffMeasure2_sphere_section_translate A c]
  rw [spherical_slicing_zero_measurable (hA.preimage (by fun_prop)) ha]
  have hset : ((fun x => c + x) ⁻¹' A) ∩ {x | a < ‖x‖ ∧ ‖x‖ < b} =
      (fun x => c + x) ⁻¹' (A ∩ {x | a < dist x c ∧ dist x c < b}) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, dist_eq_norm, add_sub_cancel_left]
  rw [hset]
  apply (measurePreserving_add_left volume c).measure_preimage
  exact (hA.inter (measurableSet_Ioo.preimage (by fun_prop))).nullMeasurableSet

lemma open_radial_slab_ae_eq_annulus (c : AmbientSpace) (a b : ℝ) :
    {x | a < dist x c ∧ dist x c < b} =ᵐ[volume] ball c b \ ball c a := by
  have hn : ∀ᵐ x : AmbientSpace ∂volume, x ∉ sphere c a :=
    (measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume c a)
  filter_upwards [hn] with x hx
  have hne : dist x c ≠ a := hx
  apply propext
  change (a < dist x c ∧ dist x c < b) ↔ (dist x c < b ∧ ¬dist x c < a)
  rw [not_lt]
  constructor
  · intro h
    exact ⟨h.2, h.1.le⟩
  · intro h
    exact ⟨lt_of_le_of_ne h.2 hne.symm, h.1⟩

/-- Spherical slicing uses the density-one representative on the spheres and
ordinary volume of the original set in the annulus. No perimeter hypothesis is needed. -/
theorem spherical_slicing {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ r in Ioo a b, hausdorffMeasure2 3 (densityOne E ∩ sphere c r) =
      volume (E ∩ (ball c b \ ball c a)) := by
  rw [spherical_slicing_measurable (measurableSet_densityOne hE) c ha]
  exact measure_congr ((densityOne_ae_eq (by norm_num : 0 < 3) hE).inter
    (open_radial_slab_ae_eq_annulus c a b))

/-- The area of the spherical section of a Borel set is a Borel function of radius. -/
lemma measurable_sphere_sections_zero {A : Set AmbientSpace} (hA : MeasurableSet A) :
    Measurable (fun r : ℝ => hausdorffMeasure2 3 (A ∩ sphere (0 : AmbientSpace) r)) := by
  let F (r : ℝ) := ∫⁻ p in sphereParamDomain,
    ENNReal.ofReal (r ^ 2 * |Real.sin (p 1)|) *
      A.indicator (fun _ => (1 : ℝ≥0∞)) (r • sphereParam p)
  have hf : Measurable F := by
    have hj : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
        ENNReal.ofReal (z.1 ^ 2 * |Real.sin (z.2 1)|) *
          A.indicator (fun _ => (1 : ℝ≥0∞)) (z.1 • sphereParam z.2)) :=
      (by fun_prop : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) =>
        ENNReal.ofReal (z.1 ^ 2 * |Real.sin (z.2 1)|))).mul
        ((measurable_const.indicator hA).comp
          (continuous_fst.smul
            (lipschitzWith_sphereParam.continuous.comp continuous_snd)).measurable)
    exact hj.lintegral_prod_right' (ν := volume.restrict sphereParamDomain)
  have heq : (fun r : ℝ => hausdorffMeasure2 3 (A ∩ sphere (0 : AmbientSpace) r)) =
      fun r => if 0 < r then F r else 0 := by
    funext r
    split_ifs with hr
    · exact hausdorffMeasure2_sphere_section_zero hA hr
    · rcases lt_or_eq_of_le (le_of_not_gt hr) with hlt | rfl
      · rw [sphere_eq_empty_of_neg hlt, inter_empty, measure_empty]
      · rw [sphere_zero]
        exact hausdorffMeasure2_subsingleton (Set.subsingleton_singleton.anti inter_subset_right)
  rw [heq]
  exact Measurable.ite measurableSet_Ioi hf measurable_const

lemma measurable_sphere_sections {A : Set AmbientSpace} (hA : MeasurableSet A)
    (c : AmbientSpace) :
    Measurable (fun r : ℝ => hausdorffMeasure2 3 (A ∩ sphere c r)) := by
  simp_rw [hausdorffMeasure2_sphere_section_translate A c]
  exact measurable_sphere_sections_zero (hA.preimage (by fun_prop))

/-- The spherical identity in the blueprint's boundary-of-ball notation. -/
theorem spherical_slicing_frontier {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ r in Ioo a b, hausdorffMeasure2 3 (densityOne E ∩ frontier (ball c r)) =
      volume (E ∩ (ball c b \ ball c a)) := by
  rw [← spherical_slicing hE c ha b]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  rw [frontier_ball c (ha.trans_lt hr.1).ne']

/-- The surface measure is the pushforward of the explicit spherical area density. -/
lemma map_sphereParam_withDensity (c : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun p => c + r • sphereParam p)
      ((volume.restrict sphereParamDomain).withDensity
        (fun p => ENNReal.ofReal (r ^ 2 * |Real.sin (p 1)|))) =
      (hausdorffMeasure2 3).restrict (sphere c r) := by
  have hm : Measurable (fun p => c + r • sphereParam p) :=
    (continuous_const.add (lipschitzWith_sphereParam.continuous.const_smul r)).measurable
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA, Measure.restrict_apply hA,
    hausdorffMeasure2_sphere_section_translate A c,
    hausdorffMeasure2_sphere_section_zero (hA.preimage (by fun_prop)) hr,
    withDensity_apply _ (hA.preimage hm), Measure.restrict_restrict (hA.preimage hm),
    ← setLIntegral_indicator (hA.preimage hm)]
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  by_cases hp : c + r • sphereParam p ∈ A <;> simp [hp]

/-- Weighted surface integration in spherical parameters, for nonnegative Borel weights. -/
lemma lintegral_sphere_eq_param (c : AmbientSpace) {r : ℝ} (hr : 0 < r)
    {g : AmbientSpace → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y in sphere c r, g y ∂hausdorffMeasure2 3 =
      ∫⁻ p in sphereParamDomain, ENNReal.ofReal (r ^ 2 * |Real.sin (p 1)|) *
        g (c + r • sphereParam p) := by
  have hm : Measurable (fun p => c + r • sphereParam p) :=
    (continuous_const.add (lipschitzWith_sphereParam.continuous.const_smul r)).measurable
  rw [← map_sphereParam_withDensity c hr, lintegral_map hg hm]
  simpa only [Function.comp_def, Pi.mul_apply] using
    lintegral_withDensity_eq_lintegral_mul (volume.restrict sphereParamDomain)
      (by fun_prop : Measurable (fun p : EuclideanSpace ℝ (Fin 2) =>
        ENNReal.ofReal (r ^ 2 * |Real.sin (p 1)|))) (hg.comp hm)

/-- Nonnegative weighted radial disintegration, with arbitrary center and infinite values. -/
theorem lintegral_radial_disintegration (c : AmbientSpace)
    {g : AmbientSpace → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ y in sphere c r, g y ∂hausdorffMeasure2 3 := by
  rw [← (measurePreserving_add_left volume c).lintegral_comp hg]
  rw [lintegral_spherical_coordinates (g := fun y => g (c + y))
    (hg.comp (by fun_prop : Measurable (fun y : AmbientSpace => c + y)))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [lintegral_sphere_eq_param c hr hg]
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p hp
  have hs : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
  simp only [abs_of_pos hs]

lemma abs_det_sphericalMapDeriv_of_mem {x : AmbientSpace} (hx : x ∈ sphericalDomain) :
    |(sphericalMapDeriv x).det| = (x 0)^2 * Real.sin (x 2) := by
  have hs : 0 < Real.sin (x 2) := by
    simpa only [sphericalAngles_one] using
      Real.sin_pos_of_pos_of_lt_pi hx.2.2.1 hx.2.2.2
  rw [det_sphericalMapDeriv, abs_mul, abs_neg, abs_pow, sq_abs, abs_of_pos hs]

section Bochner
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma integral_sphere_eq_param (c : AmbientSpace) {r : ℝ} (hr : 0 < r)
    {g : AmbientSpace → F} (hg : StronglyMeasurable g) :
    ∫ y in sphere c r, g y ∂hausdorffMeasure2 3 =
      ∫ p in sphereParamDomain, (r ^ 2 * |Real.sin (p 1)|) • g (c + r • sphereParam p) := by
  have hm : Measurable (fun p => c + r • sphereParam p) :=
    (continuous_const.add (lipschitzWith_sphereParam.continuous.const_smul r)).measurable
  rw [← map_sphereParam_withDensity c hr, integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  dsimp only
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg r) (abs_nonneg _))]

lemma integral_sphericalMap (g : AmbientSpace → F) :
    ∫ y, g y = ∫ x in sphericalDomain, ((x 0)^2 * Real.sin (x 2)) • g (sphericalMap x) := by
  calc
    _ = ∫ y in sphericalMap '' sphericalDomain, g y := by
      rw [setIntegral_congr_set sphericalMap_image_ae_eq_univ, setIntegral_univ]
    _ = ∫ x in sphericalDomain, |(sphericalMapDeriv x).det| • g (sphericalMap x) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_sphericalDomain
        (fun x _ => (hasFDerivAt_sphericalMap x).hasFDerivWithinAt) sphericalMap_injOn g
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_sphericalDomain
      intro x hx
      dsimp only
      rw [abs_det_sphericalMapDeriv_of_mem hx]

lemma integrable_sphericalMap {g : AmbientSpace → F} (hg : Integrable g volume) :
    IntegrableOn (fun x => ((x 0)^2 * Real.sin (x 2)) • g (sphericalMap x)) sphericalDomain := by
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_sphericalDomain (fun x _ => (hasFDerivAt_sphericalMap x).hasFDerivWithinAt)
    sphericalMap_injOn g).mp hg.integrableOn
  apply h.congr_fun _ measurableSet_sphericalDomain
  intro x hx
  dsimp only
  rw [abs_det_sphericalMapDeriv_of_mem hx]

lemma integral_spherical_coordinates {g : AmbientSpace → F} (hg : Integrable g volume) :
    ∫ y, g y = ∫ r in Ioi (0 : ℝ), ∫ p in sphereParamDomain,
      (r ^ 2 * Real.sin (p 1)) • g (r • sphereParam p) := by
  rw [integral_sphericalMap]
  have hset : slicingCoordinates.symm ⁻¹' sphericalDomain =
      Ioi (0 : ℝ) ×ˢ sphereParamDomain := by
    ext z
    rcases z with ⟨r, p⟩
    change (0 < coordinatePlaneParam r p 0 ∧
      sphericalAngles (coordinatePlaneParam r p) ∈ sphereParamDomain) ↔ _
    simp
  have hi := (measurePreserving_slicingCoordinates.symm.integrableOn_comp_preimage
    slicingCoordinates.symm.measurableEmbedding).mpr (integrable_sphericalMap hg)
  rw [hset] at hi
  have h := measurePreserving_slicingCoordinates.symm.setIntegral_preimage_emb
    slicingCoordinates.symm.measurableEmbedding
    (fun x => ((x 0)^2 * Real.sin (x 2)) • g (sphericalMap x)) sphericalDomain
  rw [hset] at h
  rw [← h]
  change (∫ z in Ioi (0 : ℝ) ×ˢ sphereParamDomain,
    ((slicingCoordinates.symm z 0)^2 * Real.sin (slicingCoordinates.symm z 2)) •
      g (sphericalMap (slicingCoordinates.symm z)) ∂volume.prod volume) = _
  rw [setIntegral_prod _ (by simpa only [Function.comp_def, Measure.volume_eq_prod] using hi)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  apply setIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  change ((coordinatePlaneParam r p 0)^2 * Real.sin (coordinatePlaneParam r p 2)) •
    g (sphericalMap (coordinatePlaneParam r p)) = _
  simp [sphericalMap]
  rfl

/-- Radial disintegration for integrable Banach-valued Borel functions, including
real and Euclidean vector weights. -/
theorem integral_radial_disintegration (c : AmbientSpace)
    {g : AmbientSpace → F} (hm : StronglyMeasurable g) (hi : Integrable g volume) :
    ∫ y, g y = ∫ r in Ioi (0 : ℝ), ∫ y in sphere c r, g y ∂hausdorffMeasure2 3 := by
  have ht : Integrable (fun y => g (c + y)) volume :=
    (measurePreserving_add_left volume c).integrable_comp_of_integrable hi
  rw [← (measurePreserving_add_left volume c).integral_comp
    (Homeomorph.addLeft c).measurableEmbedding g]
  rw [integral_spherical_coordinates ht]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [integral_sphere_eq_param c hr hm]
  apply setIntegral_congr_fun measurableSet_sphereParamDomain
  intro p hp
  have hs : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
  simp only [abs_of_pos hs]

end Bochner

end LiquidDrop
