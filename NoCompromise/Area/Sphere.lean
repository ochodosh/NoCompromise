module

public import NoCompromise.Area.Cofactor
public import NoCompromise.Area.Formula
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Area of Euclidean spheres

A globally Lipschitz longitude and colatitude parametrization is injective on its
open parameter rectangle and covers the unit sphere on the closed rectangle. The
rectangle boundary has zero planar measure and hence its image has zero Hausdorff
area. The blueprint-proved planar-source area formula, the explicit sine Jacobian,
and elementary one-dimensional integration give area `4 * π`. Hausdorff dilation
and isometry invariance then give arbitrary positive radii and centers. No sphere
perimeter formula or packaged lower-dimensional area theorem is used.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

namespace LiquidDrop

/-- Longitude and colatitude parametrization of the unit sphere. -/
def sphereParam (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  (Real.sin (x 1) * Real.cos (x 0)) • EuclideanSpace.single 0 1 +
    (Real.sin (x 1) * Real.sin (x 0)) • EuclideanSpace.single 1 1 +
    Real.cos (x 1) • EuclideanSpace.single 2 1

@[simp] lemma sphereParam_zero (x : EuclideanSpace ℝ (Fin 2)) :
    sphereParam x 0 = Real.sin (x 1) * Real.cos (x 0) := by simp [sphereParam]

@[simp] lemma sphereParam_one (x : EuclideanSpace ℝ (Fin 2)) :
    sphereParam x 1 = Real.sin (x 1) * Real.sin (x 0) := by simp [sphereParam]

@[simp] lemma sphereParam_two (x : EuclideanSpace ℝ (Fin 2)) :
    sphereParam x 2 = Real.cos (x 1) := by simp [sphereParam]

lemma norm_sphereParam (x : EuclideanSpace ℝ (Fin 2)) : ‖sphereParam x‖ = 1 := by
  have hs : ‖sphereParam x‖ ^ 2 = 1 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      sphereParam_zero, sphereParam_one, sphereParam_two]
    nlinarith [Real.sin_sq_add_cos_sq (x 1), Real.cos_sq_add_sin_sq (x 0),
      sq_nonneg (Real.sin (x 1))]
  nlinarith [norm_nonneg (sphereParam x)]

private lemma norm_product_sub_le {a b c d : ℝ} (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    ‖a * b - c * d‖ ≤ ‖b - d‖ + ‖a - c‖ := by
  calc
    _ = ‖a * (b - d) + (a - c) * d‖ := by congr 1; ring
    _ ≤ ‖a * (b - d)‖ + ‖(a - c) * d‖ := norm_add_le _ _
    _ ≤ 1 * ‖b - d‖ + ‖a - c‖ * 1 := by
      rw [norm_mul, norm_mul]
      gcongr
    _ = _ := by ring

lemma lipschitzWith_sphereParam : LipschitzWith 3 sphereParam := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  have hc (i : Fin 2) : ‖x i - y i‖ ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) i
  have hs (i : Fin 2) : ‖Real.sin (x i) - Real.sin (y i)‖ ≤ ‖x - y‖ :=
    (Real.lipschitzWith_sin.norm_sub_le _ _).trans (by simpa using hc i)
  have ht (i : Fin 2) : ‖Real.cos (x i) - Real.cos (y i)‖ ≤ ‖x - y‖ :=
    (Real.lipschitzWith_cos.norm_sub_le _ _).trans (by simpa using hc i)
  have h0 : ‖(sphereParam x - sphereParam y) 0‖ ≤ 2 * ‖x - y‖ := by
    simp only [PiLp.sub_apply, sphereParam_zero]
    have h := norm_product_sub_le (b := Real.cos (x 0)) (c := Real.sin (y 1))
      (Real.abs_sin_le_one (x 1)) (Real.abs_cos_le_one (y 0))
    change ‖Real.sin (x 1) * Real.cos (x 0) - Real.sin (y 1) * Real.cos (y 0)‖ ≤ _
    exact h.trans (by linarith [hs 1, ht 0])
  have h1 : ‖(sphereParam x - sphereParam y) 1‖ ≤ 2 * ‖x - y‖ := by
    simp only [PiLp.sub_apply, sphereParam_one]
    have h := norm_product_sub_le (b := Real.sin (x 0)) (c := Real.sin (y 1))
      (Real.abs_sin_le_one (x 1)) (Real.abs_sin_le_one (y 0))
    exact h.trans (by linarith [hs 1, hs 0])
  have h2 : ‖(sphereParam x - sphereParam y) 2‖ ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, sphereParam_two] using ht 1
  have hsq := EuclideanSpace.real_norm_sq_eq (sphereParam x - sphereParam y)
  simp only [Fin.sum_univ_three] at hsq
  have ha := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖x - y‖) |>.mpr h0
  have hb := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖x - y‖) |>.mpr h1
  have hc := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h2
  simp only [Real.norm_eq_abs, sq_abs] at ha hb hc
  nlinarith [norm_nonneg (sphereParam x - sphereParam y), norm_nonneg (x - y)]

/-- The explicit derivative of the longitude and colatitude map. -/
def sphereParamDeriv (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((Real.sin (x 1) * -Real.sin (x 0)) • EuclideanSpace.proj 0 +
      (Real.cos (x 0) * Real.cos (x 1)) • EuclideanSpace.proj 1 :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single 0 1) +
    ((Real.sin (x 1) * Real.cos (x 0)) • EuclideanSpace.proj 0 +
      (Real.sin (x 0) * Real.cos (x 1)) • EuclideanSpace.proj 1 :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single 1 1) +
    (-Real.sin (x 1) • EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 2 1)

lemma hasFDerivAt_sphereParam (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt sphereParam (sphereParamDeriv x) x := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt (x := x)
  convert! ((h1.sin.mul h0.cos).smul_const (EuclideanSpace.single (ι := Fin 3) (𝕜 := ℝ) 0 1)).add
    ((h1.sin.mul h0.sin).smul_const (EuclideanSpace.single (ι := Fin 3) (𝕜 := ℝ) 1 1)) |>.add
    (h1.cos.smul_const (EuclideanSpace.single (ι := Fin 3) (𝕜 := ℝ) 2 1)) using 1
  simp only [sphereParamDeriv, smul_smul]
  congr 1

lemma cross3_sphereParamDeriv (x : EuclideanSpace ℝ (Fin 2)) :
    cross3 (sphereParamDeriv x (EuclideanSpace.single 0 1))
      (sphereParamDeriv x (EuclideanSpace.single 1 1)) =
      -Real.sin (x 1) • sphereParam x := by
  have h := congrArg (fun t => -(Real.sin (x 1) * Real.cos (x 1)) * t)
    (Real.sin_sq_add_cos_sq (x 0))
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [crossProduct, sphereParamDeriv, sphereParam]
  · ring
  · ring
  · nlinarith [h]

lemma jacobian2_sphereParam (x : EuclideanSpace ℝ (Fin 2)) :
    jacobian2 sphereParam x = |Real.sin (x 1)| := by
  rw [jacobian2, (hasFDerivAt_sphereParam x).fderiv,
    jacobian2Linear_eq_norm_cross3, cross3_sphereParamDeriv, norm_smul,
    norm_sphereParam, mul_one, norm_neg, Real.norm_eq_abs]

/-- The open longitude and colatitude rectangle. -/
def sphereParamDomain : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ∈ Ioo (-Real.pi) Real.pi ∧ x 1 ∈ Ioo 0 Real.pi}

/-- The closed parameter rectangle, including the seam and the poles. -/
def sphereParamClosedDomain : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ∈ Icc (-Real.pi) Real.pi ∧ x 1 ∈ Icc 0 Real.pi}

lemma measurableSet_sphereParamDomain : MeasurableSet sphereParamDomain :=
  ((measurableSet_Ioo.preimage (EuclideanSpace.proj 0).continuous.measurable).inter
    (measurableSet_Ioo.preimage (EuclideanSpace.proj 1).continuous.measurable))

lemma sphereParam_injOn : InjOn sphereParam sphereParamDomain := by
  intro x hx y hy hxy
  have hp : x 1 = y 1 := Real.injOn_cos ⟨hx.2.1.le, hx.2.2.le⟩
    ⟨hy.2.1.le, hy.2.2.le⟩ (by simpa using congrArg (fun z => z 2) hxy)
  have hsin : 0 < Real.sin (x 1) := Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
  have hpolar : (Real.sin (x 1), x 0) = (Real.sin (y 1), y 0) := by
    have hpx : (Real.sin (x 1), x 0) ∈ polarCoord.target := ⟨hsin, hx.1⟩
    have hpy : (Real.sin (y 1), y 0) ∈ polarCoord.target := ⟨hp ▸ hsin, hy.1⟩
    apply polarCoord.symm.injOn hpx hpy
    apply Prod.ext
    · simpa using congrArg (fun z => z 0) hxy
    · simpa using congrArg (fun z => z 1) hxy
  apply PiLp.ext
  intro i
  fin_cases i
  · exact congrArg Prod.snd hpolar
  · exact hp

/-- The closed rectangle parametrizes the entire unit sphere. -/
lemma sphereParam_image_closedDomain :
    sphereParam '' sphereParamClosedDomain = sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, _, rfl⟩
    simpa only [mem_sphere_zero_iff_norm] using norm_sphereParam x
  · intro y hy
    have hn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hc : |y 2| ≤ 1 := by simpa [hn, Real.norm_eq_abs] using PiLp.norm_apply_le y 2
    obtain ⟨φ, hφ, hcos⟩ := Real.surjOn_cos (show y 2 ∈ Icc (-1 : ℝ) 1 by
      exact abs_le.mp hc)
    let z : ℂ := ⟨y 0, y 1⟩
    have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφ
    have hz : ‖z‖ = Real.sin φ := by
      have hsq := EuclideanSpace.real_norm_sq_eq y
      simp only [Fin.sum_univ_three, hn, one_pow] at hsq
      have hzs : ‖z‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
        rw [Complex.sq_norm]
        change y 0 * y 0 + y 1 * y 1 = _
        ring
      rw [← hcos] at hsq
      nlinarith [Real.sin_sq_add_cos_sq φ, norm_nonneg z]
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.arg, φ]
    refine ⟨x, ⟨⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, hφ⟩, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [sphereParam, x, ← hz, z]
    · simp [sphereParam, x, ← hz, z]
    · simpa [x] using hcos

private lemma ae_sphereParam_coordinate_ne (i : Fin 2) (a : ℝ) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 2) ∂volume, x i ≠ a := by
  exact (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae
    (Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) i a)

/-- The parameter rectangle boundary has zero two-dimensional volume. -/
lemma sphereParamClosedDomain_ae_eq : sphereParamClosedDomain =ᵐ[volume] sphereParamDomain := by
  filter_upwards [ae_sphereParam_coordinate_ne 0 (-Real.pi),
    ae_sphereParam_coordinate_ne 0 Real.pi, ae_sphereParam_coordinate_ne 1 0,
    ae_sphereParam_coordinate_ne 1 Real.pi] with x h0 h1 h2 h3
  simp only [sphereParamClosedDomain, sphereParamDomain, mem_Icc, mem_Ioo]
  exact propext ⟨fun h => ⟨⟨lt_of_le_of_ne h.1.1 h0.symm, lt_of_le_of_ne h.1.2 h1⟩,
    ⟨lt_of_le_of_ne h.2.1 h2.symm, lt_of_le_of_ne h.2.2 h3⟩⟩,
    fun h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩⟩

/-- The planar area formula applies after discarding the null parameter boundary. -/
lemma hausdorffMeasure2_unit_sphere_eq_param_area :
    hausdorffMeasure2 3 (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      ∫⁻ x in sphereParamDomain, ENNReal.ofReal |Real.sin (x 1)| := by
  have hn : hausdorffMeasure2 3
      (sphereParam '' (sphereParamClosedDomain \ sphereParamDomain)) = 0 :=
    hausdorffMeasure2_image_null lipschitzWith_sphereParam
      (ae_le_set.mp sphereParamClosedDomain_ae_eq.le)
  have hsub : sphereParamDomain ⊆ sphereParamClosedDomain :=
    fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩
  have heq : sphereParamClosedDomain =
      sphereParamDomain ∪ (sphereParamClosedDomain \ sphereParamDomain) :=
    by rw [union_sdiff_self, union_eq_self_of_subset_left hsub]
  rw [← sphereParam_image_closedDomain, heq, image_union,
    measure_congr (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hn)),
    hausdorffMeasure2_image_eq_lintegral_jacobian_of_lipschitz lipschitzWith_sphereParam
      measurableSet_sphereParamDomain sphereParam_injOn]
  simp only [jacobian2_sphereParam]

private def sphereParameterEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => WithLp.toLp 2 ![p.1, p.2]
      invFun := fun x => (x 0, x 1)
      left_inv := by intro p; rcases p with ⟨x, y⟩; rfl
      right_inv := by intro x; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_add' := by intro p q; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_smul' := by intro r p; apply PiLp.ext; intro i; fin_cases i <;> rfl }

private lemma measurePreserving_sphereParameterEquiv : MeasurePreserving sphereParameterEquiv := by
  have h : MeasurePreserving sphereParameterEquiv.symm := by
    have h := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
    convert h using 1 <;> rfl
  exact MeasurePreserving.symm sphereParameterEquiv.symm.toHomeomorph.toMeasurableEquiv h

/-- The sine area density has integral two over the colatitude interval. -/
lemma lintegral_sin_colatitude :
    ∫⁻ t in Ioo (0 : ℝ) Real.pi, ENNReal.ofReal |Real.sin t| = 2 := by
  have hi : IntegrableOn Real.sin (Ioo 0 Real.pi) :=
    Real.continuous_sin.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have heq : (∫ t in Ioo (0 : ℝ) Real.pi, Real.sin t) = 2 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le Real.pi_pos.le, integral_sin]
    norm_num
  calc
    _ = ∫⁻ t in Ioo (0 : ℝ) Real.pi, ENNReal.ofReal (Real.sin t) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp only [abs_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)]
    _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) Real.pi, Real.sin t) :=
      (ofReal_integral_eq_lintegral_ofReal hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).le)).symm
    _ = 2 := by rw [heq]; norm_num

/-- The normalized Hausdorff area of the unit two-sphere is `4 * π`. -/
theorem hausdorffMeasure2_unit_sphere :
    hausdorffMeasure2 3 (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [hausdorffMeasure2_unit_sphere_eq_param_area]
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal |Real.sin (x 1)|) := by fun_prop
  rw [← measurePreserving_sphereParameterEquiv.setLIntegral_comp_preimage
    measurableSet_sphereParamDomain hm]
  change (∫⁻ p : ℝ × ℝ in Ioo (-Real.pi) Real.pi ×ˢ Ioo 0 Real.pi,
    ENNReal.ofReal |Real.sin p.2| ∂(volume.prod volume)) = _
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_sin_colatitude, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioo, sub_neg_eq_add]
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

open scoped Pointwise in
/-- Hausdorff dilation gives the area at every positive radius. -/
theorem hausdorffMeasure2_sphere_zero {R : ℝ} (hR : 0 < R) :
    hausdorffMeasure2 3 (sphere (0 : EuclideanSpace ℝ (Fin 3)) R) =
      ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  have hs : R • sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 = sphere 0 R := by
    simpa only [smul_zero, Real.norm_of_nonneg hR.le, mul_one] using
      smul_sphere' hR.ne' (0 : EuclideanSpace ℝ (Fin 3)) 1
  rw [← hs]
  change Measure.euclideanHausdorffMeasure 2 (R • sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = _
  rw [Measure.euclideanHausdorffMeasure_smul₀ 2 hR.ne']
  change (‖R‖₊ ^ 2 : ℝ≥0∞) * hausdorffMeasure2 3 (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = _
  rw [hausdorffMeasure2_unit_sphere]
  have hn : (‖R‖₊ : ℝ≥0∞) = ENNReal.ofReal R := by
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal ‖R‖ = ENNReal.ofReal R
    rw [Real.norm_of_nonneg hR.le]
  rw [hn, ← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (sq_nonneg R)]
  congr 1
  ring

/-- The area of a sphere is independent of its center and equals `4 * π * R²`. -/
theorem hausdorffMeasure2_sphere (c : EuclideanSpace ℝ (Fin 3)) {R : ℝ} (hR : 0 < R) :
    hausdorffMeasure2 3 (sphere c R) = ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  have hi : Isometry (fun x : EuclideanSpace ℝ (Fin 3) => c + x) := isometry_add_left c
  have heq : (fun x : EuclideanSpace ℝ (Fin 3) => c + x) '' sphere 0 R = sphere c R := by
    ext y
    simp only [mem_image, mem_sphere]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
    · intro hy
      refine ⟨y - c, ?_, by simp⟩
      simpa only [dist_eq_norm, sub_zero] using hy
  rw [← heq]
  change Measure.euclideanHausdorffMeasure 2 ((fun x => c + x) '' sphere 0 R) = _
  rw [hi.euclideanHausdorffMeasure_image]
  exact hausdorffMeasure2_sphere_zero hR

/-- The boundary of a positive-radius Euclidean ball has area `4 * π * R²`. -/
theorem hausdorffMeasure2_frontier_ball (c : EuclideanSpace ℝ (Fin 3)) {R : ℝ}
    (hR : 0 < R) :
    hausdorffMeasure2 3 (frontier (ball c R)) = ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  rw [frontier_ball c hR.ne']
  exact hausdorffMeasure2_sphere c hR

end LiquidDrop
