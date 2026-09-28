import NoCompromise.CapacitaryK.Calculus
import NoCompromise.BV.SphericalSlicing

/-!
# The area formula for a radial graph over the unit sphere

Let `ρ` be `C¹` off the origin and positive on the unit sphere. The radial graph
`{ρ θ • θ + z : ‖θ‖ = 1}` is parametrized by `p ↦ ρ (σ p) • σ p + z`, where `σ` is the
longitude and colatitude parametrization of the unit sphere. Only the values of `ρ` and of
its derivative on the compact sphere enter, so this parametrization is globally Lipschitz,
and it is injective on the open parameter rectangle. Its Gram Jacobian is
`ρ √(ρ² + |∇ρ - ⟨∇ρ, θ⟩ θ|²) |sin|`, computed from the orthogonal spherical frame. The
planar-source area formula, the Hausdorff-null image of the rectangle boundary, and the
spherical-coordinate form of the surface measure then give the area formula for
nonnegative Borel weights, the pushforward identity for the surface measure, and the
Bochner form, which needs no integrability hypothesis.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace

namespace LiquidDrop
namespace CapacitaryK

set_option maxSynthPendingDepth 8

private lemma sphereParamDeriv_e0_apply (p : EuclideanSpace ℝ (Fin 2)) :
    sphereParamDeriv p (EuclideanSpace.single 0 1) =
      WithLp.toLp 2 ![-(Real.sin (p 1) * Real.sin (p 0)),
        Real.sin (p 1) * Real.cos (p 0), 0] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphereParamDeriv]

private lemma sphereParamDeriv_e1_apply (p : EuclideanSpace ℝ (Fin 2)) :
    sphereParamDeriv p (EuclideanSpace.single 1 1) =
      WithLp.toLp 2 ![Real.cos (p 0) * Real.cos (p 1),
        Real.sin (p 0) * Real.cos (p 1), -Real.sin (p 1)] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphereParamDeriv]

private lemma inner_three (u v : E3) : ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  ring

private lemma norm_sq_three (u : E3) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The Gram determinant of the columns of the radial-graph derivative. -/
private lemma gram_radial {a b θ g : E3} {r s : ℝ} (hθ : ‖θ‖ = 1) (haθ : ⟪a, θ⟫_ℝ = 0)
    (hbθ : ⟪b, θ⟫_ℝ = 0) (hab : ⟪a, b⟫_ℝ = 0) (ha : ‖a‖ ^ 2 = s ^ 2) (hb : ‖b‖ ^ 2 = 1)
    (hP : ⟪g, a⟫_ℝ ^ 2 + s ^ 2 * ⟪g, b⟫_ℝ ^ 2 + s ^ 2 * ⟪g, θ⟫_ℝ ^ 2 = s ^ 2 * ‖g‖ ^ 2) :
    ‖r • a + ⟪g, a⟫_ℝ • θ‖ ^ 2 * ‖r • b + ⟪g, b⟫_ℝ • θ‖ ^ 2 -
        ⟪r • a + ⟪g, a⟫_ℝ • θ, r • b + ⟪g, b⟫_ℝ • θ⟫_ℝ ^ 2 =
      (r * s) ^ 2 * (r ^ 2 + ‖g - ⟪g, θ⟫_ℝ • θ‖ ^ 2) := by
  have hθa : ⟪θ, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact haθ
  have hθb : ⟪θ, b⟫_ℝ = 0 := by rw [real_inner_comm]; exact hbθ
  have hθθ : ⟪θ, θ⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hθ, one_pow]
  have haa : ⟪a, a⟫_ℝ = s ^ 2 := by rw [real_inner_self_eq_norm_sq, ha]
  have hbb : ⟪b, b⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hb]
  have e1 : ‖r • a + ⟪g, a⟫_ℝ • θ‖ ^ 2 = r ^ 2 * s ^ 2 + ⟪g, a⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      haθ, hθa, hθθ, haa]
    ring
  have e2 : ‖r • b + ⟪g, b⟫_ℝ • θ‖ ^ 2 = r ^ 2 + ⟪g, b⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hbθ, hθb, hθθ, hbb]
    ring
  have e3 : ⟪r • a + ⟪g, a⟫_ℝ • θ, r • b + ⟪g, b⟫_ℝ • θ⟫_ℝ = ⟪g, a⟫_ℝ * ⟪g, b⟫_ℝ := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      haθ, hθb, hθθ, hab]
    ring
  have e4 : ‖g - ⟪g, θ⟫_ℝ • θ‖ ^ 2 = ‖g‖ ^ 2 - ⟪g, θ⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq g]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hθθ, real_inner_comm θ g]
    ring
  rw [e1, e2, e3, e4]
  linear_combination r ^ 2 * hP

/-- The orthogonality relations of the spherical-coordinate frame and the corresponding
Parseval identity for an arbitrary vector `g`. -/
private lemma sphereParam_frame (p : EuclideanSpace ℝ (Fin 2)) (g : E3) :
    ⟪sphereParamDeriv p (EuclideanSpace.single 0 1), sphereParam p⟫_ℝ = 0 ∧
    ⟪sphereParamDeriv p (EuclideanSpace.single 1 1), sphereParam p⟫_ℝ = 0 ∧
    ⟪sphereParamDeriv p (EuclideanSpace.single 0 1),
      sphereParamDeriv p (EuclideanSpace.single 1 1)⟫_ℝ = 0 ∧
    ‖sphereParamDeriv p (EuclideanSpace.single 0 1)‖ ^ 2 = Real.sin (p 1) ^ 2 ∧
    ‖sphereParamDeriv p (EuclideanSpace.single 1 1)‖ ^ 2 = 1 ∧
    ⟪g, sphereParamDeriv p (EuclideanSpace.single 0 1)⟫_ℝ ^ 2 +
        Real.sin (p 1) ^ 2 * ⟪g, sphereParamDeriv p (EuclideanSpace.single 1 1)⟫_ℝ ^ 2 +
        Real.sin (p 1) ^ 2 * ⟪g, sphereParam p⟫_ℝ ^ 2 = Real.sin (p 1) ^ 2 * ‖g‖ ^ 2 := by
  have h1 := Real.sin_sq_add_cos_sq (p 1)
  have h2 := Real.sin_sq_add_cos_sq (p 0)
  simp only [sphereParamDeriv_e0_apply, sphereParamDeriv_e1_apply, inner_three, norm_sq_three,
    sphereParam_zero, sphereParam_one, sphereParam_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨by ring, ?_, by ring, ?_, ?_, ?_⟩
  · linear_combination Real.sin (p 1) * Real.cos (p 1) * h2
  · linear_combination Real.sin (p 1) ^ 2 * h2
  · linear_combination Real.cos (p 1) ^ 2 * h2 + h1
  · linear_combination Real.sin (p 1) ^ 2 * ((Real.cos (p 0) ^ 2 * g 0 ^ 2 +
      Real.sin (p 0) ^ 2 * g 1 ^ 2 + g 2 ^ 2 + 2 * Real.cos (p 0) * Real.sin (p 0) * g 0 * g 1) *
      h1 + (g 0 ^ 2 + g 1 ^ 2) * h2)

lemma sphereParam_ne_zero (p : EuclideanSpace ℝ (Fin 2)) : sphereParam p ≠ 0 := by
  intro h
  have := norm_sphereParam p
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The spherical parametrization of the radial graph `θ ↦ ρ θ • θ + z`. -/
def radialGraphParam (ρ : E3 → ℝ) (z : E3) (p : EuclideanSpace ℝ (Fin 2)) : E3 :=
  ρ (sphereParam p) • sphereParam p + z

/-- The derivative of the spherical parametrization of a radial graph. -/
def radialGraphParamDeriv (ρ : E3 → ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] E3 :=
  ρ (sphereParam p) • sphereParamDeriv p +
    ((fderiv ℝ ρ (sphereParam p)).comp (sphereParamDeriv p)).smulRight (sphereParam p)

lemma hasFDerivAt_radialGraphParam {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0})
    (z : E3) (p : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (radialGraphParam ρ z) (radialGraphParamDeriv ρ p) p := by
  have hd : DifferentiableAt ℝ ρ (sphereParam p) :=
    (hρ.differentiableOn one_ne_zero).differentiableAt
      (isOpen_ne.mem_nhds (sphereParam_ne_zero p))
  exact ((hd.hasFDerivAt.comp p (hasFDerivAt_sphereParam p)).smul
    (hasFDerivAt_sphereParam p)).add_const z

lemma jacobian2_radialGraphParam {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0})
    (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ) (z : E3) (p : EuclideanSpace ℝ (Fin 2)) :
    jacobian2 (radialGraphParam ρ z) p =
      ρ (sphereParam p) * Real.sqrt (ρ (sphereParam p) ^ 2 +
        ‖gradient ρ (sphereParam p) - ⟪gradient ρ (sphereParam p), sphereParam p⟫_ℝ •
          sphereParam p‖ ^ 2) * |Real.sin (p 1)| := by
  set θ := sphereParam p with hθdef
  set g := gradient ρ θ with hgdef
  set r := ρ θ with hrdef
  have hr : 0 < r := hpos θ (norm_sphereParam p)
  have hg (w : E3) : fderiv ℝ ρ θ w = ⟪g, w⟫_ℝ := by
    rw [hgdef, gradient, InnerProductSpace.toDual_symm_apply]
  have happ (v : EuclideanSpace ℝ (Fin 2)) : radialGraphParamDeriv ρ p v =
      r • sphereParamDeriv p v + ⟪g, sphereParamDeriv p v⟫_ℝ • θ := by
    simp only [radialGraphParamDeriv, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, hg, ← hθdef, ← hrdef]
  obtain ⟨haθ, hbθ, hab, ha, hb, hP⟩ := sphereParam_frame p g
  rw [jacobian2, (hasFDerivAt_radialGraphParam hρ z p).fderiv, jacobian2Linear,
    gram_det_eq_norms, happ, happ, gram_radial (norm_sphereParam p) haθ hbθ hab ha hb hP,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hr]
  ring

/-- Only the values of `ρ` and its derivative on the compact unit sphere enter, so the
spherical parametrization of the radial graph is globally Lipschitz. -/
lemma exists_lipschitzWith_radialGraphParam {ρ : E3 → ℝ}
    (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0}) (z : E3) :
    ∃ K : ℝ≥0, LipschitzWith K (radialGraphParam ρ z) := by
  have hS : sphere (0 : E3) 1 ⊆ {y : E3 | y ≠ 0} := by
    intro y hy h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy
    exact zero_ne_one hy
  obtain ⟨C0, hC0⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn
    (hρ.continuousOn.mono hS)
  obtain ⟨C1, hC1⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn
    ((hρ.continuousOn_fderiv_of_isOpen isOpen_ne le_rfl).mono hS)
  have hθ (p : EuclideanSpace ℝ (Fin 2)) : sphereParam p ∈ sphere (0 : E3) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_sphereParam p)
  have hD (p : EuclideanSpace ℝ (Fin 2)) : ‖sphereParamDeriv p‖ ≤ 3 := by
    rw [← (hasFDerivAt_sphereParam p).fderiv]
    exact_mod_cast norm_fderiv_le_of_lipschitz ℝ lipschitzWith_sphereParam
  have hb (p : EuclideanSpace ℝ (Fin 2)) : ‖radialGraphParamDeriv ρ p‖ ≤ (C0 + C1) * 3 := by
    have h0 := hC0 _ (hθ p)
    have h1 := hC1 _ (hθ p)
    have hc := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ ρ (sphereParam p))
      (sphereParamDeriv p)
    have hDp := hD p
    calc
      _ ≤ ‖ρ (sphereParam p) • sphereParamDeriv p‖ +
          ‖((fderiv ℝ ρ (sphereParam p)).comp (sphereParamDeriv p)).smulRight
            (sphereParam p)‖ := norm_add_le _ _
      _ = ‖ρ (sphereParam p)‖ * ‖sphereParamDeriv p‖ +
          ‖(fderiv ℝ ρ (sphereParam p)).comp (sphereParamDeriv p)‖ * 1 := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_sphereParam]
      _ ≤ C0 * 3 + (C1 * 3) * 1 := by
        gcongr
        · exact (norm_nonneg _).trans h0
        · exact hc.trans (mul_le_mul h1 hDp (norm_nonneg _) ((norm_nonneg _).trans h1))
      _ = (C0 + C1) * 3 := by ring
  refine ⟨Real.toNNReal ((C0 + C1) * 3), lipschitzWith_of_nnnorm_fderiv_le
    (fun p => (hasFDerivAt_radialGraphParam hρ z p).differentiableAt) fun p => ?_⟩
  rw [(hasFDerivAt_radialGraphParam hρ z p).fderiv, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal']
  exact (hb p).trans (le_max_left _ _)

lemma radialGraphParam_injOn {ρ : E3 → ℝ} (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ) (z : E3) :
    InjOn (radialGraphParam ρ z) sphereParamDomain := by
  intro p hp q hq h
  have h' : ρ (sphereParam p) • sphereParam p = ρ (sphereParam q) • sphereParam q :=
    add_right_cancel h
  have hp0 := hpos _ (norm_sphereParam p)
  have hq0 := hpos _ (norm_sphereParam q)
  have hn := congrArg norm h'
  rw [norm_smul, norm_smul, norm_sphereParam, norm_sphereParam, mul_one, mul_one,
    Real.norm_of_nonneg hp0.le, Real.norm_of_nonneg hq0.le] at hn
  rw [hn] at h'
  exact sphereParam_injOn hp hq (smul_right_injective E3 hq0.ne' h')

lemma radialGraph_image_sphere_eq (ρ : E3 → ℝ) (z : E3) :
    (fun θ => ρ θ • θ + z) '' sphere (0 : E3) 1 =
      radialGraphParam ρ z '' sphereParamClosedDomain := by
  rw [← sphereParam_image_closedDomain, image_image]
  rfl

lemma measurable_radialGraph_areaFactor {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0}) :
    Measurable ρ ∧ Measurable (fun θ : E3 => ρ θ * Real.sqrt (ρ θ ^ 2 +
      ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫_ℝ • θ‖ ^ 2)) ∧
    ∀ {z : E3} {q : E3 → ℝ≥0∞}, Measurable q → Measurable (fun θ : E3 => q (ρ θ • θ + z) *
      ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
        ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫_ℝ • θ‖ ^ 2))) := by
  have hρm : Measurable ρ := measurable_of_continuousOn_compl_singleton 0 hρ.continuousOn
  have hgm : Measurable (gradient ρ) :=
    (InnerProductSpace.toDual ℝ E3).symm.continuous.measurable.comp (measurable_fderiv ℝ ρ)
  refine ⟨hρm, by fun_prop, fun hq => by fun_prop⟩

/-- Area formula for a `C¹` radial graph over the unit sphere, for nonnegative Borel
weights. -/
theorem radial_graph_lintegral {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0})
    (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ) (z : E3) {q : E3 → ℝ≥0∞} (hq : Measurable q) :
    ∫⁻ x in (fun θ => ρ θ • θ + z) '' Metric.sphere (0 : E3) 1, q x ∂(hausdorffMeasure2 3) =
      ∫⁻ θ in Metric.sphere (0 : E3) 1, q (ρ θ • θ + z) *
        ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
          ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫_ℝ • θ‖ ^ 2)) ∂(hausdorffMeasure2 3) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_radialGraphParam hρ z
  have hinj := radialGraphParam_injOn hpos z
  have hnull : hausdorffMeasure2 3
      (radialGraphParam ρ z '' (sphereParamClosedDomain \ sphereParamDomain)) = 0 :=
    hausdorffMeasure2_image_null hK (ae_le_set.mp sphereParamClosedDomain_ae_eq.le)
  have hsub : sphereParamDomain ⊆ sphereParamClosedDomain :=
    fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩
  have heq : sphereParamClosedDomain =
      sphereParamDomain ∪ (sphereParamClosedDomain \ sphereParamDomain) := by
    rw [union_sdiff_self, union_eq_self_of_subset_left hsub]
  have hmult : areaMultiplicity (radialGraphParam ρ z) sphereParamDomain
      (fun p => q (radialGraphParam ρ z p)) =
      (radialGraphParam ρ z '' sphereParamDomain).indicator q := by
    funext y
    by_cases hy : y ∈ radialGraphParam ρ z '' sphereParamDomain
    · rw [indicator_of_mem hy]
      obtain ⟨x, hx, rfl⟩ := hy
      exact areaMultiplicity_apply_of_injOn hinj _ hx
    · rw [indicator_of_notMem hy]
      exact areaMultiplicity_eq_zero_of_notMem_image _ hy
  have hhm := (measurable_radialGraph_areaFactor hρ).2.2 (z := z) hq
  rw [radialGraph_image_sphere_eq, heq, image_union,
    setLIntegral_congr (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hnull)),
    ← lintegral_indicator₀ (nullMeasurableSet_image_lipschitz_planar hK
      measurableSet_sphereParamDomain), ← hmult,
    ← area_formula_two_dimensional (q := fun p => q (radialGraphParam ρ z p)) hK
      measurableSet_sphereParamDomain (hq.comp hK.continuous.measurable),
    lintegral_sphere_eq_param 0 one_pos hhm]
  apply setLIntegral_congr_fun measurableSet_sphereParamDomain
  intro p _
  have hr := hpos _ (norm_sphereParam p)
  simp only [jacobian2_radialGraphParam hρ hpos z p, one_pow, one_mul, one_smul, zero_add,
    radialGraphParam]
  rw [ENNReal.ofReal_mul (mul_nonneg hr.le (Real.sqrt_nonneg _))]
  ring

/-- The Hausdorff area on a radial graph is the pushforward of the area density on the unit
sphere. -/
theorem radialGraph_map_withDensity {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0})
    (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ) (z : E3) :
    Measure.map (fun θ => ρ θ • θ + z)
      (((hausdorffMeasure2 3).restrict (sphere (0 : E3) 1)).withDensity fun θ =>
        ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
          ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫_ℝ • θ‖ ^ 2))) =
      (hausdorffMeasure2 3).restrict ((fun θ => ρ θ • θ + z) '' sphere (0 : E3) 1) := by
  obtain ⟨hρm, hJ, -⟩ := measurable_radialGraph_areaFactor hρ
  have hΦ : Measurable (fun θ : E3 => ρ θ • θ + z) := by fun_prop
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) hΦ,
    lintegral_withDensity_eq_lintegral_mul _ hJ.ennreal_ofReal
      (g := fun θ => A.indicator 1 (ρ θ • θ + z)) ((measurable_one.indicator hA).comp hΦ),
    radial_graph_lintegral hρ hpos z (measurable_one.indicator hA)]
  apply lintegral_congr
  intro θ
  simp only [Pi.mul_apply]
  ring

/-- Area formula for a `C¹` radial graph over the unit sphere, for Bochner integrals. No
integrability hypothesis is needed: both sides are integrals against the same measure. -/
theorem radial_graph_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0})
    (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ) (z : E3) {f : E3 → F}
    (hf : AEStronglyMeasurable f
      ((hausdorffMeasure2 3).restrict ((fun θ => ρ θ • θ + z) '' sphere (0 : E3) 1))) :
    ∫ x in (fun θ => ρ θ • θ + z) '' Metric.sphere (0 : E3) 1, f x ∂(hausdorffMeasure2 3) =
      ∫ θ in Metric.sphere (0 : E3) 1, (ρ θ * Real.sqrt (ρ θ ^ 2 +
          ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫_ℝ • θ‖ ^ 2)) • f (ρ θ • θ + z)
        ∂(hausdorffMeasure2 3) := by
  obtain ⟨hρm, hJ, -⟩ := measurable_radialGraph_areaFactor hρ
  have hΦ : Measurable (fun θ : E3 => ρ θ • θ + z) := by fun_prop
  rw [← radialGraph_map_withDensity hρ hpos z] at hf ⊢
  rw [integral_map hΦ.aemeasurable hf, integral_withDensity_eq_integral_toReal_smul
    hJ.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun isClosed_sphere.measurableSet
  intro θ hθ
  have hr := hpos θ (mem_sphere_zero_iff_norm.mp hθ)
  dsimp only
  rw [ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.sqrt_nonneg _))]

/-- The real-valued Bochner form of the radial-graph area formula. -/
theorem radial_graph_integral_real {ρ : E3 → ℝ} (hρ : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0})
    (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ) (z : E3) {f : E3 → ℝ} (hf : Measurable f) :
    ∫ x in (fun θ => ρ θ • θ + z) '' Metric.sphere (0 : E3) 1, f x ∂(hausdorffMeasure2 3) =
      ∫ θ in Metric.sphere (0 : E3) 1, f (ρ θ • θ + z) * (ρ θ * Real.sqrt (ρ θ ^ 2 +
          ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫_ℝ • θ‖ ^ 2)) ∂(hausdorffMeasure2 3) := by
  rw [radial_graph_integral hρ hpos z hf.aestronglyMeasurable]
  simp only [smul_eq_mul, mul_comm]

end CapacitaryK
end LiquidDrop
