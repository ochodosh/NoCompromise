import Mathlib
import NoCompromise.BV.SphericalSlicing
import NoCompromise.BV.ExactCuts
import NoCompromise.Energy.Scaling

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Blueprint `lem:slicing-integrals`, first identity (eq:slice-ell-integral): the length of the
set of levels ℓ with ν·y < ℓ < ν·x is the positive part of ν·(x − y). -/
theorem slice_length_integral (x y ν : EuclideanSpace ℝ (Fin 3)) :
    (∫ ℓ : ℝ, Set.indicator (Set.Ioo (inner ℝ ν y) (inner ℝ ν x)) (fun _ => (1 : ℝ)) ℓ) =
      max (inner ℝ ν (x - y)) 0 := by
  have hsub : inner ℝ ν (x - y) = inner ℝ ν x - inner ℝ ν y := by
    rw [inner_sub_right]
  rw [hsub]
  set a := inner ℝ ν y with ha
  set b := inner ℝ ν x with hb
  have hmeas : MeasurableSet (Ioo a b) := measurableSet_Ioo
  rw [integral_indicator hmeas]
  simp

theorem slice_length_lintegral (x y ν : EuclideanSpace ℝ (Fin 3)) :
    (∫⁻ ℓ : ℝ, Set.indicator (Set.Ioo (inner ℝ ν y) (inner ℝ ν x)) (fun _ => (1 : ENNReal)) ℓ) =
      ENNReal.ofReal (inner ℝ ν (x - y)) := by
  have hsub : inner ℝ ν (x - y) = inner ℝ ν x - inner ℝ ν y := by
    rw [inner_sub_right]
  rw [hsub]
  set a := inner ℝ ν y with ha
  set b := inner ℝ ν x with hb
  have hmeas : MeasurableSet (Ioo a b) := measurableSet_Ioo
  rw [lintegral_indicator hmeas]
  simp

end LiquidDrop

namespace LiquidDrop

open Metric

private def sliceSphereParameterEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => WithLp.toLp 2 ![p.1, p.2]
      invFun := fun x => (x 0, x 1)
      left_inv := by intro p; rcases p with ⟨x, y⟩; rfl
      right_inv := by intro x; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_add' := by intro p q; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_smul' := by intro r p; apply PiLp.ext; intro i; fin_cases i <;> rfl }

private lemma measurePreserving_sliceSphereParameterEquiv :
    MeasurePreserving sliceSphereParameterEquiv := by
  have h : MeasurePreserving sliceSphereParameterEquiv.symm := by
    have h := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
    convert h using 1 <;> rfl
  exact MeasurePreserving.symm sliceSphereParameterEquiv.symm.toHomeomorph.toMeasurableEquiv h

private lemma lintegral_sin_cos_colatitude :
    (∫⁻ t in Ioo (0 : ℝ) Real.pi,
      ENNReal.ofReal |Real.sin t| * ENNReal.ofReal (Real.cos t)) = 1 / 2 := by
  have hsplit :
      (∫⁻ t in Ioo (0 : ℝ) Real.pi,
        ENNReal.ofReal |Real.sin t| * ENNReal.ofReal (Real.cos t)) =
      ∫⁻ t in Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (Real.sin t * Real.cos t) := by
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)
    · have htpi : t ∈ Ioo (0 : ℝ) Real.pi :=
        ⟨ht.1, lt_trans ht.2 (by have := Real.pi_pos; linarith)⟩
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem htpi,
        abs_of_pos (Real.sin_pos_of_pos_of_lt_pi htpi.1 htpi.2),
        ENNReal.ofReal_mul (Real.sin_pos_of_pos_of_lt_pi htpi.1 htpi.2).le]
    · rw [Set.indicator_of_notMem ht]
      by_cases htpi : t ∈ Ioo (0 : ℝ) Real.pi
      · have hcos : Real.cos t ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt (fun h => ht ⟨htpi.1, h⟩))
            (by linarith [htpi.2, Real.pi_pos])
        rw [Set.indicator_of_mem htpi, ENNReal.ofReal_eq_zero.mpr hcos, mul_zero]
      · rw [Set.indicator_of_notMem htpi]
  rw [hsplit]
  have hi : IntegrableOn (fun t : ℝ => Real.sin t * Real.cos t) (Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.mul Real.continuous_cos).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have heq : (∫ t in Ioo (0 : ℝ) (Real.pi / 2), Real.sin t * Real.cos t) = 1 / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      integral_sin_mul_cos₁]
    norm_num
  calc
    _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) (Real.pi / 2),
        Real.sin t * Real.cos t) :=
      (ofReal_integral_eq_lintegral_ofReal hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_nonneg (Real.sin_pos_of_pos_of_lt_pi ht.1
          (lt_trans ht.2 (by have := Real.pi_pos; linarith))).le
          (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).le)).symm
    _ = 1 / 2 := by rw [heq, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num

private lemma sphere_lintegral_inner_pos_axis :
    (∫⁻ ν in sphere (0 : AmbientSpace) 1,
      ENNReal.ofReal (inner ℝ ν (EuclideanSpace.single 2 (1 : ℝ)))
        ∂hausdorffMeasure2 3) = ENNReal.ofReal Real.pi := by
  rw [lintegral_sphere_eq_param 0 (by norm_num : (0 : ℝ) < 1)
    (by fun_prop : Measurable (fun ν : AmbientSpace =>
      ENNReal.ofReal (inner ℝ ν (EuclideanSpace.single 2 (1 : ℝ)))))]
  simp only [zero_add, one_smul, EuclideanSpace.inner_single_right, sphereParam_two,
    one_mul, one_pow, starRingEnd_apply, star_trivial]
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal |Real.sin (p 1)| * ENNReal.ofReal (Real.cos (p 1))) := by fun_prop
  rw [← measurePreserving_sliceSphereParameterEquiv.setLIntegral_comp_preimage
    measurableSet_sphereParamDomain hm]
  change (∫⁻ p : ℝ × ℝ in Ioo (-Real.pi) Real.pi ×ˢ Ioo 0 Real.pi,
    ENNReal.ofReal |Real.sin p.2| * ENNReal.ofReal (Real.cos p.2)
      ∂(volume.prod volume)) = _
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_sin_cos_colatitude, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioo, sub_neg_eq_add]
  rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

/-- The positive part of a linear functional has spherical integral `π‖a‖`. -/
theorem sphere_lintegral_inner_pos (a : AmbientSpace) :
    (∫⁻ ν in sphere (0 : AmbientSpace) 1, ENNReal.ofReal (inner ℝ ν a)
      ∂hausdorffMeasure2 3) = ENNReal.ofReal (Real.pi * ‖a‖) := by
  by_cases ha : a = 0
  · subst a
    simp
  let u : AmbientSpace := EuclideanSpace.single 2 (1 : ℝ)
  have hu : ‖u‖ = 1 := by simp [u, PiLp.norm_single]
  let e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace :=
    (ℝ ∙ (‖a‖ • u - a))ᗮ.reflection
  have he : e (‖a‖ • u) = a := by
    apply Submodule.reflection_sub
    simp [norm_smul, hu]
  have hs : e ⁻¹' sphere (0 : AmbientSpace) 1 = sphere 0 1 := by
    ext x
    simp only [mem_preimage, mem_sphere_zero_iff_norm, e.norm_map]
  have hg : Measurable (fun ν : AmbientSpace => ENNReal.ofReal (inner ℝ ν a)) := by
    fun_prop
  have hmp : MeasurePreserving e (hausdorffMeasure2 3) (hausdorffMeasure2 3) := by
    convert (e.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure 2) using 1 <;>
      rfl
  calc
    (∫⁻ ν in sphere (0 : AmbientSpace) 1, ENNReal.ofReal (inner ℝ ν a)
        ∂hausdorffMeasure2 3) =
      ∫⁻ ν in sphere (0 : AmbientSpace) 1, ENNReal.ofReal (inner ℝ (e ν) a)
        ∂hausdorffMeasure2 3 := by
      rw [← hmp.setLIntegral_comp_preimage isClosed_sphere.measurableSet hg, hs]
    _ = ∫⁻ ν in sphere (0 : AmbientSpace) 1,
        ENNReal.ofReal ‖a‖ * ENNReal.ofReal (inner ℝ ν u) ∂hausdorffMeasure2 3 := by
      apply setLIntegral_congr_fun isClosed_sphere.measurableSet
      intro ν _
      have hinner : inner ℝ (e ν) a = ‖a‖ * inner ℝ ν u := by
        calc
          _ = inner ℝ (e ν) (e (‖a‖ • u)) := by rw [he]
          _ = inner ℝ ν (‖a‖ • u) := e.inner_map_map ν (‖a‖ • u)
          _ = _ := real_inner_smul_right ν u ‖a‖
      change ENNReal.ofReal (inner ℝ (e ν) a) =
        ENNReal.ofReal ‖a‖ * ENNReal.ofReal (inner ℝ ν u)
      rw [hinner, ENNReal.ofReal_mul (norm_nonneg a)]
    _ = ENNReal.ofReal ‖a‖ *
        (∫⁻ ν in sphere (0 : AmbientSpace) 1,
          ENNReal.ofReal (inner ℝ ν u) ∂hausdorffMeasure2 3) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = ENNReal.ofReal (Real.pi * ‖a‖) := by
      rw [show (∫⁻ ν in sphere (0 : AmbientSpace) 1,
          ENNReal.ofReal (inner ℝ ν u) ∂hausdorffMeasure2 3) =
          ENNReal.ofReal Real.pi by simpa only [u] using sphere_lintegral_inner_pos_axis]
      rw [← ENNReal.ofReal_mul (norm_nonneg a)]
      congr 1
      ring

/-- The positive inner product has mean one quarter of the norm on the unit sphere. -/
theorem slice_sphere_average (a : AmbientSpace) (ha : a ≠ 0) :
    (4 * Real.pi)⁻¹ *
      ∫ ν in sphere (0 : AmbientSpace) 1,
        max (inner ℝ ν a) 0 / ‖a‖ ∂(hausdorffMeasure2 3) = 1 / 4 := by
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hm : Measurable (fun ν : AmbientSpace => max (inner ℝ ν a) 0) := by fun_prop
  have hfin : hausdorffMeasure2 3 (sphere (0 : AmbientSpace) 1) ≠ ∞ := by
    rw [hausdorffMeasure2_unit_sphere]
    exact ENNReal.ofReal_ne_top
  have hf : IntegrableOn (fun ν : AmbientSpace => max (inner ℝ ν a) 0)
      (sphere (0 : AmbientSpace) 1) (hausdorffMeasure2 3) := by
    refine Measure.integrableOn_of_bounded (M := ‖a‖) hfin hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with ν hν
    have hνnorm : ‖ν‖ = 1 := mem_sphere_zero_iff_norm.mp hν
    have hinner : inner ℝ ν a ≤ ‖a‖ := by
      simpa only [hνnorm, one_mul] using real_inner_le_norm ν a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (inner ℝ ν a) 0)]
    exact max_le hinner (norm_nonneg a)
  have hnonneg : 0 ≤ ∫ ν in sphere (0 : AmbientSpace) 1,
      max (inner ℝ ν a) 0 ∂(hausdorffMeasure2 3) := by
    apply integral_nonneg_of_ae
    filter_upwards with ν
    exact le_max_right _ _
  have hreal : (∫ ν in sphere (0 : AmbientSpace) 1,
      max (inner ℝ ν a) 0 ∂(hausdorffMeasure2 3)) = Real.pi * ‖a‖ := by
    apply (ENNReal.ofReal_eq_ofReal_iff hnonneg (mul_nonneg Real.pi_pos.le (norm_nonneg a))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hf (by
      filter_upwards with ν
      exact le_max_right _ _)]
    simpa using sphere_lintegral_inner_pos a
  rw [integral_div, hreal]
  field_simp [hnorm.ne', Real.pi_ne_zero]

/-! ## Blueprint `prop:V-le-8` -/

/-- Cavalieri along the first coordinate, over the whole line. -/
private lemma coordinate_plane_slicing_univ {A : Set AmbientSpace} (hA : MeasurableSet A) :
    ∫⁻ t, hausdorffMeasure2 3 (A ∩ {x | x 0 = t}) = volume A := by
  let S : Set (ℝ × EuclideanSpace ℝ (Fin 2)) := slicingCoordinates.symm ⁻¹' A
  have hS : MeasurableSet S := hA.preimage slicingCoordinates.symm.measurable
  have heq : slicingCoordinates ⁻¹' S = A := by
    ext x
    simp [S]
  rw [← heq, measurePreserving_slicingCoordinates.measure_preimage hS.nullMeasurableSet]
  change _ = (volume.prod volume) S
  rw [Measure.prod_apply hS]
  apply lintegral_congr
  intro t
  rw [hausdorffMeasure2_coordinate_slice]
  congr 1

/-- Cavalieri's principle (supporting lemma of `prop:V-le-8`): the normalized Hausdorff areas of
the plane sections `A ∩ {ν·x = ℓ}` of a Borel set integrate to its volume, for every unit `ν`. -/
theorem lintegral_plane_sections_eq_volume {A : Set AmbientSpace} (hA : MeasurableSet A)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∫⁻ ℓ, hausdorffMeasure2 3 (A ∩ {x | inner ℝ ν x = ℓ}) = volume A := by
  have hcomm : ∀ ℓ : ℝ, A ∩ {x | inner ℝ ν x = ℓ} = A ∩ {x | inner ℝ x ν = ℓ} := by
    intro ℓ
    ext x
    simp [real_inner_comm]
  simp_rw [hcomm]
  obtain ⟨e, he⟩ := exists_slicing_isometry hν
  simp_rw [hausdorffMeasure2_plane_slice_isometry e he]
  rw [coordinate_plane_slicing_univ (hA.preimage e.continuous.measurable)]
  exact e.measurePreserving.measure_preimage hA.nullMeasurableSet


/-- The diagonal of `Ω × Ω` is null for the product of restricted volumes. -/
private lemma prod_restrict_diagonal_null (Ω : Set AmbientSpace) :
    ((volume.restrict Ω).prod (volume.restrict Ω)) {p : AmbientSpace × AmbientSpace | p.1 = p.2}
      = 0 := by
  have hmeas : MeasurableSet {p : AmbientSpace × AmbientSpace | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  rw [Measure.prod_apply hmeas]
  have : ∀ x : AmbientSpace, Prod.mk x ⁻¹' {p : AmbientSpace × AmbientSpace | p.1 = p.2} = {x} := by
    intro x
    ext y
    simp [eq_comm]
  simp_rw [this]
  simp [Measure.restrict_apply]

/-- Blueprint `prop:V-le-8`, with `eq:slice-coulomb` of `lem:slicing-inequality` as the named
hypothesis `hslice` (the sets `Ω ∩ {ℓ < ν·x}` and `Ω ∩ {ν·y < ℓ}` are `Ω⁺_{ν,ℓ}`, `Ω⁻_{ν,ℓ}`).
The Cavalieri identity is `lintegral_plane_sections_eq_volume` and the sphere average is
`sphere_lintegral_inner_pos`, so `hslice` is the only external input. -/
theorem volume_le_eight_of_slicing_inequality (Ω : Set AmbientSpace) (hΩ : MeasurableSet Ω)
    (hfin : volume Ω ≠ ∞)
    (hslice : ∀ ν ∈ sphere (0 : AmbientSpace) 1, ∀ᵐ ℓ : ℝ,
      (∫⁻ x in Ω ∩ {x | ℓ < inner ℝ ν x}, ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ},
          ENNReal.ofReal (‖x - y‖⁻¹)) ≤ 2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ})) :
    (volume Ω).toReal ≤ 8 := by
  have hsph := sphere_lintegral_inner_pos
  set μ : Measure AmbientSpace := volume.restrict Ω with hμ
  set k : AmbientSpace × AmbientSpace → ℝ≥0∞ := fun p => ENNReal.ofReal (‖p.1 - p.2‖⁻¹) with hk
  have hkm : Measurable k :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.inv)
  -- Step A: for each unit `ν`, integrate the slicing inequality in `ℓ` (Tonelli + Cavalieri).
  have stepA : ∀ ν ∈ sphere (0 : AmbientSpace) 1,
      ∫⁻ p, k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) ∂(μ.prod μ) ≤ 2 * volume Ω := by
    intro ν hν
    have hν1 : ‖ν‖ = 1 := mem_sphere_zero_iff_norm.mp hν
    let T : Set (ℝ × (AmbientSpace × AmbientSpace)) :=
      {q | inner ℝ ν q.2.2 < q.1 ∧ q.1 < inner ℝ ν q.2.1}
    have hT : MeasurableSet T := by
      have ha : Measurable fun q : ℝ × (AmbientSpace × AmbientSpace) => inner ℝ ν q.2.2 := by
        fun_prop
      have hb : Measurable fun q : ℝ × (AmbientSpace × AmbientSpace) => inner ℝ ν q.2.1 := by
        fun_prop
      exact (measurableSet_lt ha measurable_fst).inter (measurableSet_lt measurable_fst hb)
    let H : ℝ → AmbientSpace × AmbientSpace → ℝ≥0∞ := fun ℓ p =>
      T.indicator (fun q => k q.2) (ℓ, p)
    have hHm : Measurable (Function.uncurry H) := (hkm.comp measurable_snd).indicator hT
    have h1 : ∀ ℓ : ℝ, MeasurableSet {x : AmbientSpace | ℓ < inner ℝ ν x} := fun ℓ =>
      measurableSet_lt measurable_const (by fun_prop)
    have h2 : ∀ ℓ : ℝ, MeasurableSet {y : AmbientSpace | inner ℝ ν y < ℓ} := fun ℓ =>
      measurableSet_lt (by fun_prop) measurable_const
    have hsec : ∀ ℓ : ℝ, ∫⁻ p, H ℓ p ∂(μ.prod μ) =
        ∫⁻ x in Ω ∩ {x | ℓ < inner ℝ ν x}, ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ},
          ENNReal.ofReal (‖x - y‖⁻¹) := by
      intro ℓ
      rw [lintegral_prod (H ℓ) (hHm.comp measurable_prodMk_left).aemeasurable,
        Set.inter_comm Ω {x | ℓ < inner ℝ ν x}, ← setLIntegral_indicator (h1 ℓ)]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ {x : AmbientSpace | ℓ < inner ℝ ν x}
      · rw [indicator_of_mem hx]
        show ∫⁻ y, H ℓ (x, y) ∂μ =
          ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ}, ENNReal.ofReal (‖x - y‖⁻¹)
        rw [Set.inter_comm Ω {y | inner ℝ ν y < ℓ}, ← setLIntegral_indicator (h2 ℓ)]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ {y : AmbientSpace | inner ℝ ν y < ℓ}
        · rw [indicator_of_mem hy]
          exact indicator_of_mem (show ((ℓ, (x, y)) : ℝ × (AmbientSpace × AmbientSpace)) ∈ T
            from ⟨hy, hx⟩) _
        · rw [indicator_of_notMem hy]
          exact indicator_of_notMem (show ((ℓ, (x, y)) : ℝ × (AmbientSpace × AmbientSpace)) ∉ T
            from fun h => hy h.1) _
      · rw [indicator_of_notMem hx]
        have hz : ∀ y, H ℓ (x, y) = 0 := fun y =>
          indicator_of_notMem (show ((ℓ, (x, y)) : ℝ × (AmbientSpace × AmbientSpace)) ∉ T
            from fun h => hx h.2) _
        simp [hz]
    have hswap : ∫⁻ ℓ, (∫⁻ p, H ℓ p ∂(μ.prod μ)) = ∫⁻ p, (∫⁻ ℓ, H ℓ p) ∂(μ.prod μ) :=
      lintegral_lintegral_swap hHm.aemeasurable
    have hinner : ∀ p : AmbientSpace × AmbientSpace,
        ∫⁻ ℓ, H ℓ p = k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) := by
      intro p
      have : (fun ℓ => H ℓ p) =
          (Ioo (inner ℝ ν p.2) (inner ℝ ν p.1)).indicator (fun _ => k p) := by
        funext ℓ
        by_cases hl : ℓ ∈ Ioo (inner ℝ ν p.2) (inner ℝ ν p.1)
        · rw [indicator_of_mem hl]
          exact indicator_of_mem (show ((ℓ, p) : ℝ × (AmbientSpace × AmbientSpace)) ∈ T
            from hl) _
        · rw [indicator_of_notMem hl]
          exact indicator_of_notMem (show ((ℓ, p) : ℝ × (AmbientSpace × AmbientSpace)) ∉ T
            from hl) _
      rw [this, lintegral_indicator measurableSet_Ioo, setLIntegral_const, Real.volume_Ioo,
        inner_sub_right]
    have hcav := lintegral_plane_sections_eq_volume hΩ hν1
    have hmeas_sec : Measurable fun ℓ : ℝ => hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) := by
      have hcomm : (fun ℓ : ℝ => hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ})) =
          fun ℓ => hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ x ν = ℓ}) := by
        funext ℓ
        congr 1
        ext x
        simp [real_inner_comm]
      rw [hcomm]
      exact measurable_plane_sections hΩ hν1
    calc ∫⁻ p, k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) ∂(μ.prod μ)
        = ∫⁻ p, (∫⁻ ℓ, H ℓ p) ∂(μ.prod μ) := by simp_rw [hinner]
      _ = ∫⁻ ℓ, (∫⁻ p, H ℓ p ∂(μ.prod μ)) := hswap.symm
      _ = ∫⁻ ℓ, ∫⁻ x in Ω ∩ {x | ℓ < inner ℝ ν x}, ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ},
            ENNReal.ofReal (‖x - y‖⁻¹) := by simp_rw [hsec]
      _ ≤ ∫⁻ ℓ, 2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) :=
            lintegral_mono_ae (hslice ν hν)
      _ = 2 * volume Ω := by rw [lintegral_const_mul _ hmeas_sec, hcav]
  -- Step B: average over the unit sphere (Tonelli + the sphere average).
  set σ : Measure AmbientSpace := (hausdorffMeasure2 3).restrict (sphere (0 : AmbientSpace) 1)
    with hσ
  have : IsFiniteMeasure σ := by
    refine ⟨?_⟩
    rw [hσ, Measure.restrict_apply_univ, hausdorffMeasure2_unit_sphere]
    exact ENNReal.ofReal_lt_top
  have hFm : Measurable (Function.uncurry
      fun (ν : AmbientSpace) (p : AmbientSpace × AmbientSpace) =>
        k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2))) := by
    apply Measurable.mul (hkm.comp measurable_snd)
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hupper : ∫⁻ ν, ∫⁻ p, k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) ∂(μ.prod μ) ∂σ ≤
      2 * volume Ω * ENNReal.ofReal (4 * Real.pi) := by
    calc ∫⁻ ν, ∫⁻ p, k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) ∂(μ.prod μ) ∂σ
        ≤ ∫⁻ _ν, 2 * volume Ω ∂σ := by
          apply lintegral_mono_ae
          rw [hσ, ae_restrict_iff' isClosed_sphere.measurableSet]
          exact Eventually.of_forall stepA
      _ = 2 * volume Ω * ENNReal.ofReal (4 * Real.pi) := by
          rw [lintegral_const, hσ, Measure.restrict_apply_univ, hausdorffMeasure2_unit_sphere]
  have hae : ∀ᵐ p ∂(μ.prod μ), ENNReal.ofReal Real.pi =
      ∫⁻ ν, k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) ∂σ := by
    have hnull := prod_restrict_diagonal_null Ω
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
    have hn : ‖p.1 - p.2‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    rw [lintegral_const_mul (k p)
      (f := fun ν : AmbientSpace => ENNReal.ofReal (inner ℝ ν (p.1 - p.2)))
      (ENNReal.measurable_ofReal.comp (by fun_prop)), hσ, hsph]
    change ENNReal.ofReal Real.pi =
      ENNReal.ofReal (‖p.1 - p.2‖⁻¹) * ENNReal.ofReal (Real.pi * ‖p.1 - p.2‖)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _)), mul_comm Real.pi,
      inv_mul_cancel_left₀ hn]
  have hlower : ∫⁻ ν, ∫⁻ p, k p * ENNReal.ofReal (inner ℝ ν (p.1 - p.2)) ∂(μ.prod μ) ∂σ =
      ENNReal.ofReal Real.pi * (volume Ω * volume Ω) := by
    rw [lintegral_lintegral_swap hFm.aemeasurable, ← lintegral_congr_ae hae, lintegral_const,
      ← univ_prod_univ, Measure.prod_prod, hμ, Measure.restrict_apply_univ]
  have hvol : volume Ω = ENNReal.ofReal (volume Ω).toReal := (ENNReal.ofReal_toReal hfin).symm
  set m := (volume Ω).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hkey := hlower.symm.le.trans hupper
  rw [hvol, ← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_mul Real.pi_pos.le,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * m),
    ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 2 * m * (4 * Real.pi))] at hkey
  by_contra h
  push Not at h
  have hπ := Real.pi_pos
  nlinarith [mul_pos (mul_pos hπ (by linarith : (0 : ℝ) < m)) (by linarith : (0 : ℝ) < m - 8)]

end LiquidDrop

namespace LiquidDrop

open scoped symmDiff

private lemma slicing_section_measurable {E : Set AmbientSpace} (hE : MeasurableSet E)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    Measurable (fun ℓ : ℝ => hausdorffMeasure2 3 (E ∩ {x | inner ℝ ν x = ℓ})) := by
  simpa only [real_inner_comm ν] using measurable_plane_sections hE hν

private lemma slicing_density_sections {E : Set AmbientSpace} (hE : MeasurableSet E)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ ℓ : ℝ, hausdorffMeasure2 3 (densityOne E ∩ {x | inner ℝ ν x = ℓ}) =
      hausdorffMeasure2 3 (E ∩ {x | inner ℝ ν x = ℓ}) := by
  have hm := (measurableSet_densityOne hE.nullMeasurableSet).symmDiff hE
  have hz : volume (densityOne E ∆ E) = 0 :=
    measure_symmDiff_eq_zero_iff.mpr (densityOne_ae_eq (by norm_num) hE.nullMeasurableSet)
  have hi := lintegral_plane_sections_eq_volume hm hν
  rw [hz, lintegral_eq_zero_iff (slicing_section_measurable hm hν)] at hi
  filter_upwards [hi] with ℓ hℓ
  apply measure_congr
  apply measure_symmDiff_eq_zero_iff.mp
  change hausdorffMeasure2 3 ((densityOne E ∆ E) ∩ {x | inner ℝ ν x = ℓ}) = 0 at hℓ
  convert hℓ using 1
  congr 1
  ext x
  simp only [mem_symmDiff, mem_inter_iff, mem_ofPred_eq]
  tauto

private lemma slicing_perimeter_bulk {E : Set AmbientSpace} (hE : MeasurableSet E)
    (hp : perimeter E < ∞) (ν : AmbientSpace) :
    ∀ᵐ ℓ : ℝ, perimeterIn E {x | ℓ < inner ℝ ν x} +
      perimeterIn E {x | inner ℝ ν x < ℓ} = perimeter E := by
  obtain ⟨μ, hμ⟩ := exists_perimeter_measure hE.nullMeasurableSet
  have hu : μ univ = perimeter E := by
    rw [← hμ univ isOpen_univ]
    exact perimeterN_eq_perimeter E hE.nullMeasurableSet
  let : IsFiniteMeasure μ := ⟨by rw [hu]; exact hp⟩
  have hc := Measure.countable_meas_level_set_pos (μ := μ)
    (show Measurable (fun x : AmbientSpace => inner ℝ ν x) by fun_prop)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hc.measure_zero (μ := volume))] with ℓ hℓ
  have hz : μ {x : AmbientSpace | inner ℝ ν x = ℓ} = 0 :=
    le_antisymm (not_lt.mp hℓ) zero_le
  have hpos : IsOpen {x : AmbientSpace | ℓ < inner ℝ ν x} :=
    isOpen_lt continuous_const (by fun_prop)
  have hneg : IsOpen {x : AmbientSpace | inner ℝ ν x < ℓ} :=
    isOpen_lt (by fun_prop) continuous_const
  rw [hμ _ hpos, hμ _ hneg, ← measure_union (by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (lt_asymm (show ℓ < inner ℝ ν x from hx)
      (show inner ℝ ν x < ℓ from hy))) hneg.measurableSet]
  have heq : {x : AmbientSpace | ℓ < inner ℝ ν x} ∪ {x | inner ℝ ν x < ℓ} =
      {x | inner ℝ ν x = ℓ}ᶜ := by
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff]
    exact lt_or_lt_iff_ne.trans ne_comm
  rw [heq, measure_compl (measurableSet_eq_fun (by fun_prop) measurable_const)
    (by rw [hz]; exact ENNReal.zero_ne_top), hz, tsub_zero, hu]

/-- The perimeter identity in blueprint `lem:slicing-inequality`, for a Borel set
of finite perimeter. -/
theorem ae_slicing_perimeter {E : Set AmbientSpace} (hE : MeasurableSet E)
    (hp : perimeter E < ∞) {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ ℓ : ℝ,
      perimeter (E ∩ {x | ℓ < inner ℝ ν x}) + perimeter (E ∩ {x | inner ℝ ν x < ℓ}) =
        perimeter E + 2 * hausdorffMeasure2 3 (E ∩ {x | inner ℝ ν x = ℓ}) := by
  have hlocal : HasLocallyFinitePerimeter E := by
    intro A _ _
    have h := variation_mono (f := E.indicator (fun _ => (1 : ℝ)))
      MeasurableSet.univ (subset_univ A)
    change perimeterIn E A ≤ perimeterN E at h
    rw [perimeterN_eq_perimeter E hE.nullMeasurableSet] at h
    exact h.trans_lt hp
  filter_upwards [(exact_cut_identities hlocal hE.nullMeasurableSet).2 ν hν,
    slicing_density_sections hE hν, slicing_perimeter_bulk hE hp ν] with ℓ hcut hden hbulk
  have he : E \ {x | inner ℝ ν x < ℓ} =ᵐ[volume]
      (E ∩ {x | ℓ < inner ℝ ν x} : Set AmbientSpace) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_plane_eq_zero hν ℓ)] with x hx
    apply propext
    change (x ∈ E ∧ ¬inner ℝ ν x < ℓ) ↔ (x ∈ E ∧ ℓ < inner ℝ ν x)
    have hne : inner ℝ ν x ≠ ℓ := hx
    exact and_congr Iff.rfl ⟨fun h => lt_of_le_of_ne (not_lt.mp h) hne.symm,
      fun h => not_lt.mpr h.le⟩
  have hpplus : perimeter (E ∩ {x | ℓ < inner ℝ ν x}) =
      perimeterIn E {x | ℓ < inner ℝ ν x} +
        hausdorffMeasure2 3 (densityOne E ∩ {x | inner ℝ ν x = ℓ}) :=
    (perimeter_congr_ae he).symm.trans hcut.2
  rw [hpplus, hcut.1, hden, two_mul, ← hbulk]
  ac_rfl


private lemma slicing_energy_union {E F : Set AmbientSpace}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hs : Metric.AreSeparated E F) :
    energy (E ∪ F) = energy E + energy F + coulombInteraction E F := by
  have hp : perimeter (E ∪ F) = perimeter E + perimeter F := by
    simpa only [perimeterN_eq_perimeter _ (hE.union hF).nullMeasurableSet,
      perimeterN_eq_perimeter _ hE.nullMeasurableSet,
      perimeterN_eq_perimeter _ hF.nullMeasurableSet] using
      perimeterN_union_of_areSeparated hE.nullMeasurableSet hF.nullMeasurableSet hs
  rw [energy, hp, coulombEnergy_union E F hF.nullMeasurableSet hs.disjoint]
  simp only [energy]
  ac_rfl

private lemma slicing_energy_le_sum {V : ℝ} {Ω E F : Set AmbientSpace}
    (hmin : IsFixedVolumeMinimizer V Ω) (hbdd : Bornology.IsBounded Ω)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω)
    (hd : Disjoint E F) (hu : (E ∪ F : Set AmbientSpace) =ᵐ[volume] Ω)
    (hpE : perimeter E < ∞) (hpF : perimeter F < ∞)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    energy Ω ≤ energy E + energy F := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : AmbientSpace) |>.mp hbdd
  have hvΩ : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have hvE : volume E < ∞ := (measure_mono hEΩ).trans_lt hvΩ
  have hvF : volume F < ∞ := (measure_mono hFΩ).trans_lt hvΩ
  have heE : energy E ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hpE.ne,
    (coulombEnergy_lt_top E hvE).ne⟩
  have heF : energy F ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hpF.ne,
    (coulombEnergy_lt_top F hvF).ne⟩
  have heΩ : energy Ω ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hmin.2.2.1.ne,
    (coulombEnergy_lt_top Ω hvΩ).ne⟩
  let Ft (t : ℝ) := (fun y : AmbientSpace => t • ν + y) '' F
  have hm (t : ℝ) : MeasurableSet (Ft t) :=
    (Homeomorph.addLeft (t • ν)).toMeasurableEquiv.measurableSet_image.mpr hF
  have hv (t : ℝ) : volume (Ft t) = volume F := volume_image_translate F (t • ν)
  have he (t : ℝ) : energy (Ft t) = energy F := energy_translate hF.nullMeasurableSet _
  have hs (t : ℝ) (ht : 2 * R + 1 < t) : Metric.AreSeparated E (Ft t) := by
    refine ⟨ENNReal.ofReal 1, by norm_num, ?_⟩
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hxR : ‖x‖ < R := by simpa using hR (hEΩ hx)
    have hzR : ‖z‖ < R := by simpa using hR (hFΩ hz)
    have ht0 : 0 ≤ t := by linarith [norm_nonneg x]
    have hn : ‖t • ν‖ = t := by
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hid : t • ν = (x - z) - (x - (t • ν + z)) := by abel
    have htri := norm_sub_le (x - z) (x - (t • ν + z))
    rw [← hid, hn] at htri
    have hdist : 1 ≤ dist x (t • ν + z) := by
      rw [dist_eq_norm]
      linarith [norm_sub_le x z]
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  have hi : Tendsto (fun t : ℝ => (coulombInteraction E (Ft t)).toReal) atTop (𝓝 0) := by
    simpa only [Ft, add_comm] using
      tendsto_coulombInteraction_translate (hEΩ.trans hR) (hFΩ.trans hR) hν
  have hlim : (energy Ω).toReal ≤ (energy E).toReal + (energy F).toReal := by
    have htend : Tendsto (fun t : ℝ =>
        ((energy E).toReal + (energy F).toReal) + (coulombInteraction E (Ft t)).toReal)
        atTop (𝓝 (((energy E).toReal + (energy F).toReal) + 0)) :=
      tendsto_const_nhds.add hi
    have hbound : ∀ᶠ t : ℝ in atTop, (energy Ω).toReal ≤
        ((energy E).toReal + (energy F).toReal) + (coulombInteraction E (Ft t)).toReal := by
      filter_upwards [eventually_gt_atTop (2 * R + 1)] with t ht
      have hvunion : volume (E ∪ Ft t) = ENNReal.ofReal V := by
        rw [measure_union (hs t ht).disjoint (hm t), hv t,
          ← measure_union hd hF, measure_congr hu, hmin.2.1]
      have h := hmin.2.2.2 (E ∪ Ft t) (hE.union (hm t)) hvunion
      rw [slicing_energy_union hE (hm t) (hs t ht), he t] at h
      have hc : coulombInteraction E (Ft t) ≠ ∞ :=
        (coulombInteraction_lt_top E (Ft t) hvE (by rw [hv t]; exact hvF)).ne
      have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨heE, heF⟩, hc⟩) h
      simpa only [ENNReal.toReal_add heE heF,
        ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨heE, heF⟩) hc] using hh
    simpa only [add_zero] using ge_of_tendsto htend hbound
  apply (ENNReal.toReal_le_toReal heΩ (ENNReal.add_ne_top.mpr ⟨heE, heF⟩)).mp
  simpa only [ENNReal.toReal_add heE heF] using hlim


/-- Blueprint `lem:slicing-inequality`: exact perimeter splitting and the
Coulomb bound obtained by translating the two pieces apart. -/
theorem slicing_inequality {V : ℝ} {Ω : Set AmbientSpace}
    (hmin : IsFixedVolumeMinimizer V Ω) (hbdd : Bornology.IsBounded Ω)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ ℓ : ℝ,
      perimeter (Ω ∩ {x | ℓ < inner ℝ ν x}) + perimeter (Ω ∩ {x | inner ℝ ν x < ℓ}) =
          perimeter Ω + 2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) ∧
      (∫⁻ x in Ω ∩ {x | ℓ < inner ℝ ν x}, ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ},
          ENNReal.ofReal (‖x - y‖⁻¹)) ≤
        2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) := by
  have hvΩ : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have hsec := ae_lt_top (slicing_section_measurable hmin.1 hν)
    (show (∫⁻ ℓ, hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ})) ≠ ∞ by
      rw [lintegral_plane_sections_eq_volume hmin.1 hν]
      exact hvΩ.ne)
  filter_upwards [ae_slicing_perimeter hmin.1 hmin.2.2.1 hν, hsec] with ℓ hp harea
  refine ⟨hp, ?_⟩
  let E := Ω ∩ {x | ℓ < inner ℝ ν x}
  let F := Ω ∩ {x | inner ℝ ν x < ℓ}
  have hE : MeasurableSet E := hmin.1.inter (measurableSet_lt measurable_const (by fun_prop))
  have hF : MeasurableSet F := hmin.1.inter (measurableSet_lt (by fun_prop) measurable_const)
  have hEΩ : E ⊆ Ω := inter_subset_left
  have hFΩ : F ⊆ Ω := inter_subset_left
  have hd : Disjoint E F := Set.disjoint_left.mpr fun x hx hy =>
    lt_asymm (show ℓ < inner ℝ ν x from hx.2) (show inner ℝ ν x < ℓ from hy.2)
  have hu : (E ∪ F : Set AmbientSpace) =ᵐ[volume] Ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_plane_eq_zero hν ℓ)] with x hx
    apply propext
    change ((x ∈ Ω ∧ ℓ < inner ℝ ν x) ∨ (x ∈ Ω ∧ inner ℝ ν x < ℓ)) ↔ x ∈ Ω
    have hne : inner ℝ ν x ≠ ℓ := hx
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr ⟨h, hlt⟩
      · exact Or.inl ⟨h, hgt⟩
  have hpsum : perimeter E + perimeter F < ∞ := by
    rw [hp]
    exact ENNReal.add_lt_top.mpr ⟨hmin.2.2.1, ENNReal.mul_lt_top (by norm_num) harea⟩
  have hcomp := slicing_energy_le_sum hmin hbdd hE hF hEΩ hFΩ hd hu
    (ENNReal.add_lt_top.mp hpsum).1 (ENNReal.add_lt_top.mp hpsum).2 hν
  have hc : coulombEnergy Ω = coulombEnergy E + coulombEnergy F + coulombInteraction E F := by
    rw [← coulombEnergy_congr_ae hu, coulombEnergy_union E F hF.nullMeasurableSet hd]
  have hD : coulombEnergy E + coulombEnergy F ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨(coulombEnergy_lt_top E ((measure_mono hEΩ).trans_lt hvΩ)).ne,
      (coulombEnergy_lt_top F ((measure_mono hFΩ).trans_lt hvΩ)).ne⟩
  have hi : coulombInteraction E F ≤
      2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) := by
    apply (ENNReal.add_le_add_iff_left hmin.2.2.1.ne).mp
    rw [← hp]
    apply (ENNReal.add_le_add_iff_right hD).mp
    calc
      perimeter Ω + coulombInteraction E F + (coulombEnergy E + coulombEnergy F) =
          energy Ω := by rw [energy, hc]; ac_rfl
      _ ≤ energy E + energy F := hcomp
      _ = perimeter E + perimeter F + (coulombEnergy E + coulombEnergy F) := by
        simp only [energy]; ac_rfl
  have hk : coulombInteraction E F =
      ∫⁻ x in E, ∫⁻ y in F, ENNReal.ofReal (‖x - y‖⁻¹) := by
    rw [coulombInteraction_eq_lintegral_potential]
    apply lintegral_congr
    intro x
    exact lintegral_congr_ae (ae_restrict_of_ae (coulombKernel_ae_eq_ofReal x))
  rwa [hk] at hi

/-- Blueprint `prop:V-le-8` for a fixed-volume minimizer with a bounded representative. -/
theorem le_eight_of_isFixedVolumeMinimizer {V : ℝ} {Ω : Set AmbientSpace}
    (hmin : IsFixedVolumeMinimizer V Ω) (hbdd : Bornology.IsBounded Ω) : V ≤ 8 := by
  by_cases hV : 0 ≤ V
  · have h := volume_le_eight_of_slicing_inequality Ω hmin.1
      (by rw [hmin.2.1]; exact ENNReal.ofReal_ne_top) (fun ν hν =>
        (slicing_inequality hmin hbdd (mem_sphere_zero_iff_norm.mp hν)).mono
          (fun _ h => h.2))
    simpa only [hmin.2.1, ENNReal.toReal_ofReal hV] using h
  · linarith

end LiquidDrop
