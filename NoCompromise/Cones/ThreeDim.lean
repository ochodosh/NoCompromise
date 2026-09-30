module

public import NoCompromise.Regularity.TangentCone
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-!
# Cylindrical tangent limits of cones

Blueprint `lem:cone-tangent-cylinder`. Nontriviality means that both the cone
and its complement have positive volume. The cone condition is exact positive
dilation invariance of the density-one representative; equality of a measurable
set with that representative is never assumed.

The section of a tangent is taken in its density-one representative. Its product
structure is expressed with the ambient-valued orthogonal projection
`Submodule.starProjection`. The analytic translation argument uses only the cone
condition and local L¹ convergence. Minimality and the constant density ratio
supply the separate dilation invariance of the tangent section.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The hypotheses on the original nontrivial minimizing cone. -/
structure IsNontrivialMinimizingCone (C : Set AmbientSpace) : Prop where
  minimizing : IsLocallyPerimeterMinimizing C
  measurable : MeasurableSet C
  dilation : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C
  nontrivial : 0 < volume C ∧ 0 < volume Cᶜ

/-- Density ratios commute exactly with translations. -/
lemma cone_densityRatio_translate (F : Set AmbientSpace) (x a : AmbientSpace) (s : ℝ) :
    densityRatio ((fun y => y + a) '' F) (x + a) s = densityRatio F x s := by
  have hb : (fun y : AmbientSpace => y + a) '' ball x s = ball (x + a) s :=
    (IsometryEquiv.addRight a).image_ball x s
  have hinj : Function.Injective (fun y : AmbientSpace => y + a) :=
    fun _ _ h => add_right_cancel h
  rw [densityRatio, ← hb, ← image_inter hinj,
    show (fun y : AmbientSpace => y + a) = (fun y => a + y) from funext fun y => add_comm y a,
    volume_image_add_left, volume_image_add_left]
  rfl

lemma cone_densityOne_translate (F : Set AmbientSpace) (a : AmbientSpace) :
    densityOne ((fun y => y + a) '' F) = (fun y => y + a) '' densityOne F := by
  ext y
  obtain ⟨x, rfl⟩ := (Homeomorph.addRight a).surjective y
  change Tendsto (densityRatio ((fun y => y + a) '' F) (x + a)) _ _ ↔ _
  rw [show densityRatio ((fun y => y + a) '' F) (x + a) = densityRatio F x from
    funext fun s => cone_densityRatio_translate F x a s]
  change x ∈ densityOne F ↔ x + a ∈ (fun y => y + a) '' densityOne F
  constructor
  · exact fun hx => mem_image_of_mem _ hx
  · rintro ⟨z, hz, he⟩
    rwa [add_right_cancel he] at hz

lemma cone_densityOne_translation_invariant_of_ae {F : Set AmbientSpace} (a : AmbientSpace)
    (h : ((fun y => y + a) '' F : Set AmbientSpace) =ᵐ[volume] F) :
    (fun y => y + a) '' densityOne F = densityOne F := by
  rw [← cone_densityOne_translate]
  exact densityOne_congr_ae h

/-- Exact line invariance gives the orthogonal-projection description. -/
lemma cone_product_of_translation_invariant {S : Set AmbientSpace} (p : AmbientSpace)
    (hS : ∀ t : ℝ, (fun y => y + t • p) '' S = S) :
    S = {y | (ℝ ∙ p)ᗮ.starProjection y ∈ S ∩ (ℝ ∙ p)ᗮ} := by
  ext y
  have hm : y - (ℝ ∙ p)ᗮ.starProjection y ∈ ℝ ∙ p := by
    simpa only [Submodule.orthogonal_orthogonal] using
      (ℝ ∙ p)ᗮ.sub_starProjection_mem_orthogonal y
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
  have he : (ℝ ∙ p)ᗮ.starProjection y + t • p = y := by rw [ht]; abel
  constructor
  · intro hy
    refine ⟨?_, Submodule.starProjection_apply_mem _ _⟩
    have hmem : y + (-t) • p ∈ S := by
      rw [← hS (-t)]
      exact mem_image_of_mem _ hy
    have he' : y + (-t) • p = (ℝ ∙ p)ᗮ.starProjection y := by
      rw [neg_smul, ht]; abel
    rwa [he'] at hmem
  · rintro ⟨hy, _⟩
    rw [← he, ← hS t]
    exact mem_image_of_mem _ hy

/-- Intersecting a dilation-invariant set with a subspace preserves exact invariance. -/
lemma cone_section_dilation_invariant {S : Set AmbientSpace}
    (hS : ∀ r : ℝ, 0 < r → (fun y => r • y) '' S = S)
    (V : Submodule ℝ AmbientSpace) {r : ℝ} (hr : 0 < r) :
    (fun y => r • y) '' (S ∩ V) = S ∩ V := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hV⟩, rfl⟩
    exact ⟨by rw [← hS r hr]; exact mem_image_of_mem _ hx, V.smul_mem r hV⟩
  · rintro ⟨hy, hV⟩
    rw [← hS r hr] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨hx, (V.smul_mem_iff hr.ne').mp hV⟩, rfl⟩

/-- The canonical tangent section is measurable and is exactly a cone. -/
theorem cone_tangent_link_is_cone {F : Set AmbientSpace}
    (hF : IsLocallyPerimeterMinimizing F) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ)
    (p : AmbientSpace) :
    MeasurableSet (densityOne F ∩ (ℝ ∙ p)ᗮ) ∧
      ∀ r : ℝ, 0 < r →
        (fun y => r • y) '' (densityOne F ∩ (ℝ ∙ p)ᗮ) = densityOne F ∩ (ℝ ∙ p)ᗮ := by
  refine ⟨(measurableSet_densityOne hF.isOmegaMinimal.nullMeasurable).inter
    (Submodule.isClosed_orthogonal (ℝ ∙ p)).measurableSet, ?_⟩
  exact fun _ hr => cone_section_dilation_invariant (hF.tangent_is_cone hd).2 _ hr

/-- Local L¹ convergence remains valid when bounded continuous tests vary on a
fixed compact set and converge pointwise. -/
lemma cone_tendsto_integral_varying_test
    {f : ℕ → AmbientSpace → ℝ} {g : AmbientSpace → ℝ}
    {ψ : ℕ → AmbientSpace → ℝ} {ψ₀ : AmbientSpace → ℝ}
    {K : Set AmbientSpace} (hK : IsCompact K)
    (hf : ∀ j, IntegrableOn (f j) K) (hg : IntegrableOn g K)
    (hψ : ∀ j, ContinuousOn (ψ j) K) (_hψ₀ : ContinuousOn ψ₀ K)
    {B : ℝ} (hB : ∀ᶠ j in atTop, ∀ y ∈ K, ‖ψ j y‖ ≤ B)
    (hlim : ∀ y ∈ K, Tendsto (fun j => ψ j y) atTop (𝓝 (ψ₀ y)))
    (hconv : Tendsto (fun j => ∫ y in K, |f j y - g y|) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y in K, f j y * ψ j y) atTop
      (𝓝 (∫ y in K, g y * ψ₀ y)) := by
  have herr : Tendsto
      (fun j => (∫ y in K, f j y * ψ j y) - ∫ y in K, g y * ψ j y)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hconv.mul_const B)
    filter_upwards [hB] with j hj
    rw [← integral_sub ((hf j).mul_continuousOn (hψ j) hK)
      (hg.mul_continuousOn (hψ j) hK)]
    calc
      _ ≤ ∫ y in K, ‖f j y * ψ j y - g y * ψ j y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y in K, |f j y - g y| * B := by
        apply integral_mono_ae
        · exact (((hf j).mul_continuousOn (hψ j) hK).sub
            (hg.mul_continuousOn (hψ j) hK)).norm
        · exact ((hf j).sub hg).abs.mul_const B
        · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
          rw [← sub_mul, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hj y hy) (abs_nonneg _)
      _ = _ := integral_mul_const B _
  have hfixed : Tendsto (fun j => ∫ y in K, g y * ψ j y) atTop
      (𝓝 (∫ y in K, g y * ψ₀ y)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖ * B)
    · exact Eventually.of_forall fun j => (hg.mul_continuousOn (hψ j) hK).aestronglyMeasurable
    · filter_upwards [hB] with j hj
      filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hj y hy) (norm_nonneg _)
    · exact hg.norm.mul_const B
    · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
      exact (hlim y hy).const_mul (g y)
  simpa only [sub_add_cancel, zero_add] using herr.add hfixed

lemma cone_setIntegral_eq_indicator_on {E K : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (ψ : AmbientSpace → ℝ)
    (hs : ∀ y, y ∉ K → ψ y = 0) :
    (∫ y in E, ψ y) = ∫ y in K, E.indicator (fun _ => (1 : ℝ)) y * ψ y := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (f := fun y => E.indicator (fun _ => (1 : ℝ)) y * ψ y)
    (fun y hy => by rw [hs y hy, mul_zero])]
  rw [← integral_indicator₀ hE]
  congr 1
  funext y
  by_cases hy : y ∈ E <;> simp [hy]

/-- Tests composed with affine maps approaching a translation pass to a local
L¹ limit. The scalar factors need only be eventually positive. -/
lemma cone_tendsto_affine_test
    {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hE : ∀ j, NullMeasurableSet (E j) volume) (hF : NullMeasurableSet F volume)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(E j).indicator (fun _ => (1 : ℝ)) y - F.indicator (fun _ => (1 : ℝ)) y|)
        atTop (𝓝 0))
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop (𝓝 1))
    (a : AmbientSpace) {φ : AmbientSpace → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun j => ∫ y in E j, φ (scale j • y + a)) atTop
      (𝓝 (∫ y in F, φ (y + a))) := by
  obtain ⟨R, hR, hsupp⟩ := hcφ.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  let K : Set AmbientSpace := closedBall 0 (2 * (R + ‖a‖) + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hz (c : ℝ) (hc : 1 / 2 ≤ c) (y : AmbientSpace) (hy : y ∉ K) :
      φ (c • y + a) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hb := hsupp hmem
    simp only [mem_ball, dist_zero_right] at hb
    have hn : 2 * (R + ‖a‖) + 1 < ‖y‖ := by
      simpa only [K, mem_closedBall, dist_zero_right, not_le] using hy
    have hn' : c * ‖y‖ ≤ ‖c • y + a‖ + ‖a‖ := by
      calc
        c * ‖y‖ = ‖c • y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        _ = ‖(c • y + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    nlinarith [norm_nonneg y]
  have hscalebound : ∀ᶠ j in atTop, 1 / 2 ≤ scale j :=
    hscale.eventually (Ici_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  obtain ⟨B, hB⟩ := hcφ.exists_bound_of_continuous hφ
  have hlim := cone_tendsto_integral_varying_test hK
    (fun j => (locallyIntegrable_indicator_one (hE j)).integrableOn_isCompact hK)
    ((locallyIntegrable_indicator_one hF).integrableOn_isCompact hK)
    (fun j => (show Continuous (fun y => φ (scale j • y + a)) by fun_prop).continuousOn)
    (show ContinuousOn (fun y => φ (y + a)) K from (by fun_prop : Continuous _).continuousOn)
    (Eventually.of_forall fun j y _ => hB (scale j • y + a))
    (fun y _ => by simpa only [one_smul, Function.comp_def] using
      (hφ.tendsto (1 • y + a)).comp ((hscale.smul_const y).add_const a))
    (hconv K hK)
  rw [← cone_setIntegral_eq_indicator_on hF _
    (by simpa only [one_smul] using hz 1 (by norm_num))] at hlim
  apply hlim.congr'
  filter_upwards [hscalebound] with j hj
  exact (cone_setIntegral_eq_indicator_on (hE j) _ (hz (scale j) hj)).symm

/-- The affine symmetry inherited by a blow-up of an exactly invariant cone. -/
lemma cone_blowup_affine_image {C : Set AmbientSpace}
    (hC : ∀ c : ℝ, 0 < c → (fun y => c • y) '' C = C)
    (p : AmbientSpace) {r : ℝ} (_hr : 0 < r) (t : ℝ) (hc : 0 < 1 + t * r) :
    (fun y => (1 + t * r) • y + t • p) '' blowupSet C p r = blowupSet C p r := by
  have he (y : AmbientSpace) :
      p + r • ((1 + t * r) • y + t • p) = (1 + t * r) • (p + r • y) := by
    simp only [smul_add, add_smul, one_smul, smul_smul]
    module
  have hmem (y : AmbientSpace) :
      (1 + t * r) • y + t • p ∈ blowupSet C p r ↔ y ∈ blowupSet C p r := by
    change p + r • ((1 + t * r) • y + t • p) ∈ C ↔ p + r • y ∈ C
    rw [he]
    nth_rw 1 [← hC (1 + t * r) hc]
    exact ⟨fun ⟨z, hz, hez⟩ => by
      have : z = p + r • y := (smul_right_injective _ hc.ne') hez
      rwa [← this], fun hy => ⟨p + r • y, hy, rfl⟩⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hmem z).mpr hz
  · intro hy
    let z := (1 + t * r)⁻¹ • (y - t • p)
    have hz : (1 + t * r) • z + t • p = y := by
      simp [z, smul_smul, hc.ne']
    exact ⟨z, (hmem z).mp (hz.symm ▸ hy), hz⟩

lemma cone_affine_setIntegral (E : Set AmbientSpace) (φ : AmbientSpace → ℝ)
    (a : AmbientSpace) {c : ℝ} (hc : 0 < c) :
    (∫ y in (fun z => c • z + a) '' E, φ y) =
      c ^ 3 * ∫ y in E, φ (c • y + a) := by
  have he : (fun z => c • z + a) '' E =
      (fun z => a + z) '' ((fun z => c • z) '' E) := by
    rw [image_image]
    congr 1
    funext z
    exact add_comm _ _
  rw [he, (measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding, setIntegral_image_smul _ _ hc]
  congr 1
  congr 1
  funext y
  rw [add_comm a]

/-- Translation invariance of test integrals follows directly from conical
symmetry and local L¹ convergence. -/
lemma cone_limit_translation_test {C F : Set AmbientSpace}
    (hmC : NullMeasurableSet C volume)
    (hC : ∀ c : ℝ, 0 < c → (fun y => c • y) '' C = C)
    (p : AmbientSpace) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (ht : Tendsto r atTop (𝓝 0)) (hmF : NullMeasurableSet F volume)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet C p (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0))
    (t : ℝ) {φ : AmbientSpace → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ y in F, φ (y + t • p)) = ∫ y in F, φ y := by
  have hm j := nullMeasurableSet_blowupSet hmC p (hr j)
  have hscale : Tendsto (fun j => 1 + t * r j) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (ht.const_mul t).const_add 1
  have hleft := cone_tendsto_affine_test hm hmF hconv hscale (t • p) hφ hcφ
  have hright := cone_tendsto_affine_test hm hmF hconv
    (tendsto_const_nhds (x := (1 : ℝ))) 0 hφ hcφ
  simp only [one_smul, add_zero] at hright
  have heq : ∀ᶠ j in atTop,
      (1 + t * r j) ^ 3 * (∫ y in blowupSet C p (r j), φ ((1 + t * r j) • y + t • p)) =
        ∫ y in blowupSet C p (r j), φ y := by
    filter_upwards [hscale.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
    rw [← cone_affine_setIntegral _ _ _ hj, cone_blowup_affine_image hC p (hr j) t hj]
  have hlim := ((hscale.pow 3).mul hleft).congr' heq
  simp only [one_pow, one_mul] at hlim
  exact tendsto_nhds_unique hlim hright

/-- AE equality is preserved by the actual blow-up coordinates. -/
lemma cone_blowup_congr_ae {C D : Set AmbientSpace} (h : C =ᵐ[volume] D)
    (p : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    blowupSet C p r =ᵐ[volume] blowupSet D p r :=
  (Measure.quasiMeasurePreserving_smul volume hr.ne').preimage_ae_eq
    ((measurePreserving_add_left volume p).quasiMeasurePreserving.preimage_ae_eq h)

lemma cone_translation_ae_of_test {F : Set AmbientSpace} (hmF : MeasurableSet F)
    (a : AmbientSpace)
    (h : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y in F, φ (y + a)) = ∫ y in F, φ y) :
    ((fun y => y + a) '' F : Set AmbientSpace) =ᵐ[volume] F := by
  let D := (fun y => y + a) '' F
  have hmD : MeasurableSet D :=
    (Homeomorph.addRight a).measurableEmbedding.measurableSet_image.mpr hmF
  have hpair : D.indicator (fun _ => (1 : ℝ)) =ᵐ[volume] F.indicator (fun _ => (1 : ℝ)) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_indicator_one hmD.nullMeasurableSet)
      (locallyIntegrable_indicator_one hmF.nullMeasurableSet)
    intro φ hφ hcφ
    have he (G : Set AmbientSpace) :
        (fun y => φ y • G.indicator (fun _ => (1 : ℝ)) y) = G.indicator φ := by
      funext y
      by_cases hy : y ∈ G <;> simp [hy, smul_eq_mul]
    rw [he D, he F, integral_indicator hmD, integral_indicator hmF]
    change (∫ y in (fun z => z + a) '' F, φ y) = _
    rw [(measurePreserving_add_right volume a).setIntegral_image_emb
      (MeasurableEquiv.addRight a).measurableEmbedding]
    exact h φ (hφ.of_le (by simp)) hcφ
  filter_upwards [hpair] with y hy
  change (y ∈ D) = (y ∈ F)
  by_cases hyD : y ∈ D <;> by_cases hyF : y ∈ F <;> simp [hyD, hyF] at hy ⊢

/-- The part of the tangent-existence conclusion needed here. The subsequence
of positive radii can be absorbed into `r`; its convergence is unchanged. -/
structure IsConeTangentLimit (C : Set AmbientSpace) (p : AmbientSpace)
    (F : Set AmbientSpace) : Prop where
  measurable : MeasurableSet F
  minimizing : IsLocallyPerimeterMinimizing F
  density : ∃ θ : ℝ, ∀ R : ℝ, 0 < R →
    (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ
  convergence : ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Tendsto r atTop (𝓝 0) ∧
    ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet C p (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0)

/-- Every tangent of a nontrivial minimizing cone at a nonzero boundary point
is invariant along its radial direction, both a.e. and exactly in its canonical
representative. No equality of the original set with that representative is assumed. -/
theorem cone_blowup_translation_invariant {C F : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (_hp : p ∈ frontier (densityOne C)) (_hp0 : p ≠ 0)
    (hF : IsConeTangentLimit C p F) (t : ℝ) :
    ((fun y => y + t • p) '' F : Set AmbientSpace) =ᵐ[volume] F ∧
      (fun y => y + t • p) '' densityOne F = densityOne F := by
  obtain ⟨r, hr, ht, hconv⟩ := hF.convergence
  have hDC := densityOne_ae_eq (by norm_num : 0 < 3) hC.measurable.nullMeasurableSet
  have hconvD : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet (densityOne C) p (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0) := by
    intro K hK
    apply (hconv K hK).congr'
    apply Eventually.of_forall
    intro j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ))
        (cone_blowup_congr_ae hDC p (hr j)))] with y hy
    rw [hy]
  have hae : ((fun y => y + t • p) '' F : Set AmbientSpace) =ᵐ[volume] F := by
    apply cone_translation_ae_of_test hF.measurable (t • p)
    intro φ hφ hcφ
    exact cone_limit_translation_test
      (measurableSet_densityOne hC.measurable.nullMeasurableSet).nullMeasurableSet
      hC.dilation p hr ht hF.measurable.nullMeasurableSet hconvD t hφ.continuous hcφ
  exact ⟨hae, cone_densityOne_translation_invariant_of_ae (t • p) hae⟩

/-- Exact cylindrical structure of the canonical representative, and the
corresponding AE structure for the measurable tangent itself. `starProjection`
is Mathlib's ambient-valued orthogonal projection. -/
theorem cone_tangent_product {C F : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0)
    (hF : IsConeTangentLimit C p F) :
    MeasurableSet (densityOne F ∩ (ℝ ∙ p)ᗮ) ∧
      densityOne F = {y | (ℝ ∙ p)ᗮ.starProjection y ∈ densityOne F ∩ (ℝ ∙ p)ᗮ} ∧
      F =ᵐ[volume] {y | (ℝ ∙ p)ᗮ.starProjection y ∈ densityOne F ∩ (ℝ ∙ p)ᗮ} := by
  have he := cone_product_of_translation_invariant p
    (fun t => (cone_blowup_translation_invariant hC hp hp0 hF t).2)
  refine ⟨(measurableSet_densityOne hF.measurable.nullMeasurableSet).inter
    (Submodule.isClosed_orthogonal (ℝ ∙ p)).measurableSet, he, ?_⟩
  rw [← he]
  exact (densityOne_ae_eq (by norm_num : 0 < 3) hF.measurable.nullMeasurableSet).symm

end LiquidDrop
