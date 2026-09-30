module

public import NoCompromise.Cones.Smooth
public import NoCompromise.Cones.DescentMain
public import NoCompromise.Regularity.IsometryMinimal
public import NoCompromise.Regularity.IsometryDensity
public import NoCompromise.Cones.Halfspace

@[expose] public section

/-!
# Halfspace tangents at nonzero boundary points of minimizing cones

First step of blueprint `lem:cone-smooth` (chapter 25): "By Lemmas lem:cone-tangent-cylinder,
lem:cone-descent and lem:cone-2d, every tangent cone of `C` at every nonzero boundary point is a
halfspace; the empty and full planar factors are excluded by the two-sided density estimate at the
tangent-cone vertex."

* `cone_tangent_planar_factor` : in a radial frame (a linear isometry sending `e₃` to `p / ‖p‖`)
  a nontrivial tangent limit at `p ≠ 0` is exactly a vertical cylinder over a measurable planar
  set `L` that is locally perimeter minimising (`cone_descent`), a nontrivial cone.
* `cone_tangent_halfspace` : assuming the statement of `lem:cone-2d`
  (`Cone2dHalfplaneStatement`, an explicit hypothesis here), such a tangent is an open halfspace
  whose normal is orthogonal to `p`.
* `cone_exists_halfspace_tangent` : combined with `cone_exists_nontrivial_tangent` (the two-sided
  density estimate), a halfspace tangent limit exists at every nonzero boundary point.
* Supporting facts: `IsLocallyPerimeterMinimizing.congr_ae` (minimality depends only on the a.e.
  class, via the compact-change competitor `(F ∩ K) ∪ (E \ K)`),
  `IsLocallyPerimeterMinimizing.preimage_affineIsometry`, `cone_densityOne_dilation`.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop

/-- The statement of blueprint `lem:cone-2d` (proved separately as `cone2d_halfplane`). -/
def Cone2dHalfplaneStatement : Prop :=
  ∀ C : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet C → IsLocallyPerimeterMinimizing C →
    (∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) →
    0 < volume C ∧ 0 < volume Cᶜ →
    ∃ μ : EuclideanSpace ℝ (Fin 2), ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x}

/-- Compact-change comparisons are unaffected by changing the reference set on a null set. -/
theorem IsOmegaMinimalAtScales.congr_ae {n : ℕ}
    {E E' : Set (EuclideanSpace ℝ (Fin n))} {ω : ℝ} {s : ℝ≥0∞}
    (hE : IsOmegaMinimalAtScales E ω s) (h : E =ᵐ[volume] E') :
    IsOmegaMinimalAtScales E' ω s := by
  have hpE' : HasLocallyFinitePerimeter E' := by
    intro U hU hcU
    rw [perimeterIn_congr_ae U (ae_restrict_of_ae h.symm)]
    exact hE.locallyFinite U hU hcU
  refine ⟨hE.nonneg, hE.scale_pos, hE.nullMeasurable.congr h, hpE', ?_⟩
  intro x r hr hrs F hmF hpF hc hs
  let K := closure (F ∆ E')
  let G := (F ∩ K) ∪ (E \ K)
  have hmG : NullMeasurableSet G volume :=
    (hmF.inter isClosed_closure.measurableSet.nullMeasurableSet).union
      (hE.nullMeasurable.diff isClosed_closure.measurableSet.nullMeasurableSet)
  have hGF : G =ᵐ[volume] F := by
    filter_upwards [h] with y hy
    change (y ∈ G) = (y ∈ F)
    apply propext
    have he : y ∈ E ↔ y ∈ E' := Iff.of_eq hy
    by_cases hk : y ∈ K
    · simp [G, hk]
    · have hn : y ∉ F ∆ E' := fun hy => hk (subset_closure hy)
      simp only [mem_symmDiff] at hn
      simp only [G, mem_union, mem_inter_iff, Set.mem_sdiff, hk, and_false, false_or,
        not_false_eq_true, and_true]
      tauto
  have hpG : HasLocallyFinitePerimeter G := by
    intro U hU hcU
    rw [perimeterIn_congr_ae U (ae_restrict_of_ae hGF)]
    exact hpF U hU hcU
  have hsub : closure (G ∆ E) ⊆ K := by
    apply closure_minimal _ isClosed_closure
    intro y hy
    by_contra hk
    change y ∉ K at hk
    simp [G, mem_symmDiff, hk] at hy
  have hcomp := hE.comparison x r hr hrs G hmG hpG
    (hc.of_isClosed_subset isClosed_closure hsub) (hsub.trans hs)
  rw [perimeterIn_congr_ae (ball x r) (ae_restrict_of_ae h),
    perimeterIn_congr_ae (ball x r) (ae_restrict_of_ae hGF)] at hcomp
  have hv : volume (E ∆ G) = volume (E' ∆ F) := by
    apply measure_congr
    filter_upwards [h, hGF] with y hy hyG
    change (y ∈ E ∆ G) = (y ∈ E' ∆ F)
    change (y ∈ E) = (y ∈ E') at hy
    change (y ∈ G) = (y ∈ F) at hyG
    simp only [mem_symmDiff, hy, hyG]
  rwa [hv] at hcomp

/-- Local perimeter minimality depends only on the almost-everywhere class. -/
theorem IsLocallyPerimeterMinimizing.congr_ae {n : ℕ}
    {E E' : Set (EuclideanSpace ℝ (Fin n))}
    (hE : IsLocallyPerimeterMinimizing E) (h : E =ᵐ[volume] E') :
    IsLocallyPerimeterMinimizing E' :=
  fun R hR => (hE R hR).congr_ae h

/-- Local minimizers remain minimizing in rigid coordinates. -/
theorem IsLocallyPerimeterMinimizing.preimage_affineIsometry {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : IsLocallyPerimeterMinimizing E)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsLocallyPerimeterMinimizing (a ⁻¹' E) :=
  fun R hR => (hE R hR).preimage_affineIsometry a

/-- Positive dilation covariance of density ratios in arbitrary finite dimension. -/
lemma cone_densityRatio_pos_smul {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    densityRatio ((fun y => r • y) '' E) (r • x) (r * s) = densityRatio E x s := by
  have hinj : Function.Injective (fun y : EuclideanSpace ℝ (Fin n) => r • y) :=
    (Homeomorph.smulOfNeZero r hr.ne' :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)).injective
  have hb : (fun y : EuclideanSpace ℝ (Fin n) => r • y) '' ball x s =
      ball (r • x) (r * s) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hr] using Metric.smul_image_ball hr.ne' x s
  rw [densityRatio, ← hb, ← image_inter hinj,
    volume_image_pos_smul _ hr, volume_image_pos_smul _ hr]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  dsimp [densityRatio]
  field_simp [hr.ne']

/-- Exact dilation invariance passes to the canonical density-one representative. -/
theorem cone_densityOne_dilation {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : ∀ r : ℝ, 0 < r → (fun y => r • y) '' E = E) :
    ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne E = densityOne E := by
  have hmem (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
      r • x ∈ densityOne E ↔ x ∈ densityOne E := by
    have he (s : ℝ) : densityRatio E (r • x) (r * s) = densityRatio E x s := by
      simpa only [hE r hr] using cone_densityRatio_pos_smul E x hr s
    change Tendsto (densityRatio E (r • x)) _ _ ↔ Tendsto (densityRatio E x) _ _
    constructor
    · intro h
      simpa only [Function.comp_def, he] using
        h.comp (tangent_pos_mul_tendsto_zero hr)
    · intro h
      have ht := h.comp (tangent_pos_mul_tendsto_zero (inv_pos.mpr hr))
      apply ht.congr'
      apply Eventually.of_forall
      intro s
      have hs := he (r⁻¹ * s)
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hs
      exact hs.symm
  intro r hr
  ext y
  obtain ⟨x, rfl⟩ := (Homeomorph.smulOfNeZero r hr.ne' :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)).surjective y
  change r • x ∈ (fun y => r • y) '' densityOne E ↔ r • x ∈ densityOne E
  rw [hmem x hr]
  constructor
  · rintro ⟨z, hz, he⟩
    have hzx : z = x := (Homeomorph.smulOfNeZero r hr.ne').injective he
    rwa [← hzx]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A null change in the base makes only a null change in its infinite cylinder. -/
theorem verticalCylinder_congr_ae {L M : Set (EuclideanSpace ℝ (Fin 2))}
    (h : L =ᵐ[volume] M) : verticalCylinder L =ᵐ[volume] verticalCylinder M := by
  have hp : (Prod.snd ⁻¹' L : Set (ℝ × EuclideanSpace ℝ (Fin 2))) =ᵐ[volume.prod volume]
      Prod.snd ⁻¹' M := Measure.quasiMeasurePreserving_snd.preimage_ae_eq h
  exact (euclideanLastEquiv_measurePreserving 2).quasiMeasurePreserving.preimage_ae_eq hp

/-- Positive volume of both cylinder phases excludes null planar factors. -/
theorem verticalCylinder_nontrivial {L : Set (EuclideanSpace ℝ (Fin 2))}
    (h : 0 < volume (verticalCylinder L) ∧ 0 < volume (verticalCylinder L)ᶜ) :
    0 < volume L ∧ 0 < volume Lᶜ := by
  have hpos (M : Set (EuclideanSpace ℝ (Fin 2)))
      (hM : 0 < volume (verticalCylinder M)) : 0 < volume M := by
    by_contra hn
    have hzero : volume M = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hm : M =ᵐ[volume] (∅ : Set (EuclideanSpace ℝ (Fin 2))) := (ae_eq_empty).mpr hzero
    have hc := measure_congr (verticalCylinder_congr_ae hm)
    simp [verticalCylinder] at hc
    exact hM.ne' hc
  exact ⟨hpos L h.1, hpos Lᶜ h.2⟩

/-- Choose orthonormal coordinates whose vertical axis is the direction of `p`. -/
theorem cone_exists_radial_frame {p : AmbientSpace} (hp : p ≠ 0) :
    ∃ A : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace,
      A (EuclideanSpace.single (Fin.last 2) 1) = ‖p‖⁻¹ • p := by
  have hunit : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]
  let u : AmbientSpace := EuclideanSpace.single (Fin.last 2) 1
  exact ⟨(ℝ ∙ (u - ‖p‖⁻¹ • p))ᗮ.reflection,
    Submodule.reflection_sub (by simpa [u] using hunit.symm)⟩

/-- A set invariant along `p` is a vertical cylinder in any radial frame. -/
theorem cone_preimage_eq_verticalCylinder {S : Set AmbientSpace} {p : AmbientSpace}
    (hS : ∀ t : ℝ, (fun y => y + t • p) '' S = S)
    (A : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (hA : A (EuclideanSpace.single (Fin.last 2) 1) = ‖p‖⁻¹ • p) :
    A ⁻¹' S = verticalCylinder ((fun q => A (graphBaseN 2 q)) ⁻¹' S) := by
  have hmem (y : AmbientSpace) (t : ℝ) : y + t • p ∈ S ↔ y ∈ S := by
    constructor
    · intro hy
      have hh : y + t • p + (-t) • p ∈ S := by
        rw [← hS (-t)]
        exact mem_image_of_mem _ hy
      simpa only [neg_smul, add_neg_cancel_right] using hh
    · intro hy
      rw [← hS t]
      exact mem_image_of_mem _ hy
  ext z
  change A z ∈ S ↔ A (graphBaseN 2 (graphProjectionN 2 z)) ∈ S
  have hz : A z = A (graphBaseN 2 (graphProjectionN 2 z)) +
      (z (Fin.last 2) * ‖p‖⁻¹) • p := by
    conv_lhs => rw [← graphAppendN_projection z]
    simp only [graphAppendN, map_add, map_smul, hA, smul_smul]
  rw [hz, hmem]

/-- Sections by a linear embedding inherit exact positive dilation invariance. -/
theorem cone_section_in_frame_dilation {S : Set AmbientSpace}
    (hS : ∀ r : ℝ, 0 < r → (fun y => r • y) '' S = S)
    (A : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) :
    ∀ r : ℝ, 0 < r →
      (fun q => r • q) '' ((fun q => A (graphBaseN 2 q)) ⁻¹' S) =
        ((fun q => A (graphBaseN 2 q)) ⁻¹' S) := by
  intro r hr
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    change A (graphBaseN 2 (r • z)) ∈ S
    rw [map_smul, map_smul, ← hS r hr]
    exact mem_image_of_mem _ hz
  · intro hq
    refine ⟨r⁻¹ • q, ?_, smul_inv_smul₀ hr.ne' q⟩
    change A (graphBaseN 2 (r⁻¹ • q)) ∈ S
    rw [map_smul, map_smul, ← hS r⁻¹ (inv_pos.mpr hr)]
    exact mem_image_of_mem _ hq

/-- Pairing a horizontal vector with an ambient vector reads only its planar projection. -/
lemma cone_inner_graphBase (μ : EuclideanSpace ℝ (Fin 2)) (z : AmbientSpace) :
    inner ℝ (graphBaseN 2 μ) z = inner ℝ μ (graphProjectionN 2 z) := by
  rw [real_inner_comm, show graphBaseN 2 μ = graphAppendN μ 0 by simp [graphAppendN],
    inner_graphAppendN]
  simp [real_inner_comm]

/-- The halfplane classification lifts through a cylinder, including changes on null sets. -/
theorem cone_cylinder_halfspace {L : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : MeasurableSet L) {μ : EuclideanSpace ℝ (Fin 2)} (hμ : ‖μ‖ = 1)
    (he : densityOne L = {q | 0 < inner ℝ μ q}) :
    densityOne (verticalCylinder L) = {z | 0 < inner ℝ (graphBaseN 2 μ) z} := by
  have hrep : L =ᵐ[volume] {q | 0 < inner ℝ μ q} := by
    rw [← he]
    exact (densityOne_ae_eq (by norm_num : 0 < 2) hL.nullMeasurableSet).symm
  have hc := densityOne_congr_ae (verticalCylinder_congr_ae hrep)
  have heq : verticalCylinder {q | 0 < inner ℝ μ q} =
      {z | 0 < inner ℝ (graphBaseN 2 μ) z} := by
    ext z
    simp only [mem_verticalCylinder, mem_ofPred_eq, cone_inner_graphBase]
  rw [heq] at hc
  rw [hc, densityOne_halfspace]
  intro hz
  have hn := norm_graphBaseN_for_descent μ
  rw [hz, norm_zero, hμ] at hn
  norm_num at hn

/-- Every nontrivial tangent at a nonzero boundary point has a nontrivial minimizing planar
factor in radial coordinates. The equality of representatives is exact. -/
theorem cone_tangent_planar_factor {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) {F : Set AmbientSpace}
    (hF : IsConeTangentLimit C p F) (hFnt : 0 < volume F ∧ 0 < volume Fᶜ) :
    ∃ (A : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (L : Set (EuclideanSpace ℝ (Fin 2))),
      A (EuclideanSpace.single (Fin.last 2) 1) = ‖p‖⁻¹ • p ∧
      MeasurableSet L ∧ IsLocallyPerimeterMinimizing L ∧
      (∀ r : ℝ, 0 < r → (fun q => r • q) '' densityOne L = densityOne L) ∧
      (0 < volume L ∧ 0 < volume Lᶜ) ∧
      A ⁻¹' densityOne F = verticalCylinder L ∧
      A ⁻¹' F =ᵐ[volume] verticalCylinder L := by
  obtain ⟨A, hA⟩ := cone_exists_radial_frame hp0
  let L := (fun q => A (graphBaseN 2 q)) ⁻¹' densityOne F
  have hmD := measurableSet_densityOne hF.measurable.nullMeasurableSet
  have hmL : MeasurableSet L := hmD.preimage
    (A.continuous.comp (graphBaseN 2).continuous).measurable
  have he : A ⁻¹' densityOne F = verticalCylinder L :=
    cone_preimage_eq_verticalCylinder
      (fun t => (cone_blowup_translation_invariant hC hp hp0 hF t).2) A hA
  have hFD : F =ᵐ[volume] densityOne F :=
    (densityOne_ae_eq (by norm_num : 0 < 3) hF.measurable.nullMeasurableSet).symm
  have hae : A ⁻¹' F =ᵐ[volume] verticalCylinder L := by
    rw [← he]
    exact (measurePreserving_affineIsometry A.toAffineIsometryEquiv).quasiMeasurePreserving
      |>.preimage_ae_eq hFD
  have hmin : IsLocallyPerimeterMinimizing (verticalCylinder L) :=
    (hF.minimizing.preimage_affineIsometry A.toAffineIsometryEquiv).congr_ae hae
  have hvol : 0 < volume (verticalCylinder L) ∧ 0 < volume (verticalCylinder L)ᶜ := by
    have hv : volume (A ⁻¹' F) = volume F :=
      (measurePreserving_affineIsometry A.toAffineIsometryEquiv).measure_preimage
        hF.measurable.nullMeasurableSet
    have hvc : volume (A ⁻¹' Fᶜ) = volume Fᶜ :=
      (measurePreserving_affineIsometry A.toAffineIsometryEquiv).measure_preimage
        hF.measurable.compl.nullMeasurableSet
    rw [← measure_congr hae, ← measure_congr hae.compl]
    exact ⟨hv.symm ▸ hFnt.1, hvc.symm ▸ hFnt.2⟩
  obtain ⟨θ, hθ⟩ := hF.density
  exact ⟨A, L, hA, hmL, cone_descent hmin,
    cone_densityOne_dilation
      (cone_section_in_frame_dilation (hF.minimizing.tangent_is_cone hθ).2 A),
    verticalCylinder_nontrivial hvol, he, hae⟩

/-- Assuming the planar classification, every nontrivial tangent at a nonzero boundary point
is a halfspace whose normal is orthogonal to the radial direction. -/
theorem cone_tangent_halfspace (h2d : Cone2dHalfplaneStatement) {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) {F : Set AmbientSpace}
    (hF : IsConeTangentLimit C p F) (hFnt : 0 < volume F ∧ 0 < volume Fᶜ) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧
      densityOne F = {x | 0 < inner ℝ ν x} := by
  obtain ⟨A, L, hA, hmL, hminL, hdL, hntL, _he, hae⟩ :=
    cone_tangent_planar_factor hC hp hp0 hF hFnt
  obtain ⟨μ, hμ, hμL⟩ := h2d L hmL hminL hdL hntL
  let ν := A (graphBaseN 2 μ)
  have hν : ‖ν‖ = 1 := by
    rw [show ‖ν‖ = ‖graphBaseN 2 μ‖ from A.norm_map _, norm_graphBaseN_for_descent, hμ]
  have hperp : inner ℝ ν p = 0 := by
    have hh : inner ℝ ν (‖p‖⁻¹ • p) = 0 := by
      rw [← hA]
      change inner ℝ (A (graphBaseN 2 μ)) (A _) = 0
      rw [A.inner_map_map]
      simp only [EuclideanSpace.inner_single_right, graphBaseN_last, map_zero, mul_zero]
    rw [inner_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hp0))
  have hc := densityOne_congr_ae hae
  change densityOne (A.toAffineIsometryEquiv ⁻¹' F) = densityOne (verticalCylinder L) at hc
  rw [densityOne_preimage_affineIsometry F A.toAffineIsometryEquiv,
    cone_cylinder_halfspace hmL hμ hμL] at hc
  refine ⟨ν, hν, hperp, ?_⟩
  ext x
  have hh := Set.ext_iff.mp hc (A.symm x)
  change A (A.symm x) ∈ densityOne F ↔ 0 < inner ℝ (graphBaseN 2 μ) (A.symm x) at hh
  rw [A.apply_symm_apply] at hh
  have hi : inner ℝ ν x = inner ℝ (graphBaseN 2 μ) (A.symm x) := by
    conv_lhs => rw [← A.apply_symm_apply x]
    exact A.inner_map_map _ _
  simpa only [mem_ofPred_eq, hi] using hh

/-- The two-sided density estimate supplies a nontrivial tangent, so a halfspace tangent exists. -/
theorem cone_exists_halfspace_tangent (h2d : Cone2dHalfplaneStatement) {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) :
    ∃ F : Set AmbientSpace, IsConeTangentLimit C p F ∧
      ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧
        densityOne F = {x | 0 < inner ℝ ν x} := by
  obtain ⟨F, hF, hFcone, _⟩ := cone_exists_nontrivial_tangent hC hp
  exact ⟨F, hF, cone_tangent_halfspace h2d hC hp hp0 hF hFcone.nontrivial⟩


end LiquidDrop
