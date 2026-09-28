import NoCompromise.Surface.Geometry
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Differentials of maps into a surface are tangent almost everywhere

Let `f` map a planar set `A` into a set `S ⊆ ℝ³`. At a Lebesgue density point `z` of `A`
(with respect to balls whose centres drift at comparable scale) every direction is a tangent
direction of `A`, so `A` has unique differentials at `z`. Hence, wherever `f` is differentiable
at such a point, `fderiv ℝ f z` annihilates every function vanishing near `f z` on `S`, i.e. it
takes values in the intrinsic `tangentPlane S (f z)`. For an embedded surface and an injective
differential the range is then the whole tangent plane (dimension count).

No measurability of `A` is needed for `ae_fderiv_mem_tangentPlane`. The range equality needs
`f z ∈ S`, which is automatic at almost every point of `A` once `A` is null-measurable
(`ae_range_fderiv_eq_tangentPlane`); `ae_range_fderiv_eq_tangentPlane_of_mem` avoids
measurability by assuming `z ∈ A`.
-/

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- At almost every point of an arbitrary set `A` in a finite-dimensional real space (for an
additive Haar measure), every direction lies in the tangent cone, so `A` has unique
differentials there. -/
theorem ae_uniqueDiffWithinAt_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (A : Set E) :
    ∀ᵐ z ∂(μ.restrict A), UniqueDiffWithinAt ℝ A z := by
  have key : ∀ᵐ z ∂(μ.restrict A), ∀ K : ℕ, ∀ (v : E) (η : ℝ), 0 < η → ‖v‖ ≤ K * η →
      Tendsto (fun t : ℝ => μ (A ∩ closedBall (z + t • v) (η * t)) /
        μ (closedBall (z + t • v) (η * t))) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_all_iff]
    intro K
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ A K] with z hz
    intro v η hη hv
    refine hz (fun t => z + t • v) (fun t => η * t) ?_ ?_
    · refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => η * t) (𝓝 0) (𝓝 (η * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        exact mul_pos hη ht
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [mem_closedBall, dist_eq_norm]
      have : z - (z + t • v) = -(t • v) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      nlinarith
  filter_upwards [key] with z hz
  have hcone : tangentConeAt ℝ A z = univ := by
    refine eq_univ_of_forall fun v => ?_
    rw [Metric.nhds_basis_ball.tangentConeAt_eq_biInter_closure]
    simp only [mem_iInter₂]
    intro ε hε
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨K, hK⟩ := exists_nat_ge (‖v‖ / (η / 2))
    have hη2 : 0 < η / 2 := by positivity
    have hlim := hz K v (η / 2) hη2 (by rwa [div_le_iff₀ hη2] at hK)
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (A ∩ closedBall (z + t • v) (η / 2 * t)).Nonempty := by
      filter_upwards [hlim.eventually (lt_mem_nhds (show (0 : ENNReal) < 1 from zero_lt_one))]
        with t ht
      rw [nonempty_iff_ne_empty]
      intro he
      rw [he] at ht
      simp at ht
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * (‖v‖ + η / 2) < ε := by
      have : Tendsto (fun t : ℝ => t * (‖v‖ + η / 2)) (𝓝 0) (𝓝 (0 * (‖v‖ + η / 2))) :=
        tendsto_id.mul tendsto_const_nhds
      rw [zero_mul] at this
      exact (this.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hε)
    obtain ⟨t, ⟨a, haA, ha⟩, ht, htpos⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
    have htpos' : (0 : ℝ) < t := htpos
    rw [mem_closedBall, dist_eq_norm] at ha
    refine ⟨t⁻¹ • (a - z), ?_, ?_⟩
    · rw [Set.mem_smul]
      refine ⟨t⁻¹, mem_univ _, a - z, ⟨?_, ?_⟩, rfl⟩
      · rw [mem_ball, dist_zero_right]
        have : a - z = (a - (z + t • v)) + t • v := by abel
        rw [this]
        calc ‖(a - (z + t • v)) + t • v‖ ≤ ‖a - (z + t • v)‖ + ‖t • v‖ := norm_add_le _ _
          _ ≤ η / 2 * t + t * ‖v‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos']
            linarith
          _ = t * (‖v‖ + η / 2) := by ring
          _ < ε := ht
      · simp [haA]
    · rw [dist_eq_norm]
      have : v - t⁻¹ • (a - z) = -(t⁻¹ • (a - (z + t • v))) := by
        simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ htpos'.ne', one_smul]
        abel
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos')]
      calc t⁻¹ * ‖a - (z + t • v)‖ ≤ t⁻¹ * (η / 2 * t) := by gcongr
        _ = η / 2 := by field_simp
        _ < η := by linarith
  refine ⟨?_, mem_closure_of_nonempty_tangentConeAt (by rw [hcone]; exact univ_nonempty)⟩
  rw [hcone, Submodule.span_univ, Submodule.top_coe]
  exact dense_univ

/-- If `A` has unique differentials at `z` and `f` maps `A` into `S`, then the differential of
`f` at `z` takes values in the intrinsic tangent plane of `S` at `f z`. -/
theorem fderiv_mem_tangentPlane_of_uniqueDiffWithinAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {S : Set E₃} {f : F → E₃} {A : Set F} {z : F}
    (hAS : ∀ a ∈ A, f a ∈ S) (hA : UniqueDiffWithinAt ℝ A z) (hf : DifferentiableAt ℝ f z)
    (v : F) : fderiv ℝ f z v ∈ tangentPlane S (f z) := by
  rw [mem_tangentPlane_iff]
  intro φ hφ hφ0
  have hT : Tendsto f (𝓝[A] z) (𝓝[S] (f z)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall hAS⟩
  have hg0 : (φ ∘ f) =ᶠ[𝓝[A] z] fun _ => (0 : ℝ) := hT.eventually hφ0
  have hgc : ContinuousAt (φ ∘ f) z := (hφ.comp z hf).continuousAt
  have hne : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hA.mem_closure
  have hgz : (φ ∘ f) z = 0 :=
    tendsto_nhds_unique (hgc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hg0.symm)
  have h1 : HasFDerivWithinAt (φ ∘ f) ((fderiv ℝ φ (f z)).comp (fderiv ℝ f z)) A z :=
    (hφ.hasFDerivAt.comp z hf.hasFDerivAt).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt (φ ∘ f) (0 : F →L[ℝ] ℝ) A z :=
    (hasFDerivWithinAt_const (0 : ℝ) z A).congr_of_eventuallyEq hg0 hgz
  have := congrArg (fun L : F →L[ℝ] ℝ => L v) (hA.eq h1 h2)
  simpa using this

/-- At almost every point of a planar set A mapped into S, the differential of f takes values in
the intrinsic tangent plane of S. -/
theorem ae_fderiv_mem_tangentPlane {S : Set E₃} {f : EuclideanSpace ℝ (Fin 2) → E₃}
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hAS : ∀ z ∈ A, f z ∈ S) :
    ∀ᵐ z ∂(volume.restrict A), DifferentiableAt ℝ f z →
      ∀ v, fderiv ℝ f z v ∈ tangentPlane S (f z) := by
  filter_upwards [ae_uniqueDiffWithinAt_restrict volume A] with z hz hf v
  exact fderiv_mem_tangentPlane_of_uniqueDiffWithinAt hAS hz hf v

/-- Pointwise form: unique differentials of `A` at `z`, `f z ∈ S` and an injective differential
give range equal to the tangent plane. -/
theorem range_fderiv_eq_tangentPlane_of_uniqueDiffWithinAt {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {f : EuclideanSpace ℝ (Fin 2) → E₃}
    {A : Set (EuclideanSpace ℝ (Fin 2))} {z : EuclideanSpace ℝ (Fin 2)}
    (hAS : ∀ a ∈ A, f a ∈ S) (hA : UniqueDiffWithinAt ℝ A z) (hz : f z ∈ S)
    (hf : DifferentiableAt ℝ f z) (hinj : Function.Injective (fderiv ℝ f z)) :
    LinearMap.range (fderiv ℝ f z : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) =
      tangentPlane S (f z) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, rfl⟩
    exact fderiv_mem_tangentPlane_of_uniqueDiffWithinAt hAS hA hf v
  · rw [LinearMap.finrank_range_of_inj hinj, hS.finrank_tangentPlane hz]
    simp

/-- Measurability-free form: at almost every point of `A` that lies in `A`, an injective
differential has range the tangent plane. -/
theorem ae_range_fderiv_eq_tangentPlane_of_mem {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {f : EuclideanSpace ℝ (Fin 2) → E₃} {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hAS : ∀ z ∈ A, f z ∈ S) :
    ∀ᵐ z ∂(volume.restrict A), z ∈ A → DifferentiableAt ℝ f z →
      Function.Injective (fderiv ℝ f z) →
      LinearMap.range (fderiv ℝ f z : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) =
        tangentPlane S (f z) := by
  filter_upwards [ae_uniqueDiffWithinAt_restrict volume A] with z hz hzA hf hinj
  exact range_fderiv_eq_tangentPlane_of_uniqueDiffWithinAt hS hAS hz (hAS z hzA) hf hinj

/-- For a null-measurable planar set `A` mapped into an embedded surface, an injective
differential has range the intrinsic tangent plane at almost every point of `A`. -/
theorem ae_range_fderiv_eq_tangentPlane {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {f : EuclideanSpace ℝ (Fin 2) → E₃} {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : NullMeasurableSet A) (hAS : ∀ z ∈ A, f z ∈ S) :
    ∀ᵐ z ∂(volume.restrict A), DifferentiableAt ℝ f z → Function.Injective (fderiv ℝ f z) →
      LinearMap.range (fderiv ℝ f z : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) =
        tangentPlane S (f z) := by
  filter_upwards [ae_range_fderiv_eq_tangentPlane_of_mem hS hAS, ae_restrict_mem₀ hA]
    with z hz hzA
  exact hz hzA

end LiquidDrop
