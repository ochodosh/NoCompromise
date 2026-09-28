import NoCompromise.Area.AlmostLinear

/-!
# Uniform differentiability pieces

A carrier records the compact set, integer bounds, and common nondecreasing
modulus from the blueprint. The modulus has domain and codomain `ℝ≥0`, and tends
to zero at zero. Global Lipschitz hypotheses are imposed separately in results
that need them; the carrier conditions themselves are local to the compact set.

This module establishes restriction, local injectivity, Borel images, and local
area estimates. It does not assume or prove the Lusin–Egorov exhaustion theorem.
-/

noncomputable section

open MeasureTheory Set Module Filter
open scoped ENNReal NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A compact carrier with uniform rank-two differentiability and derivative continuity. -/
structure UniformDifferentiabilityCarrier {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) where
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  isCompact : IsCompact carrier
  bound : ℕ
  one_le_bound : 1 ≤ bound
  coordinate_le : ∀ x ∈ carrier, ∀ i : Fin 2, |x i| ≤ bound
  differentiableAt : ∀ x ∈ carrier, DifferentiableAt ℝ f x
  fderiv_norm_le : ∀ x ∈ carrier, ‖fderiv ℝ f x‖ ≤ bound
  singularValue_ge : ∀ x ∈ carrier, 1 / (bound : ℝ) ≤ (fderiv ℝ f x).singularValues 1
  modulus : ℝ≥0 → ℝ≥0
  monotone_modulus : Monotone modulus
  tendsto_modulus_zero : Tendsto modulus (𝓝 0) (𝓝 0)
  remainder_le : ∀ x ∈ carrier, ∀ y ∈ carrier,
    ‖f x - f y - fderiv ℝ f y (x - y)‖ ≤ modulus ‖x - y‖₊ * ‖x - y‖
  fderiv_sub_le : ∀ x ∈ carrier, ∀ y ∈ carrier,
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ modulus ‖x - y‖₊

/-- A Borel piece contained in one compact uniform differentiability carrier. -/
def IsUniformDifferentiabilityPiece {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (G : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  MeasurableSet G ∧ ∃ d : UniformDifferentiabilityCarrier f, G ⊆ d.carrier

lemma IsUniformDifferentiabilityPiece.mono {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {G A : Set (EuclideanSpace ℝ (Fin 2))}
    (hG : IsUniformDifferentiabilityPiece f G) (hA : MeasurableSet A) (hAG : A ⊆ G) :
    IsUniformDifferentiabilityPiece f A := by
  obtain ⟨hGm, d, hGd⟩ := hG
  exact ⟨hA, d, hAG.trans hGd⟩

/-- A continuous injection on a compact carrier sends Borel subsets to Borel sets.
The proof uses the compact-domain closed embedding, without descriptive set theory. -/
lemma measurableSet_image_of_compact_injective {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {K A : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hinj : InjOn f K)
    (hA : MeasurableSet A) (hAK : A ⊆ K) : MeasurableSet (f '' A) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hi : Function.Injective (K.domRestrict f) := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy)
  have he := (hf.domRestrict.isClosedEmbedding hi).measurableEmbedding
  have hpre : MeasurableSet ((Subtype.val : K → EuclideanSpace ℝ (Fin n)) ⁻¹' A) :=
    hA.preimage measurable_subtype_coe
  have hm := he.measurableSet_image' hpre
  convert hm using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hAK hx⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩

namespace UniformDifferentiabilityCarrier

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}

lemma bound_pos (d : UniformDifferentiabilityCarrier f) : 0 < (d.bound : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one d.one_le_bound)

lemma continuousOn (d : UniformDifferentiabilityCarrier f) : ContinuousOn f d.carrier :=
  fun x hx => (d.differentiableAt x hx).continuousAt.continuousWithinAt

lemma injective_fderiv (d : UniformDifferentiabilityCarrier f)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ d.carrier) :
    Function.Injective (fderiv ℝ f x) := by
  have hs : 0 < (fderiv ℝ f x).singularValues 1 :=
    lt_of_lt_of_le (one_div_pos.mpr d.bound_pos) (d.singularValue_ge x hx)
  apply (fderiv ℝ f x).injective_iff_forall_lt_finrank_singularValues_pos.mpr
  intro i hi
  have hi1 : i ≤ 1 := by simp only [finrank_euclideanSpace_fin] at hi; omega
  exact hs.trans_le ((fderiv ℝ f x).singularValues_antitone hi1)

lemma jacobian_pos (d : UniformDifferentiabilityCarrier f)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ d.carrier) : 0 < jacobian2 f x :=
  (jacobian2Linear_pos_iff_injective (fderiv ℝ f x)).2 (d.injective_fderiv hx)

lemma jacobian_le_sq_bound (d : UniformDifferentiabilityCarrier f)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ d.carrier) :
    jacobian2 f x ≤ (d.bound : ℝ) ^ 2 := by
  have h0 := (singularValues_zero_le_norm (fderiv ℝ f x)).trans (d.fderiv_norm_le x hx)
  have h1 := ((fderiv ℝ f x).singularValues_antitone (by norm_num : 0 ≤ 1)).trans h0
  rw [jacobian2, jacobian2Linear_eq_singularValues, pow_two]
  exact mul_le_mul h0 h1 ((fderiv ℝ f x).singularValues_nonneg 1) (by positivity)

/-- On a small set, any base derivative in the carrier is a pairwise linear model. -/
lemma pairwise_error (d : UniformDifferentiabilityCarrier f)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hBK : B ⊆ d.carrier)
    {x₀ : EuclideanSpace ℝ (Fin 2)} (hx₀ : x₀ ∈ d.carrier) {r : ℝ≥0}
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖₊ ≤ r)
    (hbase : ∀ x ∈ B, ‖x - x₀‖₊ ≤ r) :
    ∀ x ∈ B, ∀ y ∈ B,
      ‖f x - f y - fderiv ℝ f x₀ (x - y)‖ ≤ 2 * (d.modulus r : ℝ) * ‖x - y‖ := by
  intro x hx y hy
  have hr := d.remainder_le x (hBK hx) y (hBK hy)
  have hd := d.fderiv_sub_le y (hBK hy) x₀ hx₀
  have herr : ‖f x - f y - fderiv ℝ f y (x - y)‖ ≤ d.modulus r * ‖x - y‖ :=
    hr.trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.mpr (d.monotone_modulus (hdiam x hx y hy))) (norm_nonneg _))
  have hdiff : ‖(fderiv ℝ f y - fderiv ℝ f x₀) (x - y)‖ ≤ d.modulus r * ‖x - y‖ :=
    ((fderiv ℝ f y - fderiv ℝ f x₀).le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_right
        (hd.trans (NNReal.coe_le_coe.mpr (d.monotone_modulus (hbase y hy)))) (norm_nonneg _))
  have hid : f x - f y - fderiv ℝ f x₀ (x - y) =
      (f x - f y - fderiv ℝ f y (x - y)) + (fderiv ℝ f y - fderiv ℝ f x₀) (x - y) := by
    simp only [sub_apply]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)

/-- There is a positive scale at which the common modulus is as small as prescribed. -/
lemma exists_pos_modulus_lt (d : UniformDifferentiabilityCarrier f)
    {ε : ℝ} (hε : 0 < ε) : ∃ r : ℝ≥0, 0 < r ∧ (d.modulus r : ℝ) < ε := by
  have ht : Tendsto (fun r => (d.modulus r : ℝ)) (𝓝 0) (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp d.tendsto_modulus_zero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (ht.eventually (gt_mem_nhds hε))
  let r : ℝ≥0 := ⟨δ / 2, by positivity⟩
  have hr : (0 : ℝ) < r := by change 0 < δ / 2; positivity
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  apply hball
  change dist r 0 < δ
  rw [NNReal.dist_eq]
  change |δ / 2 - 0| < δ
  rw [sub_zero, abs_of_pos (by linarith : 0 < δ / 2)]
  linarith

/-- The derivative is uniformly continuous on the carrier, with the recorded modulus. -/
lemma uniformContinuousOn_fderiv (d : UniformDifferentiabilityCarrier f) :
    UniformContinuousOn (fderiv ℝ f) d.carrier := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨r, hr, hω⟩ := d.exists_pos_modulus_lt hε
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro x hx y hy hdist
  rw [dist_eq_norm] at hdist ⊢
  exact (d.fderiv_sub_le x hx y hy).trans_lt
    ((NNReal.coe_le_coe.mpr (d.monotone_modulus (by exact_mod_cast hdist.le))).trans_lt hω)

/-- The derivative, and hence the Gram Jacobian, is continuous on the compact carrier. -/
lemma continuousOn_jacobian (d : UniformDifferentiabilityCarrier f) :
    ContinuousOn (jacobian2 f) d.carrier :=
  continuous_jacobian2Linear.comp_continuousOn d.uniformContinuousOn_fderiv.continuousOn

lemma uniformContinuousOn_jacobian (d : UniformDifferentiabilityCarrier f) :
    UniformContinuousOn (jacobian2 f) d.carrier :=
  d.isCompact.uniformContinuousOn_of_continuous d.continuousOn_jacobian

/-- At this scale the perturbation error is less than half every lower singular value. -/
lemma exists_injective_scale (d : UniformDifferentiabilityCarrier f) :
    ∃ r : ℝ≥0, 0 < r ∧ 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ) := by
  obtain ⟨r, hr, hω⟩ := d.exists_pos_modulus_lt
    (div_pos (one_div_pos.mpr d.bound_pos) (by norm_num : (0 : ℝ) < 4))
  exact ⟨r, hr, by linarith⟩

/-- Every sufficiently small subset of a carrier is mapped injectively. -/
lemma injOn_of_diameter_le (d : UniformDifferentiabilityCarrier f)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hBK : B ⊆ d.carrier) {r : ℝ≥0}
    (hr : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ))
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖₊ ≤ r) : InjOn f B := by
  by_cases hB : B.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hB
    have he := d.pairwise_error hBK (hBK hx₀) hdiam (fun x hx => hdiam x hx x₀ hx₀)
    exact (almostLinear_injective_inverse (fderiv ℝ f x₀) (d.injective_fderiv (hBK hx₀))
      he (by linarith [d.singularValue_ge x₀ (hBK hx₀)])).1
  · simp only [not_nonempty_iff_eq_empty] at hB
    simp [hB]

/-- Images of Borel subsets of a sufficiently small compact portion of the carrier are Borel. -/
lemma measurableSet_image_of_subset_compact (d : UniformDifferentiabilityCarrier f)
    {T A : Set (EuclideanSpace ℝ (Fin 2))} (hT : IsCompact T) (hTK : T ⊆ d.carrier)
    {r : ℝ≥0} (hr : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ))
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖₊ ≤ r)
    (hA : MeasurableSet A) (hAT : A ⊆ T) : MeasurableSet (f '' A) :=
  measurableSet_image_of_compact_injective hT (d.continuousOn.mono hTK)
    (d.injOn_of_diameter_le hTK hr hdiam) hA hAT

/-- Local area comparison with any fixed base derivative on the compact carrier. -/
lemma local_area_bounds (d : UniformDifferentiabilityCarrier f)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hBK : B ⊆ d.carrier)
    {x₀ : EuclideanSpace ℝ (Fin 2)} (hx₀ : x₀ ∈ d.carrier) {r : ℝ≥0}
    (hr : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ))
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖₊ ≤ r)
    (hbase : ∀ x ∈ B, ‖x - x₀‖₊ ≤ r) :
    ENNReal.ofReal (jacobian2 f x₀ - 6 * d.bound * (d.modulus r : ℝ)) * volume B ≤
      hausdorffMeasure2 m (f '' B) ∧
    hausdorffMeasure2 m (f '' B) ≤
      ENNReal.ofReal (jacobian2 f x₀ + 6 * d.bound * (d.modulus r : ℝ)) * volume B := by
  have he := d.pairwise_error hBK hx₀ hdiam hbase
  have hm := almostLinear_area_bounds_uniform (fderiv ℝ f x₀) (d.injective_fderiv hx₀)
    (d.fderiv_norm_le x₀ hx₀) he (by linarith [d.singularValue_ge x₀ hx₀])
  have hc : 3 * (d.bound : ℝ) * (2 * (d.modulus r : ℝ)) =
      6 * d.bound * (d.modulus r : ℝ) := by ring
  simpa only [jacobian2, hc] using hm

/-- The compact patch with center `x` and diameter bound `r`. -/
def patch (d : UniformDifferentiabilityCarrier f) (x : EuclideanSpace ℝ (Fin 2))
    (r : ℝ≥0) : Set (EuclideanSpace ℝ (Fin 2)) :=
  d.carrier ∩ Metric.closedBall x ((r : ℝ) / 2)

lemma isCompact_patch (d : UniformDifferentiabilityCarrier f)
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ≥0) : IsCompact (d.patch x r) :=
  d.isCompact.inter_right Metric.isClosed_closedBall

lemma patch_subset (d : UniformDifferentiabilityCarrier f)
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ≥0) : d.patch x r ⊆ d.carrier :=
  inter_subset_left

lemma patch_diameter_le (d : UniformDifferentiabilityCarrier f)
    (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ≥0)
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ d.patch c r) (hy : y ∈ d.patch c r) :
    ‖x - y‖₊ ≤ r := by
  have hdist : dist x y ≤ (r : ℝ) := calc
    _ ≤ dist x c + dist c y := dist_triangle x c y
    _ ≤ (r : ℝ) / 2 + (r : ℝ) / 2 := add_le_add
      (Metric.mem_closedBall.mp hx.2)
      (by simpa only [dist_comm] using (Metric.mem_closedBall.mp hy.2))
    _ = _ := by ring
  exact_mod_cast (show ‖x - y‖ ≤ (r : ℝ) by simpa only [dist_eq_norm] using hdist)

/-- A compact carrier is covered by finitely many compact patches at every positive scale. -/
lemma exists_finite_patch_cover (d : UniformDifferentiabilityCarrier f)
    {r : ℝ≥0} (hr : 0 < r) :
    ∃ t : Finset d.carrier, d.carrier ⊆ ⋃ c ∈ t, d.patch c r := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨t, ht⟩ := d.isCompact.elim_finite_subcover
    (fun c : d.carrier => Metric.ball (c : EuclideanSpace ℝ (Fin 2)) ((r : ℝ) / 2))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by positivity)⟩)
  refine ⟨t, ?_⟩
  intro x hx
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion₂.mpr ⟨c, hct, hx, Metric.ball_subset_closedBall hxc⟩

lemma injOn_patch (d : UniformDifferentiabilityCarrier f)
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ≥0}
    (hr : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ)) : InjOn f (d.patch c r) :=
  d.injOn_of_diameter_le (d.patch_subset c r) hr (fun _ hx _ hy => d.patch_diameter_le c r hx hy)

/-- A finite compact cover on each member of which the map is injective. -/
lemma exists_finite_compact_injective_cover (d : UniformDifferentiabilityCarrier f) :
    ∃ (r : ℝ≥0) (t : Finset d.carrier), 0 < r ∧
      d.carrier ⊆ (⋃ c ∈ t, d.patch c r) ∧
      ∀ c ∈ t, IsCompact (d.patch c r) ∧ InjOn f (d.patch c r) := by
  obtain ⟨r, hr, hsmall⟩ := d.exists_injective_scale
  obtain ⟨t, ht⟩ := d.exists_finite_patch_cover hr
  exact ⟨r, t, hr, ht, fun c _ => ⟨d.isCompact_patch c r, d.injOn_patch c hsmall⟩⟩

end UniformDifferentiabilityCarrier

lemma IsUniformDifferentiabilityPiece.measure_lt_top {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsUniformDifferentiabilityPiece f G) :
    volume G < ∞ := by
  obtain ⟨hGm, d, hGd⟩ := hG
  exact (measure_mono hGd).trans_lt d.isCompact.measure_lt_top


/-- Borel subsets of a uniform piece have Borel images, using finitely many compact embeddings. -/
lemma IsUniformDifferentiabilityPiece.measurableSet_image {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsUniformDifferentiabilityPiece f G) :
    MeasurableSet (f '' G) := by
  obtain ⟨hGm, d, hGd⟩ := hG
  obtain ⟨r, t, hr, hcover, hpatch⟩ := d.exists_finite_compact_injective_cover
  have hid : f '' G = ⋃ c ∈ t, f '' (G ∩ d.patch c r) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (hcover (hGd hx))
      exact mem_iUnion₂.mpr ⟨c, hct, x, ⟨hx, hxc⟩, rfl⟩
    · intro hy
      obtain ⟨c, hct, x, hx, hxy⟩ := mem_iUnion₂.mp hy
      exact ⟨x, hx.1, hxy⟩
  rw [hid]
  apply t.measurableSet_biUnion
  intro c hc
  exact measurableSet_image_of_compact_injective (hpatch c hc).1
    (d.continuousOn.mono (d.patch_subset c r)) (hpatch c hc).2
    (hGm.inter (d.isCompact_patch c r).isClosed.measurableSet) inter_subset_right

end LiquidDrop
