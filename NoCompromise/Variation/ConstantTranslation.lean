module

public import NoCompromise.Variation.TranslationBound
public import NoCompromise.BV.DirectionalPolarCompatibility
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Weighted symmetric differences for constant translations

For a Lebesgue-measurable set of locally finite perimeter in three dimensions,
the normalized weighted symmetric difference under a constant translation has
the exact two-sided limit given by the absolute normal component integrated
against Hausdorff area on the reduced boundary. Compact continuous signed
weights are allowed; a final corollary localizes the bulk integral to any set
containing the weight's topological support.

The proof integrates the proved one-dimensional translation limits over an
orthogonal frame. A fixed compact product slab and the uniform one-dimensional
bound provide transverse dominated convergence. The actual slice measures
construct the directional derivative, and scalar distributional uniqueness
identifies its total variation with the normal-weighted reduced-boundary area.
No flow or straightening result is used.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Transverse dominated convergence for the actual slice measures. The compact
product slab supplies one integrable dominating function for both signs of shift. -/
theorem tendsto_integral_slice_weighted_translation {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} (hF : Measurable F)
    (hb : ∀ p, F p ∈ ({0, 1} : Set ℝ))
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    (hp : ∀ᵐ x, IsRealBVPolar (fun s => F (x, s)) (κ x) (σ x))
    (hBV : ∀ᵐ x, IsLocallyBVOn ((fun s => F (x, s)) ∘ euclideanOneReal) univ)
    (hκ : ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => κ x A) volume)
    (hfin : IsFiniteMeasureOnCompacts
      (sliceProductMeasure volume 0 κ (hp.mono fun _ h => h.finiteOnCompacts) hκ))
    {φ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : IsCompact B)
    {R C : ℝ} (hC : 0 ≤ C) (hφC : ∀ p, |φ p| ≤ C)
    (hsφ : Function.support φ ⊆ B ×ˢ Icc (-R) R) :
    Tendsto (fun t : ℝ => ∫ x, |t|⁻¹ * ∫ s, φ (x, s) * |F (x, s + t) - F (x, s)|)
      (𝓝[≠] 0)
      (𝓝 (∫ p, φ p ∂sliceProductMeasure volume 0 κ
        (hp.mono fun _ h => h.finiteOnCompacts) hκ)) := by
  classical
  let μp := sliceProductMeasure volume 0 κ (hp.mono fun _ h => h.finiteOnCompacts) hκ
  let : IsFiniteMeasureOnCompacts μp := hfin
  let K := Icc (-(R + 2)) (R + 2)
  let M (x : EuclideanSpace ℝ (Fin n)) := B.indicator (fun x => κ x K) x
  let D (x : EuclideanSpace ℝ (Fin n)) := C * (M x).toReal
  have hm : AEMeasurable M volume := (hκ K measurableSet_Icc).indicator hB.measurableSet
  have hmass : (∫⁻ x, M x) = μp (B ×ˢ K) := by
    rw [sliceProductMeasure_apply _ _ _ _ _ (hB.measurableSet.prod measurableSet_Icc)]
    apply lintegral_congr
    intro x
    have he : Prod.mk x ⁻¹' (B ×ˢ K) = if x ∈ B then K else ∅ := by
      ext t
      by_cases hx : x ∈ B <;> simp [hx]
    rw [he]
    by_cases hx : x ∈ B <;> simp [M, hx]
  have hD : Integrable D volume := by
    apply Integrable.const_mul
    apply integrable_toReal_of_lintegral_ne_top hm
    rw [hmass]
    exact (hB.prod isCompact_Icc).measure_lt_top.ne
  let G (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :=
    |t|⁻¹ * ∫ s, φ (x, s) * |F (x, s + t) - F (x, s)|
  have hGm (t : ℝ) : AEStronglyMeasurable (G t) volume := by
    have hh : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        φ p * |F (p.1, p.2 + t) - F p|) := by
      have hq := (hF.comp (measurable_fst.prodMk (measurable_snd.add_const t))).sub hF
      have hm := hφ.measurable.mul hq.norm
      change Measurable (fun p => φ p * ‖F (p.1, p.2 + t) - F p‖) at hm
      simpa only [Real.norm_eq_abs] using hm
    exact (hh.stronglyMeasurable.integral_prod_right'.const_mul _).aestronglyMeasurable
  have hbound (t : ℝ) (ht : |t| ≤ 1) : ∀ᵐ x, ‖G t x‖ ≤ D x := by
    filter_upwards [hp, hBV] with x hx hbx
    by_cases hxB : x ∈ B
    · have hs : Function.support (fun s => φ (x, s)) ⊆ Icc (-R) R :=
        fun s hs => (hsφ hs).2
      have hh := hx.weighted_translation_bound hbx (Eventually.of_forall fun s => hb (x, s))
        hC (fun s => hφC (x, s)) hs ht
      simpa only [G, D, M, indicator_of_mem hxB, Real.norm_eq_abs, measureReal_def] using hh
    · have hz (s : ℝ) : φ (x, s) = 0 := by
        by_contra hs
        exact hxB (hsφ hs).1
      simp [G, hz, D, M, hxB]
  have hlim : ∀ᵐ x, Tendsto (fun t => G t x) (𝓝[≠] 0)
      (𝓝 (∫ s, φ (x, s) ∂κ x)) := by
    filter_upwards [hp, hBV] with x hx hbx
    have hc : HasCompactSupport (fun s => φ (x, s)) := by
      apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R))
      intro s hs
      by_contra hn
      exact hs (hsφ hn).2
    exact hx.tendsto_weighted_translation hbx (Eventually.of_forall fun s => hb (x, s))
      (hφ.comp (continuous_const.prodMk continuous_id)) hc
  have hnear : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ 1 := by
    have ht := (continuous_abs.continuousAt (x := (0 : ℝ))).eventually
      (Iio_mem_nhds (by norm_num : |(0 : ℝ)| < 1))
    exact (ht.filter_mono nhdsWithin_le_nhds).mono fun _ ht => ht.le
  have ht := tendsto_integral_filter_of_dominated_convergence D
    (Eventually.of_forall hGm) (hnear.mono hbound) hD hlim
  have hi := integral_sliceProductMeasure volume 0 κ
    (hp.mono fun _ h => h.finiteOnCompacts) hκ hφ.measurable
    (hφ.integrable_of_hasCompactSupport hcφ (μ := μp))
  rwa [← hi.2.2] at ht

lemma jumpCoordinateHomeomorph_measurePreserving {n : ℕ}
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    MeasurePreserving (jumpCoordinateHomeomorph n e) (volume.prod volume) volume := by
  have h := e.measurePreserving.comp
    (((euclideanLastEquiv_measurePreserving n).symm
      (euclideanLastEquiv n).toHomeomorph.toMeasurableEquiv).comp
        (Measure.measurePreserving_swap (μ := volume) (ν := volume)))
  exact h

lemma jumpCoordinateHomeomorph_add_last {n : ℕ}
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (s t : ℝ) :
    jumpCoordinateHomeomorph n e (x, s + t) = jumpCoordinateHomeomorph n e (x, s) +
      t • e (EuclideanSpace.single (Fin.last n) 1) := by
  simp only [jumpCoordinateHomeomorph_apply, graphAppendN, add_smul, map_add, map_smul]
  abel

lemma IsDirectionalJumpDisintegration.measure_eq_map_sliceProductMeasure {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g) :
    τ = (sliceProductMeasure volume 0 κ
      (h.slices.mono fun _ hx => hx.1.finiteOnCompacts) h.measurable_evaluation).map
        (jumpCoordinateHomeomorph n e) := by
  ext A hA
  rw [h.variation_eq A hA, Measure.map_apply (jumpCoordinateHomeomorph n e).measurable hA,
    sliceProductMeasure_apply _ _ _ _ _ ((jumpCoordinateHomeomorph n e).measurable hA)]
  rfl

lemma abs_sub_le_one_of_binary {u v : ℝ}
    (hu : u ∈ ({0, 1} : Set ℝ)) (hv : v ∈ ({0, 1} : Set ℝ)) : |u - v| ≤ 1 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> norm_num

lemma integrable_weighted_binary_difference {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ζ F G : α → ℝ} (hζ : Integrable ζ μ)
    (hF : Measurable F) (hG : Measurable G)
    (hbF : ∀ x, F x ∈ ({0, 1} : Set ℝ)) (hbG : ∀ x, G x ∈ ({0, 1} : Set ℝ)) :
    Integrable (fun x => ζ x * |F x - G x|) μ := by
  apply hζ.norm.mono'
  · have hh := hζ.aestronglyMeasurable.mul
      (hF.sub hG).stronglyMeasurable.norm.aestronglyMeasurable
    change AEStronglyMeasurable (fun x => ζ x * ‖F x - G x‖) μ at hh
    simpa only [Real.norm_eq_abs] using hh
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      simpa only [mul_one, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (abs_sub_le_one_of_binary (hbF x) (hbG x)) (abs_nonneg (ζ x))

/-- A binary BV translation in a fixed unit coordinate direction converges to
its actual directional variation, with an arbitrary compact continuous weight. -/
theorem IsDirectionalJumpDisintegration.tendsto_weighted_translation {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g)
    (hf : IsLocallyBVOn f univ) (hm : Measurable f)
    (hb : ∀ z, f z ∈ ({0, 1} : Set ℝ))
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ z, ζ z *
      |f (z + t • e (EuclideanSpace.single (Fin.last n) 1)) - f z|)
      (𝓝[≠] 0) (𝓝 (∫ z, ζ z ∂τ)) := by
  let H := jumpCoordinateHomeomorph n e
  let F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := f ∘ H
  let φ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := ζ ∘ H
  have hF : Measurable F := hm.comp H.measurable
  have hφ : Continuous φ := hζ.comp H.continuous
  have hcφ : HasCompactSupport φ := hcζ.comp_homeomorph H
  have hp : ∀ᵐ x, IsRealBVPolar (fun t => F (x, t)) (κ x) (σ x) :=
    h.slices.mono fun _ hx => hx.1
  let μp := sliceProductMeasure volume 0 κ (hp.mono fun _ h => h.finiteOnCompacts)
    h.measurable_evaluation
  have hfe := hf.comp_linearIsometryEquiv_univ e
  have hBV : ∀ᵐ x, IsLocallyBVOn ((fun t => F (x, t)) ∘ euclideanOneReal) univ := by
    filter_upwards [hfe.ae_lineSlice] with x hx
    change IsLocallyBVOn (lineSlice (f ∘ e) x) univ
    exact hx
  have hfin : IsFiniteMeasureOnCompacts μp := hfe.isFiniteMeasureOnCompacts_sliceProductMeasure
    (h.slices.mono fun _ hx => hx.1) h.measurable_evaluation
  let B := Prod.fst '' tsupport φ
  have hB : IsCompact B := hcφ.image continuous_fst
  obtain ⟨R, hR⟩ := (hcφ.image continuous_snd).isBounded.subset_closedBall (0 : ℝ)
  have hsφ : Function.support φ ⊆ B ×ˢ Icc (-R) R := by
    intro p hp
    refine ⟨mem_image_of_mem Prod.fst (subset_tsupport φ hp), ?_⟩
    have hh := hR (mem_image_of_mem Prod.snd (subset_tsupport φ hp))
    rw [mem_closedBall, Real.dist_eq, sub_zero] at hh
    exact abs_le.mp hh
  obtain ⟨C₀, hC₀⟩ := (hcφ.image hφ).isBounded.subset_closedBall (0 : ℝ)
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hφC (p) : |φ p| ≤ C := by
    by_cases hz : φ p = 0
    · simpa only [hz, abs_zero] using hC
    · have hh := hC₀ (mem_image_of_mem φ (subset_tsupport φ hz))
      rw [mem_closedBall, Real.dist_eq, sub_zero] at hh
      exact hh.trans (le_max_left _ _)
  have ht := tendsto_integral_slice_weighted_translation hF (fun p => hb (H p))
    hp hBV h.measurable_evaluation hfin hφ hcφ hB hC hφC hsφ
  have hrhs : (∫ p, φ p ∂μp) = ∫ z, ζ z ∂τ := by
    rw [h.measure_eq_map_sliceProductMeasure,
      (jumpCoordinateHomeomorph n e).measurableEmbedding.integral_map]
    rfl
  rw [hrhs] at ht
  have heq (t : ℝ) :
      (∫ x, |t|⁻¹ * ∫ u, φ (x, u) * |F (x, u + t) - F (x, u)|) =
      |t|⁻¹ * ∫ z, ζ z * |f (z + t • e (EuclideanSpace.single (Fin.last n) 1)) - f z| := by
    have hi : Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        φ p * |F (p.1, p.2 + t) - F p|) (volume.prod volume) :=
      integrable_weighted_binary_difference (hφ.integrable_of_hasCompactSupport hcφ)
        (hF.comp (measurable_fst.prodMk (measurable_snd.add_const t))) hF
        (fun p => hb (H (p.1, p.2 + t))) (fun p => hb (H p))
    rw [integral_const_mul, integral_integral hi]
    congr 1
    have he := (jumpCoordinateHomeomorph_measurePreserving e).integral_comp
      H.measurableEmbedding (fun z => ζ z *
        |f (z + t • e (EuclideanSpace.single (Fin.last n) 1)) - f z|)
    convert he using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      change φ p * |F (p.1, p.2 + t) - F p| = _
      rw [show F (p.1, p.2 + t) = f (H p + t • e (EuclideanSpace.single (Fin.last n) 1))
        from congrArg f (jumpCoordinateHomeomorph_add_last e p.1 p.2 t)]
      rfl
  simpa only [heq] using ht

lemma integral_weighted_vector_translation_congr_ae {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hfg : f =ᵐ[volume] g)
    (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    (∫ z, ζ z * |f (z + a) - f z|) = ∫ z, ζ z * |g (z + a) - g z| := by
  have ha : (fun z => f (z + a)) =ᵐ[volume] (fun z => g (z + a)) := by
    simpa only [Function.comp_def, add_comm a] using
      (quasiMeasurePreserving_add_left volume a).ae_eq_comp hfg
  apply integral_congr_ae
  filter_upwards [hfg, ha] with z hz hza
  rw [hz, hza]

/-- The exact constant-vector symmetric-difference limit. The set is only
Lebesgue measurable, and the reduced-boundary normal and area are the actual
ones constructed by the De Giorgi theorem. Signed compact continuous weights
are allowed, so in particular this includes nonnegative weights. -/
theorem HasLocallyFinitePerimeter.tendsto_weighted_constant_translation
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (a : AmbientSpace)
    {ζ : AmbientSpace → ℝ} (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ z, ζ z *
      |E.indicator (fun _ => (1 : ℝ)) (z - t • a) - E.indicator (fun _ => (1 : ℝ)) z|)
      (𝓝[≠] 0)
      (𝓝 (∫ z in reducedBoundary E hE hmE,
        ζ z * |inner ℝ a (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3)) := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  let v : AmbientSpace := ‖a‖⁻¹ • a
  have hv : ‖v‖ = 1 := norm_smul_inv_norm ha
  have hav : ‖a‖ • v = a := by simp [v, smul_smul, hna]
  let f := E.indicator (fun _ => (1 : ℝ))
  let B := toMeasurable volume E
  let b := B.indicator (fun _ => (1 : ℝ))
  have hbf : b =ᵐ[volume] f := indicator_ae_eq_of_ae_eq_set hmE.toMeasurable_ae_eq
  have hb : IsLocallyBVOn b univ :=
    (hE.isLocallyBVOn_indicator hmE univ).congr_ae (by simpa using hbf.symm)
  have hbm : Measurable b := measurable_const.indicator (measurableSet_toMeasurable volume E)
  have hbb (z) : b z ∈ ({0, 1} : Set ℝ) := by
    by_cases hz : z ∈ B <;> simp [b, hz]
  obtain ⟨e, he⟩ := exists_line_direction_frame hv
  obtain ⟨τ, s, κ, σ, g, h⟩ := hb.exists_directionalJumpDisintegration hbm hbb e
  have ht := h.tendsto_weighted_translation hb hbm hbb hζ hcζ
  rw [he] at ht
  have hpol : IsDirectionalBVPolar f v τ s := by
    simpa only [he] using (h.congr_ae hbf).polar
  have hshift (t : ℝ) :
      (∫ z, ζ z * |b (z + t • v) - b z|) = ∫ z, ζ z * |f (z + t • v) - f z| :=
    integral_weighted_vector_translation_congr_ae hbf ζ (t • v)
  simp_rw [hshift] at ht
  have hparam : Tendsto (fun t : ℝ => -t * ‖a‖) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((continuous_id.neg.mul_const ‖a‖).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [hna] using ht
  have htt := (ht.comp hparam).const_mul ‖a‖
  have hrhs : ‖a‖ * (∫ z, ζ z ∂τ) =
      ∫ z in reducedBoundary E hE hmE, ζ z *
        |inner ℝ a (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3 := by
    rw [hpol.integral_eq_reducedBoundary_normal_component hE hmE ζ, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      have hi : inner ℝ a (reducedNormal E hE hmE z) =
          ‖a‖ * inner ℝ v (reducedNormal E hE hmE z) := by
        nth_rw 1 [← hav]
        rw [real_inner_smul_left]
      change ‖a‖ * (ζ z * |inner ℝ v (reducedNormal E hE hmE z)|) =
        ζ z * |inner ℝ a (reducedNormal E hE hmE z)|
      rw [hi, abs_mul, abs_of_nonneg (norm_nonneg a)]
      ring
  rw [hrhs] at htt
  apply htt.congr'
  exact Eventually.of_forall fun t => by
    have hvec : (-t * ‖a‖) • v = -(t • a) := by
      rw [mul_smul, hav, neg_smul]
    have hcoef : ‖a‖ * |-t * ‖a‖|⁻¹ = |t|⁻¹ := by
      rw [abs_mul, abs_neg, abs_of_nonneg (norm_nonneg a), mul_inv_rev,
        ← mul_assoc, mul_inv_cancel₀ hna, one_mul]
    change ‖a‖ * (|-t * ‖a‖|⁻¹ *
      (∫ z, ζ z * |f (z + (-t * ‖a‖) • v) - f z|)) = _
    rw [← mul_assoc, hcoef]
    simp only [hvec, ← sub_eq_add_neg, f]

/-- The blueprint's localized formulation for a compactly supported weight in `U`. -/
theorem HasLocallyFinitePerimeter.tendsto_weighted_constant_translation_on
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (a : AmbientSpace)
    {U : Set AmbientSpace} {ζ : AmbientSpace → ℝ}
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ z in U, ζ z *
      |E.indicator (fun _ => (1 : ℝ)) (z - t • a) - E.indicator (fun _ => (1 : ℝ)) z|)
      (𝓝[≠] 0)
      (𝓝 (∫ z in reducedBoundary E hE hmE,
        ζ z * |inner ℝ a (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3)) := by
  have he (t : ℝ) : (∫ z in U, ζ z *
      |E.indicator (fun _ => (1 : ℝ)) (z - t • a) - E.indicator (fun _ => (1 : ℝ)) z|) =
      ∫ z, ζ z *
      |E.indicator (fun _ => (1 : ℝ)) (z - t • a) - E.indicator (fun _ => (1 : ℝ)) z| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun hz' => hz (hsζ hz')), zero_mul]
  simpa only [he] using hE.tendsto_weighted_constant_translation hmE a hζ hcζ

end LiquidDrop
