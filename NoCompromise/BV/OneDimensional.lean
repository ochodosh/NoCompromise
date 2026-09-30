module

public import NoCompromise.Measure.CumulativeDerivative
public import NoCompromise.BV.LineDistribution
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

@[expose] public section

/-!
# One-dimensional BV representatives and finite jumps

An integrable signed derivative density has a left-continuous cumulative
primitive of classical bounded variation. Distributional constancy identifies
this primitive, up to a constant, with a distributionally BV function. Compact
cutoffs give representatives on arbitrary bounded intervals; left continuity
makes them pointwise unique on overlaps.

For binary almost-everywhere functions these representatives are binary at
interior points, and their nonzero jumps are finite on compact subintervals.
The final theorem applies this construction to almost every line in any fixed
unit direction. Identifying the derivative measures with the signed jump sums
is a separate remaining step of the slicing theorem.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma boundedVariationOn_sub_real {f g : ℝ → ℝ} {S : Set ℝ}
    (hf : BoundedVariationOn f S) (hg : BoundedVariationOn g S) :
    BoundedVariationOn (fun x => f x - g x) S := by
  have hbound : eVariationOn (fun x => f x - g x) S ≤ eVariationOn f S + eVariationOn g S := by
    apply iSup_le
    rintro ⟨N, u, hu, hus⟩
    calc
      _ ≤ ∑ i ∈ Finset.range N,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [edist_dist]
        rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        exact ENNReal.ofReal_le_ofReal (dist_sub_sub_le _ _ _ _)
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)
  exact (hbound.trans_lt (ENNReal.add_lt_top.mpr ⟨hf.lt_top, hg.lt_top⟩)).ne

/-- A signed integrable density has a primitive of classical bounded variation. -/
lemma boundedVariationOn_integral_sublevel {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w a : α → ℝ} (hw : Integrable w μ) (ha : Measurable a) :
    BoundedVariationOn (fun t : ℝ => ∫ x in {x | a x < t}, w x ∂μ) univ := by
  let p : α → ℝ := fun x => max (w x) 0
  let q : α → ℝ := fun x => max (-w x) 0
  have hp : Integrable p μ := hw.pos_part
  have hq : Integrable q μ := hw.neg.pos_part
  have hmono {v : α → ℝ} (hi : Integrable v μ) (hv : ∀ x, 0 ≤ v x) :
      Monotone (fun t : ℝ => ∫ x in {x | a x < t}, v x ∂μ) := by
    intro s t hst
    apply setIntegral_mono_set hi.integrableOn (ae_of_all _ hv)
    exact ae_of_all _ fun x hx => hx.trans_le hst
  have hb {v : α → ℝ} (hi : Integrable v μ) (hv : ∀ x, 0 ≤ v x) (t : ℝ) :
      |∫ x in {x | a x < t}, v x ∂μ| ≤ ∫ x, v x ∂μ := by
    rw [abs_of_nonneg (setIntegral_nonneg (measurableSet_lt ha measurable_const) (fun x _ => hv x))]
    exact setIntegral_le_integral hi (ae_of_all _ hv)
  have hpv : BoundedVariationOn (fun t : ℝ => ∫ x in {x | a x < t}, p x ∂μ) univ :=
    (hmono hp (fun x => le_max_right _ _)).monotoneOn _ |>.boundedVariationOn
      (fun t _ => hb hp (fun x => le_max_right _ _) t)
  have hqv : BoundedVariationOn (fun t : ℝ => ∫ x in {x | a x < t}, q x ∂μ) univ :=
    (hmono hq (fun x => le_max_right _ _)).monotoneOn _ |>.boundedVariationOn
      (fun t _ => hb hq (fun x => le_max_right _ _) t)
  have heq (t : ℝ) : (∫ x in {x | a x < t}, w x ∂μ) =
      (∫ x in {x | a x < t}, p x ∂μ) - ∫ x in {x | a x < t}, q x ∂μ := by
    rw [← integral_sub hp.integrableOn hq.integrableOn]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp [p, q]
      by_cases hx : 0 ≤ w x <;> simp only [max_def] <;> split_ifs <;> linarith
  simpa only [← heq] using boundedVariationOn_sub_real hpv hqv

lemma continuousWithinAt_integral_sublevel_left {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w a : α → ℝ} (hw : Integrable w μ) (ha : Measurable a) (t : ℝ) :
    ContinuousWithinAt (fun s : ℝ => ∫ x in {x | a x < s}, w x ∂μ) (Iic t) t := by
  have hi (s : ℝ) : AEStronglyMeasurable ({x | a x < s}.indicator w) μ :=
    hw.aestronglyMeasurable.indicator (measurableSet_lt ha measurable_const)
  have hb (s : ℝ) : ∀ᵐ x ∂μ, ‖{x | a x < s}.indicator w x‖ ≤ ‖w x‖ :=
    ae_of_all _ fun x => norm_indicator_le_norm_self _ _
  have ht : ∀ᵐ x ∂μ, Tendsto (fun s : ℝ => {x | a x < s}.indicator w x)
      (𝓝[≤] t) (𝓝 ({x | a x < t}.indicator w x)) := by
    apply ae_of_all
    intro x
    by_cases hx : a x < t
    · apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds] with s hs
      simp [Set.indicator, hx, hs]
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hxs : ¬a x < s := fun h => hx (h.trans_le hs)
      change {x | a x < t}.indicator w x = {x | a x < s}.indicator w x
      simp [Set.indicator, hx, hxs]
  have hh := tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖)
    (Eventually.of_forall hi) (Eventually.of_forall hb) hw.norm ht
  change Tendsto _ (𝓝[≤] t) (𝓝 _)
  simpa only [integral_indicator (measurableSet_lt ha measurable_const)] using hh

/-- A distribution represented by an integrable signed density has a left-continuous
classical BV primitive, equal almost everywhere to any locally integrable weak primitive. -/
theorem exists_boundedVariationOn_ae_eq_of_weak_primitive {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {w a : α → ℝ} (hw : Integrable w μ) (ha : Measurable a)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ t, f t * deriv ψ t) = -(∫ x, ψ (a x) * w x ∂μ)) :
    ∃ g : ℝ → ℝ, BoundedVariationOn g univ ∧
      (∀ t, ContinuousWithinAt g (Iic t) t) ∧ f =ᵐ[volume] g := by
  let F : ℝ → ℝ := fun t => ∫ x in {x | a x < t}, w x ∂μ
  have hBV : BoundedVariationOn F univ := boundedVariationOn_integral_sublevel hw ha
  have hm : Measurable F := measurable_of_countable_not_continuousAt
    hBV.countable_not_continuousAt
  have hi : LocallyIntegrable F volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    apply Integrable.mono (integrableOn_const (C := ∫ x, ‖w x‖ ∂μ) hK.measure_ne_top)
      hm.aestronglyMeasurable.restrict
    apply ae_of_all
    intro t
    exact ((norm_integral_le_integral_norm _).trans
      (setIntegral_le_integral hw.norm (ae_of_all _ fun _ => norm_nonneg _))).trans
        (le_abs_self _)
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero isOpen_univ isPreconnected_univ
    ((hf.sub hi).locallyIntegrableOn univ) (by
      intro ψ hψ hcψ _
      change (∫ t in univ, (f t - F t) * deriv ψ t) = 0
      have hif : Integrable (fun t => f t * deriv ψ t) volume := by
        simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport
          (hψ.continuous_deriv le_rfl) hcψ.deriv
      have hiF : Integrable (fun t => F t * deriv ψ t) volume := by
        simpa only [smul_eq_mul] using hi.integrable_smul_right_of_hasCompactSupport
          (hψ.continuous_deriv le_rfl) hcψ.deriv
      simp only [setIntegral_univ, sub_mul]
      rw [integral_sub hif hiF, hweak ψ hψ hcψ, integral_cumulative_mul_deriv μ hw ha hψ hcψ,
        sub_self])
  refine ⟨fun t => F t + c, ?_, ?_, ?_⟩
  · exact (isometry_add_right c).lipschitzWith.comp_boundedVariationOn hBV
  · intro t
    exact (continuousWithinAt_integral_sublevel_left hw ha t).add_const c
  · have hc' : (fun t => f t - F t) =ᵐ[volume] fun _ => c := by
      change (fun t => f t - F t) =ᵐ[volume.restrict univ] fun _ => c at hc
      simpa only [Measure.restrict_univ] using hc
    exact hc'.mono fun t ht => by dsimp only at ht ⊢; linarith

/-- Distributional BV on the line has a left-continuous classical BV representative. -/
theorem IsBVOn.exists_boundedVariationOn_representative
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : IsBVOn f univ) :
    ∃ g : ℝ → ℝ, BoundedVariationOn g univ ∧
      (∀ t, ContinuousWithinAt g (Iic t) t) ∧
      (f ∘ euclideanOneReal.symm) =ᵐ[volume] g := by
  have hlocal := isLocallyBVOn_of_variation_lt_top isOpen_univ
    hf.1.locallyIntegrableOn hf.2
  obtain ⟨ρ, σ, hρ, hpol, hvar⟩ := exists_polar_representation_with_variation isOpen_univ hlocal
  have hmass : ρ univ = variation f univ := by
    simpa only [preimage_univ] using (hvar univ isOpen_univ (subset_refl _)).symm
  let : IsFiniteMeasure ρ := ⟨by rw [hmass]; exact hf.2⟩
  have hw : Integrable (fun x => σ x 0) ρ :=
    Integrable.of_bound ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).measurable.comp
      hpol.measurable).aestronglyMeasurable 1
      (hpol.norm_ae.mono fun x hx => (PiLp.norm_apply_le (σ x) 0).trans_eq hx)
  have ha : Measurable (fun x : (univ : Set (EuclideanSpace ℝ (Fin 1))) =>
      euclideanOneReal x) := euclideanOneReal.continuous.measurable.comp measurable_subtype_coe
  have hif := integrableOn_univ.mp hf.1
  have hi : LocallyIntegrable (f ∘ euclideanOneReal.symm) volume :=
    ((euclideanOneReal.symm.measurePreserving.integrable_comp hif.aestronglyMeasurable).mpr
      hif).locallyIntegrable
  apply exists_boundedVariationOn_ae_eq_of_weak_primitive ρ hw ha hi
  intro ψ hψ hcψ
  let φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
    ⟨⟨ψ ∘ euclideanOneReal, hψ.continuous.comp euclideanOneReal.continuous⟩,
      hcψ.comp_homeomorph euclideanOneReal.toHomeomorph⟩
  have hφ : ContDiff ℝ 1 φ := hψ.comp euclideanOneReal.toContinuousLinearEquiv.contDiff
  have ht := hpol.test_eq 0 φ hφ (subset_univ _)
  have hd (x : EuclideanSpace ℝ (Fin 1)) :
      fderiv ℝ φ x (EuclideanSpace.single 0 1) = deriv ψ (euclideanOneReal x) := by
    have he : HasFDerivAt (fun y => euclideanOneReal y)
        euclideanOneReal.toContinuousLinearEquiv.toContinuousLinearMap x :=
      euclideanOneReal.toContinuousLinearEquiv.hasFDerivAt
    have hh := (hψ.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x he
    change fderiv ℝ (ψ ∘ euclideanOneReal) x (EuclideanSpace.single 0 1) = _
    rw [hh.fderiv]
    simp [smul_apply, smul_eq_mul]
  simp only [Measure.restrict_univ, hd] at ht
  have he := euclideanOneReal.measurePreserving.integral_comp
    euclideanOneReal.toHomeomorph.measurableEmbedding
    (fun t => f (euclideanOneReal.symm t) * deriv ψ t)
  simp only [euclideanOneReal.symm_apply_apply] at he
  change -(∫ x, f x * deriv ψ (euclideanOneReal x)) =
    (∫ x : (univ : Set (EuclideanSpace ℝ (Fin 1))), ψ (euclideanOneReal x) * σ x 0 ∂ρ) at ht
  rw [he] at ht
  simpa only [Function.comp_def, neg_neg] using congrArg Neg.neg ht

/-- Left continuity upgrades an almost-everywhere closed-range condition on an interval
at every point accessible from the left inside that interval. -/
lemma mem_closed_of_continuousWithinAt_left_of_ae {g : ℝ → ℝ} {a b x : ℝ} {S : Set ℝ}
    (hS : IsClosed S) (hax : a < x) (hxb : x ≤ b)
    (hc : ContinuousWithinAt g (Iic x) x)
    (hAE : ∀ᵐ t ∂volume.restrict (Ioo a b), g t ∈ S) : g x ∈ S := by
  let T := Ioo a x ∩ g ⁻¹' S
  have hx : x ∈ closure T := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have haε : max a (x - ε) < x := max_lt hax (by linarith)
    have hpos : volume (Ioo (max a (x - ε)) x) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr haε))
    have hsub : Ioo (max a (x - ε)) x ⊆ Ioo a b :=
      fun t ht => ⟨(le_max_left _ _).trans_lt ht.1, ht.2.trans_le hxb⟩
    obtain ⟨t, ht, hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae_restrict_of_subset hsub hAE)
    refine ⟨t, ⟨⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩, hg⟩, ?_⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.2)]
    have := (le_max_right a (x - ε)).trans_lt ht.1
    linarith
  have h : g x ∈ closure S := (hc.mono (show T ⊆ Iic x from fun t ht => ht.1.2.le)).mem_closure
    hx (fun _ ht => ht.2)
  rwa [hS.closure_eq] at h

/-- Left-continuous representatives of the same almost-everywhere function agree
pointwise in the interior of their common interval. -/
lemma eqOn_Ioo_of_left_continuous_ae_eq {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Ioo a b, ContinuousWithinAt f (Iic x) x)
    (hg : ∀ x ∈ Ioo a b, ContinuousWithinAt g (Iic x) x)
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) : EqOn f g (Ioo a b) := by
  intro x hx
  have hAE : ∀ᵐ t ∂volume.restrict (Ioo a b), f t - g t ∈ ({0} : Set ℝ) :=
    hfg.mono fun t ht => by simp [ht]
  have h := mem_closed_of_continuousWithinAt_left_of_ae isClosed_singleton hx.1 hx.2.le
    ((hf x hx).sub (hg x hx)) hAE
  exact sub_eq_zero.mp h

lemma eventually_eq_of_tendsto_binary {ι : Type*} {l : Filter ι} [l.NeBot]
    {g : ι → ℝ} {c : ℝ} (hg : ∀ᶠ t in l, g t ∈ ({0, 1} : Set ℝ))
    (ht : Tendsto g l (𝓝 c)) : ∀ᶠ t in l, g t = c := by
  have hc : c ∈ ({0, 1} : Set ℝ) := (Set.toFinite ({0, 1} : Set ℝ)).isClosed.mem_of_tendsto ht hg
  have hd : ∀ᶠ t in l, dist (g t) c < (1 / 2 : ℝ) :=
    ht.eventually (Metric.ball_mem_nhds _ (by norm_num))
  filter_upwards [hg, hd] with t hgt hdt
  simp only [mem_insert_iff, mem_singleton_iff] at hc hgt
  rcases hc with rfl | rfl <;> rcases hgt with h | h <;> simp_all <;> norm_num at *

/-- A classical BV function taking only two values near a point is constant on
each side sufficiently near that point. Thus only the center can be discontinuous there. -/
lemma exists_nhds_continuousAt_except_self_of_binary_bv {g : ℝ → ℝ} {U : Set ℝ}
    (hg : BoundedVariationOn g univ) (hU : IsOpen U)
    (hb : ∀ x ∈ U, g x ∈ ({0, 1} : Set ℝ)) {x : ℝ} (hx : x ∈ U) :
    ∃ δ > 0, ∀ y : ℝ, dist y x < δ → y ≠ x → ContinuousAt g y := by
  have hnear : ∀ᶠ y in 𝓝 x, g y ∈ ({0, 1} : Set ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hb y hy
  have hl := eventually_eq_of_tendsto_binary
    (hnear.filter_mono (nhdsWithin_le_nhds : 𝓝[<] x ≤ 𝓝 x)) (hg.tendsto_leftLim x)
  have hr := eventually_eq_of_tendsto_binary
    (hnear.filter_mono (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x)) (hg.tendsto_rightLim x)
  obtain ⟨δl, hδl, hgl⟩ := Metric.mem_nhdsWithin_iff.mp hl
  obtain ⟨δr, hδr, hgr⟩ := Metric.mem_nhdsWithin_iff.mp hr
  refine ⟨min δl δr, lt_min hδl hδr, fun y hy hyx => ?_⟩
  rcases lt_or_gt_of_ne hyx with hlt | hgt
  · have hyV : y ∈ Metric.ball x δl ∩ Iio x :=
      ⟨hy.trans_le (min_le_left _ _), hlt⟩
    have heq : g =ᶠ[𝓝 y] fun _ => Function.leftLim g x := by
      filter_upwards [(isOpen_ball.inter isOpen_Iio).mem_nhds hyV] with z hz
      exact hgl hz
    exact heq.continuousAt
  · have hyV : y ∈ Metric.ball x δr ∩ Ioi x :=
      ⟨hy.trans_le (min_le_right _ _), hgt⟩
    have heq : g =ᶠ[𝓝 y] fun _ => Function.rightLim g x := by
      filter_upwards [(isOpen_ball.inter isOpen_Ioi).mem_nhds hyV] with z hz
      exact hgr hz
    exact heq.continuousAt

/-- Binary classical BV functions have only finitely many discontinuities on compact
subsets of their binary-valued open region. -/
theorem finite_discontinuities_binary_bv {g : ℝ → ℝ} {U K : Set ℝ}
    (hg : BoundedVariationOn g univ) (hU : IsOpen U)
    (hb : ∀ x ∈ U, g x ∈ ({0, 1} : Set ℝ)) (hK : IsCompact K) (hKU : K ⊆ U) :
    {x ∈ K | ¬ContinuousAt g x}.Finite := by
  classical
  have hex (x : K) := exists_nhds_continuousAt_except_self_of_binary_bv hg hU hb (hKU x.2)
  choose δ hδ hd using hex
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x (δ x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using hδ ⟨x, hx⟩⟩)
  apply (s.finite_toSet.image (fun x : K => (x : ℝ))).subset
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx.1)
  have heq : x = y := by
    by_contra hne
    exact hx.2 (hd y x hxy hne)
  exact ⟨y, hy, heq.symm⟩

/-- For a left-continuous BV representative of a binary almost-everywhere function,
all discontinuities on a compact subinterval form a finite set. -/
theorem finite_discontinuities_of_binary_ae_bv {g : ℝ → ℝ} {a b : ℝ} {K : Set ℝ}
    (hg : BoundedVariationOn g univ) (hc : ∀ x, ContinuousWithinAt g (Iic x) x)
    (hb : ∀ᵐ x ∂volume.restrict (Ioo a b), g x ∈ ({0, 1} : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ Ioo a b) :
    {x ∈ K | ¬ContinuousAt g x}.Finite := by
  apply finite_discontinuities_binary_bv hg isOpen_Ioo _ hK hKU
  intro x hx
  exact mem_closed_of_continuousWithinAt_left_of_ae
    (Set.toFinite ({0, 1} : Set ℝ)).isClosed hx.1 hx.2.le (hc x) hb

/-- On every bounded open interval, a locally distributionally BV function agrees
almost everywhere with a left-continuous classical BV function. -/
theorem IsLocallyBVOn.exists_boundedVariationOn_representative_Ioo
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : IsLocallyBVOn f univ) (a b : ℝ) :
    ∃ g : ℝ → ℝ, BoundedVariationOn g univ ∧
      (∀ t, ContinuousWithinAt g (Iic t) t) ∧
      (f ∘ euclideanOneReal.symm) =ᵐ[volume.restrict (Ioo a b)] g := by
  let R := |a| + |b| + 1
  let κ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) :=
    ⟨R, R + 1, by dsimp [R]; positivity, by linarith⟩
  have hκ : IsBVOn (fun z => κ z * f z) univ :=
    hf.isBVOn_mul_compact_factor isOpen_univ κ.contDiff κ.hasCompactSupport (subset_univ _)
  obtain ⟨g, hg, hc, he⟩ := hκ.exists_boundedVariationOn_representative
  refine ⟨g, hg, hc, ?_⟩
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioo] with t ht htab
  have htR : |t| ≤ R := by
    rw [abs_le]
    constructor
    · have := neg_abs_le a
      have := abs_nonneg b
      dsimp [R]
      linarith [htab.1]
    · have := le_abs_self b
      have := abs_nonneg a
      dsimp [R]
      linarith [htab.2]
  have hmem : euclideanOneReal.symm t ∈ closedBall 0 κ.rIn := by
    simpa only [mem_closedBall, dist_zero_right, euclideanOneReal.symm.norm_map,
      Real.norm_eq_abs] using htR
  simpa only [Function.comp_def, κ.one_of_mem_closedBall hmem, one_mul] using ht

/-- Binary locally BV functions have locally unique left-continuous representatives
whose discontinuities are finite on each compact subinterval. -/
theorem IsLocallyBVOn.exists_binary_representative_Ioo
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : IsLocallyBVOn f univ)
    (hb : ∀ᵐ t : ℝ, f (euclideanOneReal.symm t) ∈ ({0, 1} : Set ℝ)) (a b : ℝ) :
    ∃ g : ℝ → ℝ, BoundedVariationOn g univ ∧
      (∀ t, ContinuousWithinAt g (Iic t) t) ∧
      (f ∘ euclideanOneReal.symm) =ᵐ[volume.restrict (Ioo a b)] g ∧
      (∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ)) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b → {x ∈ K | ¬ContinuousAt g x}.Finite := by
  obtain ⟨g, hg, hc, he⟩ := hf.exists_boundedVariationOn_representative_Ioo a b
  have hgb : ∀ᵐ t ∂volume.restrict (Ioo a b), g t ∈ ({0, 1} : Set ℝ) := by
    filter_upwards [ae_restrict_of_ae hb, he] with t ht hteq
    exact hteq ▸ ht
  refine ⟨g, hg, hc, he, ?_, fun K hK hKU =>
    finite_discontinuities_of_binary_ae_bv hg hc hgb hK hKU⟩
  intro t ht
  exact mem_closed_of_continuousWithinAt_left_of_ae
    (Set.toFinite ({0, 1} : Set ℝ)).isClosed ht.1 ht.2.le (hc t) hgb

/-- The signed jump of a left-continuous representative is its right limit minus its value. -/
def oneDimensionalJump (g : ℝ → ℝ) (t : ℝ) : ℝ := Function.rightLim g t - g t

lemma oneDimensionalJump_eq_zero_iff {g : ℝ → ℝ} (hg : BoundedVariationOn g univ)
    {t : ℝ} (hc : ContinuousWithinAt g (Iic t) t) :
    oneDimensionalJump g t = 0 ↔ ContinuousAt g t := by
  rw [oneDimensionalJump, sub_eq_zero]
  constructor
  · intro heq
    apply continuousAt_iff_continuous_left'_right'.mpr
    refine ⟨hc.mono Iio_subset_Iic_self, ?_⟩
    change Tendsto g (𝓝[>] t) (𝓝 (g t))
    simpa only [heq] using hg.tendsto_rightLim t
  · intro ht
    exact ht.continuousWithinAt.rightLim_eq

/-- Actual nonzero jumps of the left-continuous representative form a finite set on
compact subintervals where the represented function is binary almost everywhere. -/
lemma finite_oneDimensionalJump_of_binary_ae {g : ℝ → ℝ} {a b : ℝ} {K : Set ℝ}
    (hg : BoundedVariationOn g univ) (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hb : ∀ᵐ t ∂volume.restrict (Ioo a b), g t ∈ ({0, 1} : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ Ioo a b) :
    {t ∈ K | oneDimensionalJump g t ≠ 0}.Finite := by
  have heq : {t ∈ K | oneDimensionalJump g t ≠ 0} = {t ∈ K | ¬ContinuousAt g t} := by
    ext t
    simp only [mem_ofPred_eq, ne_eq, oneDimensionalJump_eq_zero_iff hg (hc t)]
  rw [heq]
  exact finite_discontinuities_of_binary_ae_bv hg hc hb hK hKU

/-- Almost every line in any fixed direction has locally unique left-continuous
indicator representatives with finitely many jumps on compact subintervals. -/
theorem HasLocallyFinitePerimeter.ae_finite_jumps_direction {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ‖v‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      e (EuclideanSpace.single (Fin.last n) 1) = v ∧
      ∀ᵐ x : EuclideanSpace ℝ (Fin n), ∀ a b : ℝ, ∃ g : ℝ → ℝ,
        BoundedVariationOn g univ ∧ (∀ t, ContinuousWithinAt g (Iic t) t) ∧
        (fun t : ℝ => E.indicator (fun _ => (1 : ℝ)) (e (graphBaseN n x) + t • v))
          =ᵐ[volume.restrict (Ioo a b)] g ∧
        (∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ)) ∧
        ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b →
          {t ∈ K | oneDimensionalJump g t ≠ 0}.Finite := by
  classical
  obtain ⟨e, he, hlines⟩ := hE.ae_lineSlice_direction hmE hv
  refine ⟨e, he, ?_⟩
  filter_upwards [hlines] with x hx
  intro a b
  let f : EuclideanSpace ℝ (Fin 1) → ℝ :=
    fun t => E.indicator (fun _ => (1 : ℝ)) (e (graphBaseN n x) + t 0 • v)
  have hfb : ∀ᵐ t : ℝ, f (euclideanOneReal.symm t) ∈ ({0, 1} : Set ℝ) :=
    ae_of_all _ fun t => by
      dsimp [f]
      by_cases ht : e (graphBaseN n x) + t • v ∈ E <;> simp [ht]
  obtain ⟨g, hg, hc, hfg, hgb, _⟩ := hx.exists_binary_representative_Ioo hfb a b
  refine ⟨g, hg, hc, ?_, hgb, fun K hK hKU => ?_⟩
  · simpa only [Function.comp_def, euclideanOneReal_symm_apply] using hfg
  · exact finite_oneDimensionalJump_of_binary_ae hg hc
      (ae_restrict_of_forall_mem measurableSet_Ioo hgb) hK hKU

end LiquidDrop
