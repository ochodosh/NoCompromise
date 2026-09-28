import NoCompromise.Area.GoodPiecesCarrier

/-!
# Countable exhaustion by uniform differentiability pieces

Quantitative Borel levels cover the rank-two differentiability locus. Each level
is covered up to a null set by countably many compact carriers, using the exact
small-remainder extraction. Successive set differences make the pieces disjoint
while retaining their original compact carriers.
-/

noncomputable section

open MeasureTheory Set Module Filter
open scoped ENNReal NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- The largest singular value is exactly the operator norm. -/
lemma singularValues_zero_eq_norm {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    L.singularValues 0 = ‖L‖ := by
  apply le_antisymm (singularValues_zero_le_norm L)
  exact L.opNorm_le_bound (L.singularValues_nonneg 0)
    (fun x => (singularValues_two_norm_bounds L x).2)

/-- The smaller planar singular value is the Jacobian divided by the operator norm. -/
lemma singularValues_one_eq_jacobian_div_norm {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    L.singularValues 1 = jacobian2Linear L / ‖L‖ := by
  by_cases hL : L = 0
  · simp [hL, jacobian2Linear_zero]
  · have hn : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
    apply (eq_div_iff hn).mpr
    rw [jacobian2Linear_eq_singularValues, singularValues_zero_eq_norm]
    ring

lemma measurable_singularValues_one {m : ℕ} : Measurable
    (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m) => L.singularValues 1) := by
  simp_rw [singularValues_one_eq_jacobian_div_norm]
  exact continuous_jacobian2Linear.measurable.div continuous_norm.measurable

/-- The differentiability points where the derivative has rank two. -/
def rankTwoDifferentiabilitySet {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | DifferentiableAt ℝ f x ∧ Function.Injective (fderiv ℝ f x)}

/-- The rank-two differentiability locus is exactly the nonzero-Jacobian locus. -/
lemma rankTwoDifferentiabilitySet_eq_jacobian_ne_zero {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) :
    rankTwoDifferentiabilitySet f = {x | jacobian2 f x ≠ 0} := by
  ext x
  constructor
  · intro hx
    exact ((jacobian2Linear_pos_iff_injective (fderiv ℝ f x)).2 hx.2).ne'
  · intro hx
    refine ⟨?_, ?_⟩
    · by_contra hnot
      exact hx (jacobian2_eq_zero_of_not_differentiableAt hnot)
    · exact (jacobian2Linear_pos_iff_injective (fderiv ℝ f x)).1
        (lt_of_le_of_ne (jacobian2_nonneg f x) (Ne.symm hx))

lemma measurableSet_rankTwoDifferentiabilitySet {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) :
    MeasurableSet (rankTwoDifferentiabilitySet f) := by
  have heq : rankTwoDifferentiabilitySet f =
      {x | DifferentiableAt ℝ f x} ∩ {x | 0 < jacobian2 f x} := by
    ext x
    simp [rankTwoDifferentiabilitySet, jacobian2, jacobian2Linear_pos_iff_injective]
  rw [heq]
  exact (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_lt measurable_const (measurable_jacobian2 f))

/-- Quantitative levels for the bounded compact-carrier extraction. -/
def quantitativeRankTwoSet {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | DifferentiableAt ℝ f x ∧ (∀ i : Fin 2, |x i| ≤ (n : ℝ) + 1) ∧
    ‖fderiv ℝ f x‖ ≤ (n : ℝ) + 1 ∧
    1 / ((n : ℝ) + 1) ≤ (fderiv ℝ f x).singularValues 1}
lemma measurableSet_quantitativeRankTwoSet {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) (n : ℕ) :
    MeasurableSet (quantitativeRankTwoSet f n) := by
  have hcoord : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) |
      ∀ i : Fin 2, |x i| ≤ (n : ℝ) + 1} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => |x i|) from
        (show Continuous (fun x : EuclideanSpace ℝ (Fin 2) => |x i|) from
          (EuclideanSpace.proj i).continuous.abs).measurable) measurable_const
  exact (measurableSet_of_differentiableAt ℝ f).inter (hcoord.inter
    ((measurableSet_le (measurable_fderiv ℝ f).norm measurable_const).inter
      (measurableSet_le measurable_const
        (measurable_singularValues_one.comp (measurable_fderiv ℝ f)))))
lemma quantitativeRankTwoSet_subset {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) (n : ℕ) :
    quantitativeRankTwoSet f n ⊆ rankTwoDifferentiabilitySet f := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hs : 0 < (fderiv ℝ f x).singularValues 1 :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hx.2.2.2
  apply (fderiv ℝ f x).injective_iff_forall_lt_finrank_singularValues_pos.mpr
  intro i hi
  have hi1 : i ≤ 1 := by simp only [finrank_euclideanSpace_fin] at hi; omega
  exact hs.trans_le ((fderiv ℝ f x).singularValues_antitone hi1)

lemma rankTwoDifferentiabilitySet_eq_iUnion {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) :
    rankTwoDifferentiabilitySet f = ⋃ n, quantitativeRankTwoSet f n := by
  apply Subset.antisymm
  · intro x hx
    have hs := (singularValues_two_pos_and_ordered (fderiv ℝ f x) hx.2).1
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖
      (max ‖fderiv ℝ f x‖ (1 / (fderiv ℝ f x).singularValues 1)))
    have hxn0 : ‖x‖ ≤ (n : ℝ) := (le_max_left _ _).trans hn
    have hrest : max ‖fderiv ℝ f x‖ (1 / (fderiv ℝ f x).singularValues 1) ≤ (n : ℝ) :=
      (le_max_right _ _).trans hn
    have hxn : ‖x‖ ≤ (n : ℝ) + 1 := by linarith
    have hDn0 : ‖fderiv ℝ f x‖ ≤ (n : ℝ) := (le_max_left _ _).trans hrest
    have hDn : ‖fderiv ℝ f x‖ ≤ (n : ℝ) + 1 := by linarith
    have hinv0 : 1 / (fderiv ℝ f x).singularValues 1 ≤ (n : ℝ) :=
      (le_max_right _ _).trans hrest
    have hinv : 1 / (fderiv ℝ f x).singularValues 1 ≤ (n : ℝ) + 1 := by linarith
    refine mem_iUnion.mpr ⟨n, hx.1, ?_, hDn, ?_⟩
    · intro i
      exact (show |x i| ≤ ‖x‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans hxn
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      have hh := (div_le_iff₀ hs).mp hinv
      nlinarith
  · exact iUnion_subset (quantitativeRankTwoSet_subset f)

/-- Countably many compact carriers cover the rank-two differentiability locus up to null sets. -/
theorem exists_countable_uniform_carrier_cover {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    ∃ d : ℕ → UniformDifferentiabilityCarrier f,
      (∀ j, (d j).carrier ⊆ rankTwoDifferentiabilitySet f) ∧
      volume (rankTwoDifferentiabilitySet f \ ⋃ j, (d j).carrier) = 0 := by
  classical
  have hex (n k : ℕ) : ∃ d : UniformDifferentiabilityCarrier f,
      d.carrier ⊆ quantitativeRankTwoSet f n ∧
      volume (quantitativeRankTwoSet f n \ d.carrier) <
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    obtain ⟨d, hsub, hsmall, hbound⟩ := exists_uniformDifferentiabilityCarrier_subset hf
      (measurableSet_quantitativeRankTwoSet f n) (n + 1) (by omega)
      (fun x hx i => by simpa only [Nat.cast_add, Nat.cast_one] using hx.2.1 i)
      (fun x hx => hx.1)
      (fun x hx => by simpa only [Nat.cast_add, Nat.cast_one] using hx.2.2.1)
      (fun x hx => by simpa only [Nat.cast_add, Nat.cast_one] using hx.2.2.2)
      (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    exact ⟨d, hsub, hsmall⟩
  choose d hsub hsmall using hex
  have hnull (n : ℕ) : volume (quantitativeRankTwoSet f n \ ⋃ k, (d n k).carrier) = 0 := by
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
    apply le_antisymm _ bot_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    exact Eventually.of_forall fun k =>
      (measure_mono (sdiff_subset_sdiff_right (subset_iUnion (fun j => (d n j).carrier) k))).trans
        (hsmall n k).le
  let D : ℕ → UniformDifferentiabilityCarrier f := fun j => d (Nat.unpair j).1 (Nat.unpair j).2
  refine ⟨D, fun j => (hsub _ _).trans (quantitativeRankTwoSet_subset f _), ?_⟩
  have hcover : rankTwoDifferentiabilitySet f \ (⋃ j, (D j).carrier) ⊆
      ⋃ n, quantitativeRankTwoSet f n \ (⋃ k, (d n k).carrier) := by
    intro x hx
    have hxrank := hx.1
    rw [rankTwoDifferentiabilitySet_eq_iUnion] at hxrank
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxrank
    refine mem_iUnion.mpr ⟨n, hxn, ?_⟩
    intro hxunion
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxunion
    apply hx.2
    exact mem_iUnion.mpr ⟨Nat.pair n k, by simpa only [D, Nat.unpair_pair] using hxk⟩
  exact measure_mono_null hcover (measure_iUnion_null hnull)

/-- The blueprint's exhaustion theorem: pairwise disjoint Borel uniform pieces
cover the rank-two differentiability points up to a Lebesgue-null remainder. -/
theorem exists_disjoint_uniform_differentiability_pieces {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    ∃ G : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
      Pairwise (fun i j => Disjoint (G i) (G j)) ∧
      (∀ j, IsUniformDifferentiabilityPiece f (G j)) ∧
      (∀ j, G j ⊆ rankTwoDifferentiabilitySet f) ∧
      volume (rankTwoDifferentiabilitySet f \ ⋃ j, G j) = 0 := by
  obtain ⟨d, hsub, hcover⟩ := exists_countable_uniform_carrier_cover hf
  let G : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := disjointed (fun j => (d j).carrier)
  refine ⟨G, disjoint_disjointed _, ?_, ?_, ?_⟩
  · intro j
    exact ⟨MeasurableSet.disjointed (fun j => (d j).isCompact.isClosed.measurableSet) j,
      d j, disjointed_subset _ _⟩
  · intro j
    exact (disjointed_subset _ _).trans (hsub j)
  · simpa only [G, iUnion_disjointed] using hcover

end LiquidDrop
