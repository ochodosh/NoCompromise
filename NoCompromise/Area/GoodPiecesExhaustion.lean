module

public import NoCompromise.Area.GoodPieces
public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

/-!
# Extraction of uniform differentiability carriers

Uniform remainder conditions are closed conditions on the pair `(x, L)` when
`f` is continuous. Their pullbacks along the measurable derivative are therefore
Borel. The countable-scale argument and inner regularity provide compact subsets
with uniform differentiability, without any area formula as an input.
-/

noncomputable section

open MeasureTheory Set Module Filter
open scoped ENNReal NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- The closed condition that `L` approximates `f` near `x` at a specified scale. -/
def remainderControl {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) (r ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2) ×
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
  {p | ∀ y, ‖y - p.1‖ < r → ‖f y - f p.1 - p.2 (y - p.1)‖ ≤ ε * ‖y - p.1‖}

lemma isClosed_remainderControl {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    (r ε : ℝ) : IsClosed (remainderControl f r ε) := by
  have heq : remainderControl f r ε = ⋂ y,
      {p | r ≤ ‖y - p.1‖} ∪ {p | ‖f y - f p.1 - p.2 (y - p.1)‖ ≤ ε * ‖y - p.1‖} := by
    ext p
    simp only [remainderControl, mem_ofPred_eq, mem_iInter, mem_union,
      imp_iff_not_or, not_lt]
  rw [heq]
  apply isClosed_iInter
  intro y
  apply IsClosed.union
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le (by fun_prop) (by fun_prop)

/-- Points at which the actual derivative has the specified remainder control. -/
def derivativeRemainderSet {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)) (r ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun x => (x, fderiv ℝ f x)) ⁻¹' remainderControl f r ε

lemma measurableSet_derivativeRemainderSet {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    (r ε : ℝ) : MeasurableSet (derivativeRemainderSet f r ε) :=
  (isClosed_remainderControl hf r ε).measurableSet.preimage
    (measurable_id.prodMk (measurable_fderiv ℝ f))

lemma derivativeRemainderSet_mono_radius {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    {r s ε : ℝ} (hrs : r ≤ s) :
    derivativeRemainderSet f s ε ⊆ derivativeRemainderSet f r ε :=
  fun _ hx y hy => hx y (hy.trans_le hrs)

lemma differentiableAt_mem_derivativeRemainderSet {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, x ∈ derivativeRemainderSet f (1 / ((n : ℝ) + 1)) ε := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hf.hasFDerivAt.isLittleO.def hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  refine ⟨n, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hy.trans hn

/-- Uniform differentiability on a set, with comparison points in the whole ambient plane. -/
def UniformRemainderOn {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ ε > 0, ∃ r > 0, ∀ x ∈ S, ∀ y, ‖y - x‖ < r →
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε * ‖y - x‖

lemma UniformRemainderOn.mono {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {S T : Set (EuclideanSpace ℝ (Fin 2))} (hf : UniformRemainderOn f S) (hTS : T ⊆ S) :
    UniformRemainderOn f T := by
  intro ε hε
  obtain ⟨r, hr, hrem⟩ := hf ε hε
  exact ⟨r, hr, fun x hx => hrem x (hTS hx)⟩

/-- At any fixed error tolerance, the bad points decrease to the empty set. -/
lemma tendsto_measure_sdiff_derivativeRemainderSet {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => volume (S \ derivativeRemainderSet f (1 / ((n : ℝ) + 1)) ε))
      atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => S \ derivativeRemainderSet f (1 / ((n : ℝ) + 1)) ε) := by
    intro i j hij
    apply sdiff_subset_sdiff_right
    apply derivativeRemainderSet_mono_radius
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hempty : (⋂ n : ℕ, S \ derivativeRemainderSet f (1 / ((n : ℝ) + 1)) ε) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxS := (mem_iInter.mp hx 0).1
    obtain ⟨n, hn⟩ := differentiableAt_mem_derivativeRemainderSet (hdiff x hxS) hε
    exact (mem_iInter.mp hx n).2 hn
  have ht := tendsto_measure_iInter_atTop
    (fun n => (hS.diff (measurableSet_derivativeRemainderSet hf _ _)).nullMeasurableSet)
    hanti ⟨0, ne_top_of_le_ne_top hSf (measure_mono sdiff_subset)⟩
  simpa only [hempty, measure_empty, Function.comp_def] using ht

/-- The countable-scale Egorov step for differentiation remainders. -/
lemma exists_uniformRemainderOn_sdiff_small {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ T ⊆ S, MeasurableSet T ∧ volume (S \ T) ≤ η ∧ UniformRemainderOn f T := by
  classical
  have hn : ∀ k : ℕ, ∃ n : ℕ,
      volume (S \ derivativeRemainderSet f (1 / ((n : ℝ) + 1)) (1 / ((k : ℝ) + 1))) ≤
        (η / 2) * (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have ht := tendsto_measure_sdiff_derivativeRemainderSet hf hS hSf hdiff
      (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
    have hpos : 0 < (η / 2) * (2⁻¹ : ℝ≥0∞) ^ k :=
      ENNReal.mul_pos (η.half_pos hη.ne').ne' (by simp)
    obtain ⟨n, hn⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1 ht _ hpos
    exact ⟨n, by simpa only [zero_add] using (hn n le_rfl).2⟩
  choose n hn using hn
  let bad : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun k =>
    S \ derivativeRemainderSet f (1 / ((n k : ℝ) + 1)) (1 / ((k : ℝ) + 1))
  let T := S \ ⋃ k, bad k
  have hTm : MeasurableSet T := hS.diff (MeasurableSet.iUnion fun k =>
    hS.diff (measurableSet_derivativeRemainderSet hf _ _))
  refine ⟨T, sdiff_subset, hTm, ?_, ?_⟩
  · calc
      volume (S \ T) ≤ volume (⋃ k, bad k) := measure_mono (by
        intro x hx
        by_contra hnot
        exact hx.2 ⟨hx.1, hnot⟩)
      _ ≤ ∑' k, volume (bad k) := measure_iUnion_le _
      _ ≤ ∑' k, (η / 2) * (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.tsum_le_tsum hn
      _ ≤ η := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, mul_comm]
        exact ENNReal.mul_div_le
  · intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    refine ⟨1 / ((n k : ℝ) + 1), by positivity, ?_⟩
    intro x hx y hy
    have hxR : x ∈ derivativeRemainderSet f (1 / ((n k : ℝ) + 1))
        (1 / ((k : ℝ) + 1)) := by
      by_contra hnot
      exact hx.2 (mem_iUnion.mpr ⟨k, hx.1, hnot⟩)
    exact (hxR y hy).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))

/-- A finite-measure differentiability set contains compact subsets with uniform
full-space remainder control and arbitrarily small omitted measure. -/
lemma exists_compact_uniformRemainderOn {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K ⊆ S, IsCompact K ∧ volume (S \ K) < η ∧ UniformRemainderOn f K := by
  obtain ⟨T, hTS, hTm, hsmall, hrem⟩ := exists_uniformRemainderOn_sdiff_small hf hS hSf hdiff
    (η.half_pos hη.ne')
  obtain ⟨K, hKT, hK, hTK⟩ := hTm.exists_isCompact_sdiff_lt
    (ne_top_of_le_ne_top hSf (measure_mono hTS)) (η.half_pos hη.ne').ne'
  refine ⟨K, hKT.trans hTS, hK, ?_, hrem.mono hKT⟩
  calc
    volume (S \ K) ≤ volume (S \ T) + volume (T \ K) := by
      apply (measure_mono (show S \ K ⊆ (S \ T) ∪ (T \ K) from ?_)).trans
        (measure_union_le _ _)
      intro x hx
      by_cases hxT : x ∈ T
      · exact Or.inr ⟨hxT, hx.2⟩
      · exact Or.inl ⟨hx.1, hxT⟩
    _ < η / 2 + η / 2 := ENNReal.add_lt_add_of_le_of_lt
      (ne_top_of_le_ne_top hSf (measure_mono sdiff_subset)) hsmall hTK
    _ = η := ENNReal.add_halves _

end LiquidDrop
