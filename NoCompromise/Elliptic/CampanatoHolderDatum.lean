module

public import NoCompromise.Elliptic.CampanatoHolderSegmentTests
public import NoCompromise.Elliptic.CampanatoHolderSegmentDerivative

@[expose] public section

/-!
# Hölder data as a divergence, blueprint `lem:Gh`

The constructed field has the exact C⁰,α norm bound, is locally integrable,
and has the required divergence in the genuine test-function sense. The scalar
segment average also has the stated ordinary directional derivative. The
segment-domain convention agrees with the full unoriented interval between
zero and h, for both signs of every nonzero step.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanatoSegmentDomain_mem_iff_between {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) {h : ℝ} (hh : h ≠ 0)
    (e x : EuclideanSpace ℝ (Fin n)) :
    x ∈ campanatoSegmentDomain U (h • e) ↔
      ∀ t ∈ uIcc (0 : ℝ) h, x + t • e ∈ U := by
  constructor
  · intro hx t ht
    have hs : t / h ∈ Icc (0 : ℝ) 1 := by
      by_cases hp : 0 < h
      · have ht' : 0 ≤ t ∧ t ≤ h := by simpa only [uIcc_of_le hp.le, mem_Icc] using ht
        exact ⟨div_nonneg ht'.1 hp.le, (div_le_iff₀ hp).mpr (by linarith [ht'.2])⟩
      · have hn : h < 0 := lt_of_le_of_ne (le_of_not_gt hp) hh
        have ht' : h ≤ t ∧ t ≤ 0 := by simpa only [uIcc_of_ge hn.le, mem_Icc] using ht
        exact ⟨div_nonneg_of_nonpos ht'.2 hn.le,
          (div_le_iff_of_neg hn).mpr (by linarith [ht'.1])⟩
    simpa only [smul_smul, div_mul_cancel₀ t hh] using hx (t / h) hs
  · intro hx s hs
    have ht : s * h ∈ uIcc (0 : ℝ) h := by
      by_cases hp : 0 ≤ h
      · rw [uIcc_of_le hp, mem_Icc]
        constructor <;> nlinarith [hs.1, hs.2]
      · have hn : h ≤ 0 := (lt_of_not_ge hp).le
        rw [uIcc_of_ge hn, mem_Icc]
        constructor <;> nlinarith [hs.1, hs.2]
    simpa only [smul_smul] using hx (s * h) ht

lemma campanato_difference_data_continuousOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContinuousOn g U) (h : ℝ) (e : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun x => (g (x + h • e) - g x) / h)
      (campanatoSegmentDomain U (h • e)) := by
  apply ContinuousOn.div_const
  apply ContinuousOn.sub
  · apply hg.comp (continuous_id.add continuous_const).continuousOn
    intro x hx
    simpa only [one_smul, Pi.add_apply, id_eq] using! hx 1 (by simp)
  · exact hg.mono (campanatoSegmentDomain_subset U (h • e))

/-- Full `lem:Gh`, expressed using its explicit field rather than an assumed
primitive. It includes local integrability, classical directional differentiation,
and the exact weak divergence identity against every compact C¹ test. -/
theorem campanato_holder_difference_quotient_datum {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {a : ℝ} (ha : 0 < a)
    (hg : ContinuousOn g U) (hf : HasFiniteHolderNormOn a g U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0) :
    let e := EuclideanSpace.single i (1 : ℝ)
    let V := campanatoSegmentDomain U (h • e)
    IsOpen V ∧
      HasFiniteHolderNormOn a (campanatoSegmentField g h e) V ∧
      holderNorm a (campanatoSegmentField g h e) V ≤ holderNorm a g U ∧
      ContinuousOn (campanatoSegmentField g h e) V ∧
      LocallyIntegrableOn (campanatoSegmentField g h e) V ∧
      LocallyIntegrableOn (fun x => (g (x + h • e) - g x) / h) V ∧
      (∀ x ∈ V, HasDerivAt
        (fun s : ℝ => campanatoSegmentAverage g (h • e) (x + s • e))
        ((g (x + h • e) - g x) / h) 0) ∧
      ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ V →
        (∫ x, inner ℝ (campanatoSegmentField g h e x) (gradient φ x)) =
          -(∫ x, ((g (x + h • e) - g x) / h) * φ x) := by
  dsimp only
  let e := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hV := isOpen_campanatoSegmentDomain hU (h • e)
  have hnorm := campanatoSegmentField_holder hg hf h e he
  have hc := campanatoSegmentField_continuousOn ha hg hf h e he
  refine ⟨hV, hnorm.1, hnorm.2, hc, hc.locallyIntegrableOn hV.measurableSet,
    (campanato_difference_data_continuousOn hg h e).locallyIntegrableOn hV.measurableSet, ?_, ?_⟩
  · exact fun x hx => campanatoSegmentAverage_hasDerivAt hU hg hh e hx
  · exact fun φ hφ hcφ hsφ => campanatoSegmentField_distribution hU hg hφ hcφ hh e hsφ

end LiquidDrop
