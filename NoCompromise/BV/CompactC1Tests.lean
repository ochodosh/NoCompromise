module

public import NoCompromise.BV.JumpKernel

@[expose] public section

/-!
# Countable compact C¹ test families

On each fixed compact support, values and first coordinate derivatives live
in a finite product of separable spaces of continuous functions. A countable
family therefore determines every continuous test functional, simultaneously
for arbitrary parameters outside one null set.
-/

noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped Topology
namespace LiquidDrop

/-- Scalar C¹ test functions whose support lies in one fixed compact set. -/
def CompactC1Test {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :=
  {φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ //
    ContDiff ℝ 1 φ ∧ tsupport φ ⊆ K}

/-- Values and coordinate derivatives, restricted to the compact support set. -/
def compactC1TestJet {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (φ : CompactC1Test K) : C(K, ℝ) × (Fin n → C(K, ℝ)) :=
  (⟨fun x => φ.val x, φ.val.continuous.comp continuous_subtype_val⟩,
    fun i => ⟨fun x => fderiv ℝ φ.val x (EuclideanSpace.single i 1),
      (((φ.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        continuous_subtype_val)⟩)

/-- A single countable test family determines every continuous functional of
values and first derivatives on the fixed compact support. -/
theorem exists_countable_compactC1_tests {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    ∃ S : Set (CompactC1Test K), S.Countable ∧
      ∀ F : C(K, ℝ) × (Fin n → C(K, ℝ)) → ℝ, Continuous F →
        (∀ φ ∈ S, F (compactC1TestJet K φ) = 0) →
          ∀ φ : CompactC1Test K, F (compactC1TestJet K φ) = 0 := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (C(K, ℝ) × (Fin n → C(K, ℝ))) := range (compactC1TestJet K)
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense A
  have hpre (w : A) : ∃ φ, compactC1TestJet K φ = w.val := w.property
  choose pick hpick using hpre
  let S : Set (CompactC1Test K) := pick '' D
  refine ⟨S, hDc.image pick, fun F hF hzero φ => ?_⟩
  have hclosed : IsClosed {w : A | F w.val = 0} :=
    isClosed_eq (hF.comp continuous_subtype_val) continuous_const
  have hsub : D ⊆ {w : A | F w.val = 0} := by
    intro w hw
    change F w.val = 0
    rw [← hpick w]
    exact hzero (pick w) (mem_image_of_mem pick hw)
  exact closure_minimal hsub hclosed (hDd ⟨compactC1TestJet K φ, mem_range_self φ⟩)

/-- Exceptional parameter sets can be chosen simultaneously for all compact C¹
tests whenever the test functional is continuous in its value/derivative jet. -/
theorem ae_all_compactC1_tests_of_continuous {n : ℕ} {α : Type*}
    [MeasurableSpace α] {μ : Measure α}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (F : α → C(K, ℝ) × (Fin n → C(K, ℝ)) → ℝ)
    (hF : ∀ x, Continuous (F x))
    (htest : ∀ φ : CompactC1Test K, ∀ᵐ x ∂μ, F x (compactC1TestJet K φ) = 0) :
    ∀ᵐ x ∂μ, ∀ φ : CompactC1Test K, F x (compactC1TestJet K φ) = 0 := by
  obtain ⟨S, hSc, hS⟩ := exists_countable_compactC1_tests hK
  have ha : ∀ᵐ x ∂μ, ∀ φ ∈ S, F x (compactC1TestJet K φ) = 0 := by
    rw [ae_ball_iff hSc]
    exact fun φ _ => htest φ
  exact ha.mono fun x hx => hS (F x) (hF x) hx

end LiquidDrop
