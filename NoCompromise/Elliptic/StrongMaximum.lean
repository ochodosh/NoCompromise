import NoCompromise.Elliptic.HarmonicMeanValueBall
import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Strong maximum principle from the actual ball mean-value identity
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma eqOn_ball_of_mean_value_maximum {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : Set (EuclideanSpace ℝ (Fin n))}
    (hu : ContinuousOn u G) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hball : closedBall c r ⊆ G)
    (havg : (⨍ x in ball c r, u x) = u c)
    (hmax : ∀ x ∈ ball c r, u x ≤ u c) : EqOn u (fun _ => u c) (ball c r) := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.restrict (ball c r)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (isBounded_ball (x := c) (r := r)).measure_lt_top (μ := volume)⟩
  have hi : Integrable u μ :=
    (hu.mono hball).integrableOn_compact (isCompact_closedBall c r) |>.mono_set
      ball_subset_closedBall
  have heq : (∫ x, u x ∂μ) = ∫ _, u c ∂μ := by
    rw [← havg]
    exact (integral_average μ u).symm
  have hae : u =ᵐ[μ] fun _ => u c :=
    (integral_eq_iff_of_ae_le hi (integrable_const _) (ae_restrict_of_forall_mem
      measurableSet_ball hmax)).mp heq
  exact Measure.eqOn_open_of_ae_eq hae isOpen_ball
    (hu.mono (ball_subset_closedBall.trans hball)) continuousOn_const

/-- On a connected open set, a continuous function with the genuine local
ball mean-value identity cannot attain its maximum without being constant. -/
theorem strong_maximum_of_mean_value {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : Set (EuclideanSpace ℝ (Fin n))}
    (hG : IsOpen G) (hconn : IsPreconnected G) (hu : ContinuousOn u G)
    (hmean : ∀ c ∈ G, ∀ r : ℝ, 0 < r → closedBall c r ⊆ G →
      (⨍ x in ball c r, u x) = u c)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ G)
    (hmax : ∀ x ∈ G, u x ≤ u x₀) : ∀ x ∈ G, u x = u x₀ := by
  let A := G ∩ {x | u x = u x₀}
  have hoA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hG.mem_nhds hx.1)
    have havg := hmean x hx.1 r hr hball
    have heq := eqOn_ball_of_mean_value_maximum hu x hball havg
      (fun y hy => (hmax y (hball (ball_subset_closedBall hy))).trans_eq hx.2.symm)
    apply mem_of_superset (ball_mem_nhds x hr)
    intro y hy
    exact ⟨hball (ball_subset_closedBall hy), (heq hy).trans hx.2⟩
  have hclosed : closure A ∩ G ⊆ A := by
    rintro x ⟨hxA, hxG⟩
    refine ⟨hxG, ?_⟩
    have hc := ((hu x hxG).mono (show A ⊆ G from inter_subset_left)).mem_closure hxA
      (show MapsTo u A {u x₀} from fun y hy => hy.2)
    change u x = u x₀
    simpa only [closure_singleton, mem_singleton_iff] using hc
  have hsub := hconn.subset_of_closure_inter_subset hoA
    (show (G ∩ A).Nonempty from ⟨x₀, hx₀, hx₀, rfl⟩) hclosed
  intro x hx
  exact (hsub hx).2

end LiquidDrop
