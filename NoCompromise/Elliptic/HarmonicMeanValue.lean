module

public import NoCompromise.Elliptic.HarmonicMeanValueLocal

@[expose] public section

/-!
# Smooth representatives and harmonic mean values

Distributional harmonicity and explicit local L² integrability give a single
smooth representative on any open domain in dimensions below four. It equals
its average on every compactly contained ball. For an already continuous
function, local L² follows automatically and the identities hold pointwise
for the original representative.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Continuous functions are locally L² on open Euclidean sets. -/
lemma exists_ball_memLp_two_of_continuousOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContinuousOn u U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ∃ R > 0, ball x R ⊆ U ∧ MemLp u 2 (volume.restrict (ball x R)) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hs : closedBall x (R / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hc := hu.mono hs
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (R / 2)).exists_bound_of_continuousOn hc
  let : IsFiniteMeasure (volume.restrict (ball x (R / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  refine ⟨R / 2, half_pos hR, ball_subset_closedBall.trans hs,
    MemLp.of_bound (hc.mono ball_subset_closedBall |>.aestronglyMeasurable measurableSet_ball)
      C ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  exact hC y (ball_subset_closedBall hy)

/-- Weak harmonicity with explicit local L² yields one smooth representative
on the whole open domain, satisfying the actual ball mean-value identity.
This includes both dimensions in blueprint `lem:mean-value`. -/
theorem HasDistributionalLaplacianOn.exists_smooth_mean_value {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U)
    (hu : ∀ x ∈ U, ∃ R > 0, ball x R ⊆ U ∧ MemLp u 2 (volume.restrict (ball x R))) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v U ∧ v =ᵐ[volume.restrict U] u ∧
      (∀ x ∈ U, laplacianN v x = 0) ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → closedBall c r ⊆ U →
        (⨍ x in ball c r, v x) = v c := by
  have hlocal : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
        w =ᵐ[volume.restrict V] u ∧ ∀ y ∈ V, laplacianN w y = 0 := by
    intro x hx
    obtain ⟨R, hR, hs, hmem⟩ := hu x hx
    obtain ⟨w, hw, he, hzero⟩ := interior_harmonic_smooth hn x (half_lt_self hR) (h.mono hs) hmem
    exact ⟨ball x (R / 2), isOpen_ball, mem_ball_self (half_pos hR),
      (ball_subset_ball (half_le_self hR.le)).trans hs, w, hw, he, hzero⟩
  obtain ⟨v, hv, he, hzero⟩ := exists_contDiffOn_representative_of_local hU hlocal
  exact ⟨v, hv, he, hzero, fun c _ hr hs =>
    average_ball_eq_of_contDiffOn_laplacianN_eq_zero hU hv hzero c hr hs⟩

/-- For an already continuous weakly harmonic function, the smooth representative
is the original function everywhere, so no representative convention is hidden. -/
theorem HasDistributionalLaplacianOn.smooth_mean_value_of_continuous {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U) (hu : ContinuousOn u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) u U ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → closedBall c r ⊆ U →
        (⨍ x in ball c r, u x) = u c := by
  obtain ⟨v, hv, he, _, hm⟩ := h.exists_smooth_mean_value hn hU
    (fun _ hx => exists_ball_memLp_two_of_continuousOn hU hu hx)
  have hp : EqOn v u U := Measure.eqOn_open_of_ae_eq he hU hv.continuousOn hu
  refine ⟨hv.congr (fun _ hx => (hp hx).symm), fun c r hr hs => ?_⟩
  have hae : v =ᵐ[volume.restrict (ball c r)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hp (hs (ball_subset_closedBall hx))
  rw [← average_congr hae, hm c r hr hs]
  exact hp (hs (mem_closedBall_self hr.le))

/-- The actual mean-value identity for continuous distributionally harmonic
functions on arbitrary open domains in dimensions two and three. -/
theorem HasDistributionalLaplacianOn.average_ball_eq {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U) (hu : ContinuousOn u U)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (hs : closedBall c r ⊆ U) :
    (⨍ x in ball c r, u x) = u c :=
  (h.smooth_mean_value_of_continuous hn hU hu).2 c r hr hs

/-- Weak harmonicity upgrades an already continuous representative to smoothness. -/
theorem HasDistributionalLaplacianOn.contDiffOn_of_continuous {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U) (hu : ContinuousOn u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) u U :=
  (h.smooth_mean_value_of_continuous hn hU hu).1

end LiquidDrop
