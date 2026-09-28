import NoCompromise.Elliptic.HarmonicMeanValueBall
import NoCompromise.Elliptic.SobolevChainHarmonic

/-!
# Local harmonic representatives and mean values

Cutoff extension localizes the classical ball mean-value identity. Local smooth
representatives of the same almost-everywhere class agree on overlaps and glue
to one smooth representative on an arbitrary open Euclidean set.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma laplacianN_congr_nhds {n : ℕ}
    {u v : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : u =ᶠ[𝓝 x] v) : laplacianN u x = laplacianN v x := by
  unfold laplacianN
  apply Finset.sum_congr rfl
  intro i _
  have hc : poissonCoordinateDerivative i u =ᶠ[𝓝 x] poissonCoordinateDerivative i v := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L => L (EuclideanSpace.single i 1)) hy
  exact congrArg (fun L => L (EuclideanSpace.single i 1)) (hc.fderiv_eq (𝕜 := ℝ))

lemma exists_global_contDiff_eq_near_compact {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      ∀ x ∈ K, w =ᶠ[𝓝 x] u := by
  obtain ⟨χ, hcχ, _, hsχ, hχ, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  refine ⟨fun x => χ x * u x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hcχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
    · have hxt : x ∉ tsupport χ := fun ht => hx (hsχ ht)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hxt] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · intro x hx
    filter_upwards [hχ.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [hy, one_mul]

/-- The classical mean-value identity requires smoothness only on the open
ambient domain; a compact cutoff supplies the global representative locally. -/
theorem average_ball_eq_of_contDiffOn_laplacianN_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hh : ∀ x ∈ U, laplacianN u x = 0)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ U) :
    (⨍ x in ball c r, u x) = u c := by
  obtain ⟨w, hw, he⟩ := exists_global_contDiff_eq_near_compact hU
    (isCompact_closedBall c r) hball hu
  have hwlap (x) (hx : x ∈ ball c r) : laplacianN w x = 0 :=
    (laplacianN_congr_nhds (he x (ball_subset_closedBall hx))).trans (hh x (hball
      (ball_subset_closedBall hx)))
  have hv := average_ball_eq_of_laplacianN_eq_zero (hw.of_le (by simp)) c hr hwlap
  have hae : w =ᵐ[volume.restrict (ball c r)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (he x (ball_subset_closedBall hx)).self_of_nhds
  rw [average_congr hae] at hv
  exact hv.trans ((he c (mem_closedBall_self hr.le)).self_of_nhds)

/-- Compatible local smooth representatives of a measurable class glue on an
open Euclidean set. Compatibility follows from almost-everywhere agreement
and continuity, rather than an assumed choice of representatives. -/
theorem exists_contDiffOn_representative_of_local {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hloc : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
        w =ᵐ[volume.restrict V] u ∧ ∀ y ∈ V, laplacianN w y = 0) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
      v =ᵐ[volume.restrict U] u ∧ ∀ x ∈ U, laplacianN v x = 0 := by
  classical
  choose V hV hxV hsV w hw heq hzero using fun x : U => hloc x.val x.property
  let v (x : EuclideanSpace ℝ (Fin n)) : ℝ := if hx : x ∈ U then w ⟨x, hx⟩ x else 0
  have hev (x : U) : EqOn v (w x) (V x) := by
    intro y hy
    have hyU := hsV x hy
    have hyEq : w ⟨y, hyU⟩ =ᵐ[volume.restrict (V x ∩ V ⟨y, hyU⟩)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (heq ⟨y, hyU⟩)
    have hxEq : w x =ᵐ[volume.restrict (V x ∩ V ⟨y, hyU⟩)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (heq x)
    have hlocal : w ⟨y, hyU⟩ =ᵐ[volume.restrict (V x ∩ V ⟨y, hyU⟩)] w x :=
      hyEq.trans hxEq.symm
    have hp := Measure.eqOn_open_of_ae_eq hlocal ((hV x).inter (hV ⟨y, hyU⟩))
      (hw ⟨y, hyU⟩).continuous.continuousOn (hw x).continuous.continuousOn
    dsimp only [v]
    rw [dite_eq_left hyU]
    exact hp ⟨hy, hxV ⟨y, hyU⟩⟩
  have hnear (x : U) : v =ᶠ[𝓝 x.val] w x :=
    Filter.eventually_of_mem ((hV x).mem_nhds (hxV x)) (fun _ hy => hev x hy)
  have hvc : ContDiffOn ℝ (⊤ : ℕ∞) v U := hU.contDiffOn_iff.mpr (by
    intro x hx
    exact (hw ⟨x, hx⟩).contDiffAt.congr_of_eventuallyEq (hnear ⟨x, hx⟩))
  refine ⟨v, hvc, ?_, fun x hx => (laplacianN_congr_nhds (hnear ⟨x, hx⟩)).trans
    (hzero ⟨x, hx⟩ x (hxV ⟨x, hx⟩))⟩
  have hcover : U ⊆ ⋃ x : U, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨S, hS, hcoverS⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hV hcover
  apply ae_restrict_of_ae_restrict_of_subset hcoverS
  apply (ae_restrict_biUnion_iff V hS _).mpr
  intro x _
  filter_upwards [heq x, ae_restrict_mem (hV x).measurableSet] with y hy hyV
  exact (hev x hyV).trans hy

end LiquidDrop
