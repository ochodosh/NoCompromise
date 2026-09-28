import NoCompromise.Elliptic.CampanatoHolderPrimitive

/-! Compatible local C¹ representatives glue to a single genuine C¹ function.
Compatibility follows from almost-everywhere equality and continuity on open
sets; no pointwise choice of the original weak representative is presumed. -/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem boundary_exists_c1_representative_of_local {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hloc : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 1 w V ∧
        w =ᵐ[volume.restrict V] u) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 1 v U ∧
      v =ᵐ[volume.restrict U] u := by
  classical
  choose V hV hxV hsV w hw heq using fun x : U => hloc x.val x.property
  let v (x : EuclideanSpace ℝ (Fin n)) : ℝ := if hx : x ∈ U then w ⟨x, hx⟩ x else 0
  have hev (x : U) : EqOn v (w x) (V x) := by
    intro y hy
    have hyU := hsV x hy
    have hyEq : w ⟨y, hyU⟩ =ᵐ[volume.restrict (V x ∩ V ⟨y, hyU⟩)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (heq ⟨y, hyU⟩)
    have hxEq : w x =ᵐ[volume.restrict (V x ∩ V ⟨y, hyU⟩)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (heq x)
    have hp := Measure.eqOn_open_of_ae_eq (hyEq.trans hxEq.symm)
      ((hV x).inter (hV ⟨y, hyU⟩))
      ((hw ⟨y, hyU⟩).continuousOn.mono inter_subset_right)
      ((hw x).continuousOn.mono inter_subset_left)
    dsimp only [v]
    rw [dite_eq_left hyU]
    exact hp ⟨hy, hxV ⟨y, hyU⟩⟩
  have hnear (x : U) : v =ᶠ[𝓝 x.val] w x :=
    Filter.eventually_of_mem ((hV x).mem_nhds (hxV x)) (fun _ hy => hev x hy)
  have hvc : ContDiffOn ℝ 1 v U := hU.contDiffOn_iff.mpr (by
    intro x hx
    have ht := (hw ⟨x, hx⟩).contDiffAt ((hV ⟨x, hx⟩).mem_nhds (hxV ⟨x, hx⟩))
    exact ht.congr_of_eventuallyEq (hnear ⟨x, hx⟩))
  refine ⟨v, hvc, ?_⟩
  have hcover : U ⊆ ⋃ x : U, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨S, hS, hcoverS⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hV hcover
  apply ae_restrict_of_ae_restrict_of_subset hcoverS
  apply (ae_restrict_biUnion_iff V hS _).mpr
  intro x _
  filter_upwards [heq x, ae_restrict_mem (hV x).measurableSet] with y hy hyV
  exact (hev x hyV).trans hy

end LiquidDrop
