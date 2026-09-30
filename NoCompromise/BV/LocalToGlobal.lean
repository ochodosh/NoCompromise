module

public import NoCompromise.BV.Basic

@[expose] public section

/-!
# Local-to-global BV on an open domain

Finite compact subcovers and the proved open-cover variation inequality turn
local finite-variation neighborhoods into genuine locally BV regularity.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Finite variation on an open neighborhood of each point gives local BV.
The neighborhoods need not share one global variation bound. -/
theorem isLocallyBVOn_of_local_variation {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : LocallyIntegrableOn f U)
    (hlocal : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ variation f V < ∞) : IsLocallyBVOn f U := by
  classical
  refine ⟨hf, fun A _ hcA hAU => ?_⟩
  have hloc (x : closure A) := hlocal x (hAU x.property)
  choose V hV hxV hfin using hloc
  obtain ⟨s, hs⟩ := hcA.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  have hcover : A ⊆ ⋃ i : s, V i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (subset_closure hx))
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  apply (variation_le_tsum_open_cover (hf.mono_set (subset_closure.trans hAU))
    (fun i : s => V i.val) (fun i => hV i.val) hcover).trans_lt
  rw [tsum_fintype, ENNReal.sum_lt_top]
  intro i _
  exact hfin i.val

/-- The whole-space form used when assembling chartwise cuts. -/
theorem isLocallyBVOn_univ_of_local_variation {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f)
    (hlocal : ∀ x, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ variation f V < ∞) : IsLocallyBVOn f univ :=
  isLocallyBVOn_of_local_variation (hf.locallyIntegrableOn univ) (fun x _ => hlocal x)

end LiquidDrop
