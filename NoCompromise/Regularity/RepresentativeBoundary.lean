module

public import NoCompromise.Regularity.RepresentativeOpen

@[expose] public section

/-! # Topological boundary of the density-one representative -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem IsOmegaMinimal.frontier_densityOne {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) : frontier (densityOne E) = essentialBoundary E := by
  apply Subset.antisymm
  · intro x hx
    rw [frontier, hE.isOpen_densityOne.interior_eq] at hx
    have hcl : closure (densityOne E) ⊆ (densityZero E)ᶜ :=
      closure_minimal (fun _ h1 h0 =>
        disjoint_left.mp (disjoint_densityZero_densityOne E) h0 h1)
        hE.isOpen_densityZero.isClosed_compl
    exact fun h => h.elim (hcl hx.1) hx.2
  · intro x hx
    rw [frontier, hE.isOpen_densityOne.interior_eq]
    refine ⟨?_, fun h => hx (Or.inr h)⟩
    apply Metric.mem_closure_iff.mpr
    intro r hr
    have hp := radialVolume_pos_at_essentialBoundary hx hr
    have hne : volume (E ∩ ball x r) ≠ 0 := by
      intro hz
      simp only [radialVolume, hz, ENNReal.toReal_zero, lt_self_iff_false] at hp
    have hd : volume (densityOne E ∩ ball x r) ≠ 0 := by
      have heq : (densityOne E ∩ ball x r : Set AmbientSpace) =ᵐ[volume]
          (E ∩ ball x r : Set AmbientSpace) :=
        (densityOne_ae_eq (by norm_num : 0 < 3) hE.nullMeasurable).inter
          (EventuallyEq.rfl : ball x r =ᵐ[volume] ball x r)
      rwa [measure_congr heq]
    obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hd
    exact ⟨z, hz.1, by simpa only [mem_ball, dist_comm] using hz.2⟩

theorem IsOmegaMinimal.closure_reducedBoundary {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) :
    closure (reducedBoundary E hE.locallyFinite hE.nullMeasurable) = essentialBoundary E := by
  apply Subset.antisymm
  · exact closure_minimal
      (reducedBoundary_subset_essentialBoundary hE.locallyFinite hE.nullMeasurable)
      hE.isClosed_essentialBoundary
  · intro x hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r := min ε 1
    have hr : 0 < r := lt_min hε zero_lt_one
    obtain ⟨c, hc, hl⟩ := quasiminimal_perimeter_lower_bound ω hE.nonneg
    have hp := hl E hE x hx r hr (min_le_right _ _)
    have hne : perimeterIn E (ball x r) ≠ 0 := by
      intro hz
      rw [hz, ENNReal.toReal_zero] at hp
      exact (not_le.mpr (mul_pos hc (pow_pos hr 2))) hp
    rw [perimeterIn_eq_reducedBoundary_area E hE.locallyFinite hE.nullMeasurable
      isOpen_ball] at hne
    obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hne
    refine ⟨z, hz.2, ?_⟩
    have hzr : dist z x < r := hz.1
    simpa only [dist_comm] using hzr.trans_le (min_le_left ε 1)

/-- The full open-representative conversion, including equality modulo null sets
and both genuine topological boundary identifications. -/
theorem quasiminimal_open_representative {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) :
    IsOpen (densityOne E) ∧ densityOne E =ᵐ[volume] E ∧ IsOpen (densityZero E) ∧
      frontier (densityOne E) = essentialBoundary E ∧
      frontier (densityOne E) =
        closure (reducedBoundary E hE.locallyFinite hE.nullMeasurable) :=
  ⟨hE.isOpen_densityOne, densityOne_ae_eq (by norm_num) hE.nullMeasurable,
    hE.isOpen_densityZero, hE.frontier_densityOne,
    hE.frontier_densityOne.trans hE.closure_reducedBoundary.symm⟩

end LiquidDrop
