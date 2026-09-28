import NoCompromise.Regularity.HeightBoundLimit

/-! # Uniform height control at unit scale -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Bounded quasiminimality error suffices at unit scale. The smallness
threshold is fixed before the set and its error parameter. -/
theorem height_bound_unit {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (E : Set AmbientSpace) (ω : ℝ)
      (hE : IsOmegaMinimal E ω), ω ≤ 1 →
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) ≤ ε →
      ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < η := by
  classical
  by_contra hn
  push Not at hn
  have hseq (j : ℕ) : ∃ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      ω ≤ 1 ∧ (0 : AmbientSpace) ∈ frontier (densityOne E) ∧
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) ≤ 1 / ((j : ℝ) + 1) ∧
      ∃ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), η ≤ |x 2| :=
    hn (1 / ((j : ℝ) + 1)) (by positivity)
  choose E ω hE hω h0 he x hx hbad using hseq
  have hsmall : Tendsto (fun j => normalExcessIntegral (E j) (hE j).locallyFinite
      (hE j).nullMeasurable (standardCylinder (7 / 8)) (EuclideanSpace.single 2 1))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun j : ℕ => normalExcessIntegral_nonneg _ _ _ _ _)
      (g := fun j : ℕ => 1 / ((j : ℝ) + 1))
    · intro j
      apply (normalExcessIntegral_mono (E j) (hE j).locallyFinite (hE j).nullMeasurable
        (isBounded_cylinder 0 1 (ν := EuclideanSpace.single 2 1) (by simp))
        (by rw [standardCylinder_eq_cylinder]; exact cylinder_mono (by norm_num))
        (EuclideanSpace.single 2 1)).trans
      simpa only [cylindricalExcess, one_pow, div_one] using he j
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨F, hmF, _, k, hk, hl1⟩ := exists_quasiminimal_subsequence hE hω
  obtain ⟨a, ha, l, hl, hxl⟩ :=
    (isBounded_standardCylinder (3 / 4)).isCompact_closure.tendsto_subseq
      (fun j => subset_closure (hx (k j)).2)
  have haU : a ∈ standardCylinder (7 / 8) :=
    closure_standardCylinder_subset (by norm_num : (3 / 4 : ℝ) < 7 / 8) ha
  have hEk (j : ℕ) := hE (k (l j))
  have hωk (j : ℕ) := hω (k (l j))
  have h0k (j : ℕ) := h0 (k (l j))
  have hl1k (K : Set AmbientSpace) (hK : IsCompact K) :=
    (hl1 K hK).comp hl.tendsto_atTop
  have hhalf := height_limit_is_halfspace_zero hEk hωk h0k (by norm_num : (0 : ℝ) < 7 / 8)
    (hsmall.comp (hk.tendsto_atTop.comp hl.tendsto_atTop)) hmF.nullMeasurableSet hl1k
  have hheight : a 2 = 0 := IsOmegaMinimal.limit_boundary_height_eq hEk hωk
    (fun j => (hx (k (l j))).1) hxl hmF.nullMeasurableSet
    (isOpen_standardCylinder (7 / 8)) haU (fun K hK _ => hl1k K hK) hhalf
  have habs : Tendsto (fun j => |x (k (l j)) 2|) atTop (𝓝 |a 2|) :=
    ((show Continuous (fun y : AmbientSpace => |y 2|) by fun_prop).tendsto a).comp hxl
  have hge : η ≤ |a 2| := le_of_tendsto_of_tendsto tendsto_const_nhds habs
    (Eventually.of_forall fun j => hbad (k (l j)))
  rw [hheight, abs_zero] at hge
  exact (not_le_of_gt hη) hge

end LiquidDrop
