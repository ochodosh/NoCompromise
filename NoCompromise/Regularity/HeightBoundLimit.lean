module

public import NoCompromise.Regularity.HeightCompactnessPolar
public import NoCompromise.Regularity.HeightCompactnessClassification
public import NoCompromise.Regularity.SlabCap

@[expose] public section

/-! # The small-excess compactness limit is the correctly oriented plane -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem height_limit_is_halfspace_zero
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    (h0 : ∀ j, (0 : AmbientSpace) ∈ frontier (densityOne (E j)))
    {R : ℝ} (hR : 0 < R)
    (he : Tendsto (fun j => normalExcessIntegral (E j) (hE j).locallyFinite
      (hE j).nullMeasurable (standardCylinder R) (EuclideanSpace.single 2 1))
      atTop (𝓝 0))
    {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hl1 : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    F =ᵐ[volume.restrict (standardCylinder R)] {x : AmbientSpace | x 2 < 0} := by
  have hU := isOpen_standardCylinder R
  have hcU : Convex ℝ (standardCylinder R) := by
    rw [standardCylinder_eq_cylinder]
    exact convex_cylinder _ _ _
  have hzero : (0 : AmbientSpace) ∈ standardCylinder R := by
    change ‖graphProjectionN 2 0‖ < R ∧ |(0 : AmbientSpace) 2| < R
    simpa using And.intro hR hR
  obtain ⟨μ, _, _, hp⟩ := exists_small_excess_constant_polar_limit hE hω
    (isBounded_standardCylinder R) (EuclideanSpace.single 2 1) he hmF hl1
  have hph := IsOmegaMinimal.limit_two_phases hE hω h0
    (tendsto_const_nhds (x := (0 : AmbientSpace))) hmF hU hzero
    (fun K hK _ => hl1 K hK)
  rcases hp.classification hmF (by simp) hU hcU (isBounded_standardCylinder R)
      with he | he | ⟨c, he⟩
  · exact False.elim ((ne_of_gt hph.1) (volume_inter_zero_of_ae_empty hmF he))
  · exact False.elim ((ne_of_gt hph.2) (volume_compl_inter_zero_of_ae_full hmF he))
  · have he' : F =ᵐ[volume.restrict (standardCylinder R)] {x : AmbientSpace | x 2 < c} := by
      simpa only [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul] using he
    have hc := IsOmegaMinimal.limit_boundary_height_eq hE hω h0
      (tendsto_const_nhds (x := (0 : AmbientSpace))) hmF hU hzero
      (fun K hK _ => hl1 K hK) he'
    have hc0 : c = 0 := by simpa using hc.symm
    simpa only [hc0] using he'

lemma closure_standardCylinder_subset {r R : ℝ} (hrR : r < R) :
    closure (standardCylinder r) ⊆ standardCylinder R := by
  have hclosed : IsClosed {x : AmbientSpace |
      ‖graphProjectionN 2 x‖ ≤ r ∧ |x 2| ≤ r} :=
    (isClosed_le
      (show Continuous (fun x : AmbientSpace => ‖graphProjectionN 2 x‖) by fun_prop)
      continuous_const).inter
      (isClosed_le (show Continuous (fun x : AmbientSpace => |x 2|) by fun_prop) continuous_const)
  have hsub := closure_minimal (show standardCylinder r ⊆
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ ≤ r ∧ |x 2| ≤ r} from
        fun _ hx => ⟨hx.1.le, hx.2.le⟩) hclosed
  exact fun _ hx => ⟨((hsub hx).1).trans_lt hrR, ((hsub hx).2).trans_lt hrR⟩

end LiquidDrop
