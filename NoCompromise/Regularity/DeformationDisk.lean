module

public import NoCompromise.Regularity.SlabCapArea
public import NoCompromise.Regularity.SlabGeometry
public import NoCompromise.DeGiorgi.SmoothGraph

@[expose] public section

/-! # Exact disk perimeter of the flattened core -/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace LiquidDrop

def cylindricalCore (r σ : ℝ) : Set AmbientSpace :=
  {x | ‖graphProjectionN 2 x‖ < σ} ∩ standardCylinder r

lemma isOpen_cylindricalCore (r σ : ℝ) : IsOpen (cylindricalCore r σ) :=
  (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const).inter
    (isOpen_standardCylinder r)

lemma cylindricalCore_inter_horizontal_graph {r σ c : ℝ} (hσr : σ ≤ r) (hc : |c| < r) :
    cylindricalCore r σ ∩ range (graphMapN (fun _ : EuclideanSpace ℝ (Fin 2) => c)) =
      cylindricalCap σ c := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    refine ⟨p, ?_, rfl⟩
    have hh := hx.1
    change ‖graphProjectionN 2 (graphAppendN p c)‖ < σ at hh
    simpa only [mem_ball, dist_zero_right, graphProjectionN_append] using hh
  · rintro ⟨p, hp, rfl⟩
    have hp' : ‖p‖ < σ := by simpa only [mem_ball, dist_zero_right] using hp
    refine ⟨⟨?_, ?_, ?_⟩, ⟨p, rfl⟩⟩
    · simpa only [mem_ofPred_eq, graphProjectionN_append] using hp'
    · simpa only [graphProjectionN_append] using hp'.trans_le hσr
    · simpa only [graphAppendN_height_three] using hc

theorem perimeterIn_horizontal_halfspace_core {r σ c : ℝ}
    (hσ : 0 ≤ σ) (hσr : σ ≤ r) (hc : |c| < r) :
    perimeterIn {x : AmbientSpace | x 2 < c} (cylindricalCore r σ) =
      ENNReal.ofReal (Real.pi * σ ^ 2) := by
  change perimeterIn (smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin 2) => c))
    (cylindricalCore r σ) = _
  rw [perimeterIn_smoothSubgraph contDiff_const (isOpen_cylindricalCore r σ),
    smoothGraphArea, Measure.restrict_apply (isOpen_cylindricalCore r σ).measurableSet,
    cylindricalCore_inter_horizontal_graph hσr hc]
  change hausdorffMeasure2 3 (cylindricalCap σ c) = _
  rw [hausdorffMeasure2_cylindricalCap, EuclideanSpace.volume_ball_fin_two,
    ← ENNReal.ofReal_pow hσ, ← ENNReal.ofReal_mul (sq_nonneg σ)]
  congr 1
  ring

theorem perimeterIn_core_eq_disk_of_ae_phase {F : Set AmbientSpace} {r σ c : ℝ}
    (hσ : 0 ≤ σ) (hσr : σ ≤ r) (hc : |c| < r)
    (hphase : F.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict (cylindricalCore r σ)]
      {x : AmbientSpace | x 2 < c}.indicator (fun _ => (1 : ℝ))) :
    perimeterIn F (cylindricalCore r σ) = ENNReal.ofReal (Real.pi * σ ^ 2) := by
  exact (variation_congr_ae _ hphase).trans (perimeterIn_horizontal_halfspace_core hσ hσr hc)

end LiquidDrop
