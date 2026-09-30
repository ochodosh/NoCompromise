module

public import NoCompromise.Elliptic.NeumannInterior

@[expose] public section

/-!
# Smooth interior representatives and their agreement on overlaps

Constant-source weak Neumann solutions have an interior smooth representative
whose Hessian trace is the source and whose classical gradient is the original
weak gradient. Continuous representatives agree on open overlaps and, when
continuous there, on overlaps with the closure of the domain.
-/

noncomputable section

open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient

namespace LiquidDrop

/-- A constant-source weak Neumann solution has a smooth interior representative
with the pointwise Hessian-trace equation and the original weak gradient. -/
theorem IsWeakNeumannSolution.exists_smooth_interior_representative
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {c : ℝ} (hf : ⇑f =ᵐ[volume.restrict D] fun _ => c) :
    ∃ v : AmbientSpace → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v D ∧
      ⇑z =ᵐ[volume.restrict D] v ∧ (∀ x ∈ D, laplacianTrace v x = c) ∧
      gradient v =ᵐ[volume.restrict D] z.gradientLp := by
  have hq := contDiff_neumannQuadratic c
  have hqL : MemLp (fun x : AmbientSpace => c * ‖x‖ ^ 2 / 6) 2
      (volume.restrict D) := by
    let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hbD.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hbD.isCompact_closure.exists_bound_of_continuousOn hq.continuous.continuousOn
    apply MemLp.of_bound hq.continuous.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact hC x (subset_closure hx)
  have hloc : HasSobolevOrderLocallyOn 0
      (fun x => z x - c * ‖x‖ ^ 2 / 6) D := by
    intro x hx
    obtain ⟨r, hr, hs⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
    exact ⟨r, hr, hs, (z.hasH1GradientOn.memLp_function.sub hqL).mono_measure
      (Measure.restrict_mono hs le_rfl)⟩
  obtain ⟨w, hw, he, hzero⟩ :=
    (hz.sub_quadratic_harmonic hf).harmonic_smooth (by norm_num : 3 < 4) hloc
  let v : AmbientSpace → ℝ := fun x => w x + c * ‖x‖ ^ 2 / 6
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) v D := hw.add hq.contDiffOn
  have hev : ⇑z =ᵐ[volume.restrict D] v := by
    filter_upwards [he] with x hx
    dsimp [v]
    rw [hx]
    ring
  refine ⟨v, hv, hev, ?_, ?_⟩
  · intro x hx
    have hwx : ContDiffAt ℝ 2 w x := (hw.of_le (by simp)).contDiffAt (hD.mem_nhds hx)
    rw [laplacianTrace_eq_laplacianN ((hv.of_le (by simp)).contDiffAt (hD.mem_nhds hx))]
    change laplacianN (fun y => w y + c * ‖y‖ ^ 2 / 6) x = c
    rw [laplacianN_add_of_contDiffAt hwx (hq.of_le (by simp)).contDiffAt,
      hzero x hx, laplacianN_neumannQuadratic, zero_add]
  · exact (hasWeakGradientOn_of_contDiffOn hD (hv.of_le (by simp))).unique hD
      (z.hasH1GradientOn.toHasWeakGradientOn.congr_ae hev EventuallyEq.rfl)

/-- Two continuous representatives of the same a.e. class agree on an open
overlap; the second representative only needs continuity on the domain. -/
theorem neumannInterior_eqOn_overlap
    {D V : Set AmbientSpace} (hD : IsOpen D) (hV : IsOpen V)
    {z v₁ v₂ : AmbientSpace → ℝ}
    (hv₁ : ContinuousOn v₁ (V ∩ D)) (hv₂ : ContinuousOn v₂ D)
    (he₁ : v₁ =ᵐ[volume.restrict (V ∩ D)] z)
    (he₂ : v₂ =ᵐ[volume.restrict (V ∩ D)] z) : EqOn v₁ v₂ (V ∩ D) :=
  Measure.eqOn_open_of_ae_eq (he₁.trans he₂.symm) (hV.inter hD) hv₁
    (hv₂.mono inter_subset_right)

/-- Agreement of continuous representatives extends to the part of the domain
closure lying in the open chart. Neither representative needs global continuity. -/
theorem neumannInterior_eqOn_closure_overlap
    {D V : Set AmbientSpace} (hD : IsOpen D) (hV : IsOpen V)
    {z v₁ v₂ : AmbientSpace → ℝ}
    (hv₁ : ContinuousOn v₁ (closure D ∩ V))
    (hv₂ : ContinuousOn v₂ (closure D ∩ V))
    (he₁ : v₁ =ᵐ[volume.restrict (D ∩ V)] z)
    (he₂ : v₂ =ᵐ[volume.restrict (D ∩ V)] z) : EqOn v₁ v₂ (closure D ∩ V) := by
  have hs : D ∩ V ⊆ closure D ∩ V := inter_subset_inter_left V subset_closure
  have he : EqOn v₁ v₂ (D ∩ V) :=
    Measure.eqOn_open_of_ae_eq (he₁.trans he₂.symm) (hD.inter hV)
      (hv₁.mono hs) (hv₂.mono hs)
  exact he.of_subset_closure hv₁ hv₂ hs hV.closure_inter

end LiquidDrop
