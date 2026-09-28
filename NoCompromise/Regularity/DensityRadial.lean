import NoCompromise.BV.RadialCuts
import NoCompromise.DeGiorgi.DensityFlux

/-!
# Radial volume derivatives and exact cuts

These identities need only Lebesgue measurability and locally finite perimeter;
quasiminimality and membership in the essential boundary are unnecessary here.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma hasDerivAt_radialVolume_compl {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) {r d : ℝ} (hr : 0 < r)
    (hd : HasDerivAt (radialVolume E x) d r) :
    HasDerivAt (radialVolume Eᶜ x) (4 * Real.pi * r ^ 2 - d) r := by
  have hp : HasDerivAt (fun t : ℝ => (4 * Real.pi / 3) * t ^ 3)
      (4 * Real.pi * r ^ 2) r := by
    convert! ((hasDerivAt_id r).pow 3).const_mul (4 * Real.pi / 3) using 1
    simp only [id_eq]
    ring
  apply (hp.sub hd).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  have h := radialVolume_add_compl hmE x ht.le
  dsimp only [Pi.sub_apply]
  linarith

/-- Blueprint `lem:mx-derivative`: genuine derivatives of both radial phase
volumes, together with the exact inside and outside perimeter cuts, at almost
every positive radius. -/
theorem ae_radial_derivatives_and_cut_identities (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (x : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      HasDerivAt (radialVolume E x) (radialSectionArea E x r) r ∧
      HasDerivAt (radialVolume Eᶜ x) (4 * Real.pi * r ^ 2 - radialSectionArea E x r) r ∧
      IsGoodRadius E hE hmE x r ∧
      perimeter (E ∩ ball x r) = perimeterIn E (ball x r) +
        hausdorffMeasure2 3 (densityOne E ∩ sphere x r) ∧
      perimeter (E \ ball x r) = perimeterIn E (closedBall x r)ᶜ +
        hausdorffMeasure2 3 (densityOne E ∩ sphere x r) := by
  filter_upwards [ae_isGoodRadius E hE hmE x,
    ae_restrict_of_ae (ae_hasDerivAt_radialVolume hmE x)] with r hg hd
  exact ⟨hd hg.1, hasDerivAt_radialVolume_compl hmE x hg.1 (hd hg.1), hg,
    hg.perimeter_cut_identities⟩

/-- The derivative version of the same full radial assertion. -/
theorem ae_radial_deriv_and_cut_identities (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (x : AmbientSpace) :
    ∀ᵐ r : ℝ, 0 < r →
      deriv (radialVolume E x) r = radialSectionArea E x r ∧
      deriv (radialVolume Eᶜ x) r = 4 * Real.pi * r ^ 2 - deriv (radialVolume E x) r ∧
      IsGoodRadius E hE hmE x r ∧
      perimeter (E ∩ ball x r) = perimeterIn E (ball x r) +
        hausdorffMeasure2 3 (densityOne E ∩ sphere x r) ∧
      perimeter (E \ ball x r) = perimeterIn E (closedBall x r)ᶜ +
        hausdorffMeasure2 3 (densityOne E ∩ sphere x r) := by
  have h := (ae_restrict_iff' measurableSet_Ioi).mp
    (ae_radial_derivatives_and_cut_identities E hE hmE x)
  filter_upwards [h] with r hr hrpos
  obtain ⟨hd, hc, hg, hcuts⟩ := hr hrpos
  exact ⟨hd.deriv, by rw [hd.deriv]; exact hc.deriv, hg, hcuts⟩

end LiquidDrop
