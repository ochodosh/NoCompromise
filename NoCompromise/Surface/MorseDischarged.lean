module

public import NoCompromise.Surface.MorseCoordsPlanar
public import NoCompromise.Surface.SublevelStable

@[expose] public section

/-!
# Chapter 14 results with the planar Morse lemma and cor:sublevel-stable discharged

`lem:morse-coords` and `lem:local-sectors` on an embedded surface, now unconditional (charts are
C¹ in the planar step, pending the user's wording decision), and thm:total-curvature-bound with
cor:sublevel-stable discharged.
-/

noncomputable section

open Set Function InnerProductSpace

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- `lem:morse-coords` on the surface: at a nondegenerate critical point `p` of a smooth `h`
there is a chart of the surface around `p`, sending `p` to `0`, whose source is the trace of an
ambient open set, in which `h = h p + (model form of index surfaceIndex S n h p)`.
`exists_surface_morse_chart` with `MorseCoordsStatement` discharged by `morseCoordsStatement`. -/
theorem surface_morse_chart {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) :
    ∃ (E : OpenPartialHomeomorph S E2) (U : Set E₃),
      IsOpen U ∧ p ∈ U ∧ E.source = Subtype.val ⁻¹' U ∧
      (⟨p, hcrit.1⟩ : S) ∈ E.source ∧ E ⟨p, hcrit.1⟩ = 0 ∧
      ∀ x ∈ E.source, h x = h p + morseModel (surfaceIndex S n h p) (E x) :=
  exists_surface_morse_chart hS hn hh hcrit hnd morseCoordsStatement

/-- `lem:local-sectors` on the surface: `exists_surface_local_sectors` with
`MorseCoordsStatement` discharged by `morseCoordsStatement`. -/
theorem surface_local_sectors {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) :
    ∃ (E : OpenPartialHomeomorph S E2) (U : Set E₃) (ρ : ℝ),
      IsOpen U ∧ E.source = Subtype.val ⁻¹' U ∧ 0 < ρ ∧ morseDisk ρ ⊆ E.target ∧
      (⟨p, hcrit.1⟩ : S) ∈ E.source ∧ E ⟨p, hcrit.1⟩ = 0 ∧
      (surfaceIndex S n h p = 0 →
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x < h p} = ∅ ∧
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x = h p} = {⟨p, hcrit.1⟩} ∧
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h p < h x} = E.symm '' (morseDisk ρ \ {0})) ∧
      (surfaceIndex S n h p = 2 →
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x < h p} = E.symm '' (morseDisk ρ \ {0}) ∧
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x = h p} = {⟨p, hcrit.1⟩} ∧
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h p < h x} = ∅) ∧
      (surfaceIndex S n h p = 1 →
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x < h p} =
          E.symm '' (morseSm12 ρ ∪ morseSm34 ρ) ∧
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x = h p} =
          E.symm '' ({0} ∪ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ) ∧
        {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h p < h x} =
          E.symm '' (morseSp23 ρ ∪ morseSp41 ρ)) :=
  exists_surface_local_sectors hS hn hh hcrit hnd morseCoordsStatement

open MeasureTheory in
/-- thm:total-curvature-bound, PARTIAL, for a compact connected surface: `∫_Σ κ dH² ≤ 4π`, as
`total_curvature_le_of_morse_merge` with cor:sublevel-stable (i), (ii) discharged by
`componentCount_sublevel_closed` and `componentCount_sublevel_open`. The remaining named
hypotheses are `h_sard_charts` (cor:sard-charts), `h_closure` (lem:sublevel-closure),
`h_merge_disjoint` (lem:merge-disjoint) and `h_total_curvature_index`
(thm:total-curvature-index), exactly as in `total_curvature_le_of_morse_merge`. -/
theorem total_curvature_le_of_closure_merge {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_sard_charts : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y)
    (h_closure : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ p, IsSurfaceCriticalPoint S h p →
      (surfaceIndex S n h p = 0 →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) + 1) ∧
      (IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) + 1 = componentCount (S ∩ {x | h x < h p})) ∧
      (surfaceIndex S n h p ≠ 0 → ¬ IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p})))
    (h_merge_disjoint : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} →
      ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p))
    (h_total_curvature_index :
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_morse_merge hS hc hconn hn h_sard_charts
    (fun _ hh' _ _ _ _ hab hreg => componentCount_sublevel_closed hS hc hn hh' hab hreg)
    (fun _ hh' _ _ _ _ hab hreg => componentCount_sublevel_open hS hc hn hh' hab hreg)
    h_closure h_merge_disjoint h_total_curvature_index

end LiquidDrop
