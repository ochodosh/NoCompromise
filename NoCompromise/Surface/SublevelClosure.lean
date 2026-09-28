import NoCompromise.Surface.SublevelClosureZero
import NoCompromise.Surface.SublevelClosureTwo
import NoCompromise.Surface.SublevelClosureCount
import NoCompromise.Surface.SublevelClosureMerge
import NoCompromise.Surface.MorseDischarged

/-!
# `lem:sublevel-closure`

Closing up the sublevel `S ∩ {h < c}` at a critical level `c` with unique critical point `p`
adds one component at a minimum, removes one at a sub-merging saddle, and changes nothing
otherwise.
-/

noncomputable section

open Set

namespace LiquidDrop

variable {S : Set E₃}

/-- `lem:sublevel-closure`, the case "otherwise": at a critical point of index `1` or `2` that is
not a sub-merging saddle, `#comp {h ≤ c} = #comp {h < c}`. -/
theorem componentCount_sublevel_closure_otherwise {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) (hk : surfaceIndex S n h p ≠ 0)
    (hns : ¬ IsSubMergingSaddle S n h p) :
    componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) := by
  have hle : surfaceIndex S n h p ≤ 2 := surfaceIndex_le_two hS hp.1
  rcases (show surfaceIndex S n h p = 1 ∨ surfaceIndex S n h p = 2 by omega) with h1 | h2
  · exact componentCount_sublevel_closure_saddle_of_not_subMerging hS hn hh hM hinj hp h1 hns
  · exact componentCount_sublevel_closure_index_two hS hn hh hM hinj hp h2

/-- `lem:sublevel-closure` (proved): for a smooth Morse function with distinct critical values
on an embedded surface and a critical point `p`, `#comp {h ≤ h p} - #comp {h < h p}` is `+1` at
an index-zero point, `-1` at a sub-merging saddle, and `0` otherwise. This is exactly the
named hypothesis `h_closure` of `count_submerging`. -/
theorem sublevel_closure {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hM : IsSurfaceMorse S n h) (hinj : InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) :
      (surfaceIndex S n h p = 0 →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) + 1) ∧
      (IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) + 1 = componentCount (S ∩ {x | h x < h p})) ∧
      (surfaceIndex S n h p ≠ 0 → ¬ IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p})) :=
  ⟨componentCount_sublevel_closure_index_zero hS hn hh hM hinj hp,
    componentCount_sublevel_closure_subMerging hS hn hh hM hinj,
    componentCount_sublevel_closure_otherwise hS hn hh hM hinj hp⟩

/-- `lem:count-submerging` (proved): a smooth Morse function with distinct critical values on a
compact connected embedded surface has `c₀ - 1` sub-merging and `c₂ - 1` super-merging
saddles. -/
theorem count_submerging_unconditional {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hM : IsSurfaceMorse S n h) (hinj : InjOn h {p | IsSurfaceCriticalPoint S h p}) :
    {p | IsSubMergingSaddle S n h p}.ncard + 1 = morseCount S n h 0 ∧
      {p | IsSuperMergingSaddle S n h p}.ncard + 1 = morseCount S n h 2 :=
  count_submerging_of_closure hS hc hconn hn
    (fun _ hh' hM' hinj' _ hp => sublevel_closure hS hn hh' hM' hinj' hp) hh hM hinj

/-- prop:morse-count, PARTIAL: `c₀ - c₁ + c₂ ≤ 2` for every smooth Morse function on a compact
connected embedded surface; the only remaining named hypothesis is `h_merge_disjoint`
(lem:merge-disjoint), exactly as in `morse_count_le_two`. -/
theorem morse_count_le_two_of_merge_disjoint {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_merge_disjoint : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} →
      ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p))
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h) :
    (morseCount S n h 0 : ℤ) - morseCount S n h 1 + morseCount S n h 2 ≤ 2 :=
  morse_count_le_two_of_closure hS hc hconn hn
    (fun _ hh' hM' hinj' _ hp => sublevel_closure hS hn hh' hM' hinj' hp) h_merge_disjoint hh hM

open MeasureTheory in
/-- thm:total-curvature-bound, PARTIAL, for a compact connected surface: `∫_Σ κ dH² ≤ 4π`, with
cor:sublevel-stable and lem:sublevel-closure discharged. The remaining named hypotheses are
`h_sard_charts` (cor:sard-charts), `h_merge_disjoint` (lem:merge-disjoint) and
`h_total_curvature_index` (thm:total-curvature-index), exactly as in
`total_curvature_le_of_morse_merge`. -/
theorem total_curvature_le_of_merge_disjoint {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_sard_charts : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y)
    (h_merge_disjoint : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} →
      ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p))
    (h_total_curvature_index :
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_closure_merge hS hc hconn hn h_sard_charts
    (fun _ hh' hM' hinj' _ hp => sublevel_closure hS hn hh' hM' hinj' hp) h_merge_disjoint
    h_total_curvature_index

end LiquidDrop
