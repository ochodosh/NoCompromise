import NoCompromise.Surface.MorseChart
import NoCompromise.Surface.MorseModel
import NoCompromise.Surface.MorseSectors

/-!
# Morse charts on an embedded surface

`lem:morse-coords` transported to a critical point of a smooth function on an embedded
surface, and `lem:local-sectors` on the surface. The planar Morse lemma enters through
`MorseCoordsStatement` (C¹ charts, pending the user's wording decision on C¹ versus smooth).
-/

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The planar Morse lemma `lem:morse-coords` at C¹ regularity (C¹ pending the user's wording
decision): a `C³` function vanishing to second order at `0` with nondegenerate Hessian is the
model form of its index in a C¹ chart with C¹ inverse. -/
def MorseCoordsStatement : Prop :=
  ∀ g : E2 → ℝ, ContDiffAt ℝ 3 g 0 → g 0 = 0 → fderiv ℝ g 0 = 0 →
    IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w) →
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ x ∈ e.source,
        g x = morseModel (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) (e x)

variable {S : Set E₃}

/-- `lem:morse-coords` on the surface: at a nondegenerate critical point `p` of a smooth `h`,
there is a chart of the surface around `p`, sending `p` to `0`, whose source is the trace of
an ambient open set, in which `h = h p + (model form of index surfaceIndex S n h p)`.
PARTIAL: the planar Morse lemma is the named hypothesis `h_morse_coords`. -/
theorem exists_surface_morse_chart {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p))
    (h_morse_coords : MorseCoordsStatement) :
    ∃ (E : OpenPartialHomeomorph S E2) (U : Set E₃),
      IsOpen U ∧ p ∈ U ∧ E.source = Subtype.val ⁻¹' U ∧
      (⟨p, hcrit.1⟩ : S) ∈ E.source ∧ E ⟨p, hcrit.1⟩ = 0 ∧
      ∀ x ∈ E.source, h x = h p + morseModel (surfaceIndex S n h p) (E x) := by
  obtain ⟨e, P, U, hU, hpU, hsrc, hps, he0, heP, hC, hgC, hg0, hgd, hnd', hidx⟩ :=
    exists_chart_pullback hS hn hh hcrit
  obtain ⟨eM, h0M, heM0, -, -, hmodel⟩ :=
    h_morse_coords _ hgC hg0 hgd (hnd'.mpr hnd)
  rw [hidx] at hmodel
  let E := e.trans eM
  have hPc : Continuous (fun x : E₃ => P (x - p)) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  refine ⟨E, U ∩ (fun x => P (x - p)) ⁻¹' eM.source,
    hU.inter (eM.open_source.preimage hPc), ⟨hpU, ?_⟩, ?_, ?_, ?_, ?_⟩
  · change P (p - p) ∈ eM.source
    simpa using h0M
  · ext x
    simp only [E, OpenPartialHomeomorph.trans_source, hsrc, mem_inter_iff, mem_preimage,
      heP]
  · refine ⟨hps, ?_⟩
    change e ⟨p, hcrit.1⟩ ∈ eM.source
    rw [he0]; exact h0M
  · change eM (e ⟨p, hcrit.1⟩) = 0
    rw [he0, heM0]
  · intro x hx
    have hxe : x ∈ e.source := hx.1
    have hxM : e x ∈ eM.source := hx.2
    have h1 := hmodel (e x) hxM
    have h2 : chartPullback e h p (e x) = h x - h p := by
      simp only [chartPullback, e.left_inv hxe]
    change h x = h p + morseModel (surfaceIndex S n h p) (eM (e x))
    linarith

/-- `lem:local-sectors` on the surface: around a nondegenerate critical point `p` of a smooth
`h` there is a Morse chart `E` of the surface and a coordinate disk `D = E⁻¹(morseDisk ρ)` on
which the sets `{h < c}`, `{h = c}`, `{h > c}` (`c = h p`) are the chart images of the model sets
of `lem:local-sectors`: (i) index `0`: empty, the point `p`, the punctured disk; (ii) index `2`:
the punctured disk, the point `p`, empty; (iii) index `1`: the two sectors `S⁻₁₂ ∪ S⁻₃₄`, the
point `p` with the four rays, and the two sectors `S⁺₂₃ ∪ S⁺₄₁` (connectedness, closure and
flanking relations transport by `morse_model_connected_transport`,
`morse_model_closure_transport` and the model lemmas of `MorseSectors.lean`).
PARTIAL: the planar Morse lemma is the named hypothesis `h_morse_coords`. -/
theorem exists_surface_local_sectors {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p))
    (h_morse_coords : MorseCoordsStatement) :
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
          E.symm '' (morseSp23 ρ ∪ morseSp41 ρ)) := by
  obtain ⟨E, U, hU, -, hsrc, hps, hE0, hmodel⟩ :=
    exists_surface_morse_chart hS hn hh hcrit hnd h_morse_coords
  have h0t : (0 : E2) ∈ E.target := hE0 ▸ E.map_source hps
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp E.open_target 0 h0t
  have hD : morseDisk ρ ⊆ E.target := hball
  have hsymm0 : E.symm 0 = ⟨p, hcrit.1⟩ := by
    rw [← hE0]; exact E.left_inv hps
  have hsing : E.symm '' {(0 : E2)} = {⟨p, hcrit.1⟩} := by
    rw [image_singleton, hsymm0]
  refine ⟨E, U, ρ, hU, hsrc, hρ, hD, hps, hE0, ?_, ?_, ?_⟩
  · intro hk
    rw [hk] at hmodel
    obtain ⟨h1, h2, h3⟩ := morse_model_sets_transport E hD (fun x : S => h x) (morseModel 0)
      hmodel
    obtain ⟨m1, m2, m3⟩ := morse_index_zero_sets hρ
    have hm : morseModel 0 = fun y : E2 => y 0 ^ 2 + y 1 ^ 2 := by
      funext y; simp [morseModel]
    rw [hm] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, m1, image_empty]
    · rw [h2, m3, hsing]
    · rw [h3, m2]
  · intro hk
    rw [hk] at hmodel
    obtain ⟨h1, h2, h3⟩ := morse_model_sets_transport E hD (fun x : S => h x) (morseModel 2)
      hmodel
    obtain ⟨m1, m2, m3⟩ := morse_index_two_sets hρ
    have hm : morseModel 2 = fun y : E2 => -(y 0 ^ 2 + y 1 ^ 2) := by
      funext y; simp [morseModel]; ring
    rw [hm] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, m2]
    · rw [h2, m3, hsing]
    · rw [h3, m1, image_empty]
  · intro hk
    rw [hk] at hmodel
    obtain ⟨h1, h2, h3⟩ := morse_model_sets_transport E hD (fun x : S => h x) (morseModel 1)
      hmodel
    have hm : morseModel 1 = fun y : E2 => y 0 ^ 2 - y 1 ^ 2 := by
      funext y; simp [morseModel]
    rw [hm] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, morse_saddle_negative_set]
    · rw [h2, morse_saddle_zero_set hρ]
    · rw [h3, morse_saddle_positive_set]

end LiquidDrop
