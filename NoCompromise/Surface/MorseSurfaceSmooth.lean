module

public import NoCompromise.Surface.MorseCoordsSmooth
public import NoCompromise.Surface.SurfaceChartSmooth

@[expose] public section

/-!
# `lem:morse-coords` on an embedded surface with smooth coordinates

At a nondegenerate critical point `p` of a smooth function `h` on an embedded surface `Σ`
there is a chart of `Σ` around `p` which is smooth in both directions (the forward map is the
restriction to `Σ` of a `C^∞` map on an ambient open set, the inverse is `C^∞` as a map into
`ℝ³`), sending `p` to `0`, in which `h = h(p) + (model form eq:morse-normal-form of index
surfaceIndex S n h p)`. The planar input is `exists_morse_coords_smooth`
(`NoCompromise.Surface.MorseCoordsSmooth`), the chart input `exists_chart_pullback_smooth`
(`NoCompromise.Surface.SurfaceChartSmooth`).
-/

noncomputable section

open Set Function

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- `lem:morse-coords` on the surface with smooth coordinates: at a nondegenerate critical point
`p` of a smooth `h` there is a chart `E` of the surface around `p`, sending `p` to `0`, whose
source is the trace of an ambient open set `U`, which is the restriction of a map `F` that is
`C^∞` on `U`, whose inverse is `C^∞` (as a map into `ℝ³`) on its target, and in which
`h = h p + (model form eq:morse-normal-form of index surfaceIndex S n h p)`. -/
theorem surface_morse_chart_smooth {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) :
    ∃ (E : OpenPartialHomeomorph S E2) (U : Set E₃) (F : E₃ → E2),
      IsOpen U ∧ p ∈ U ∧ E.source = Subtype.val ⁻¹' U ∧
      (⟨p, hcrit.1⟩ : S) ∈ E.source ∧ E ⟨p, hcrit.1⟩ = 0 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) F U ∧ (∀ x : S, E x = F x) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (E.symm y : E₃)) E.target ∧
      ∀ x ∈ E.source, h x = h p + morseModel (surfaceIndex S n h p) (E x) := by
  obtain ⟨e, P, U, hU, hpU, hsrc, hps, he0, heP, hψC, hgC, hg0, hgd, hnd', hidx⟩ :=
    exists_chart_pullback_smooth hS hn hh hcrit
  have h0t : (0 : E2) ∈ e.target := he0 ▸ e.map_source hps
  obtain ⟨eM, h0M, heM0, hMt, hMC, hMiC, hmodel⟩ :=
    exists_morse_coords_smooth e.open_target h0t hgC hg0 hgd (hnd'.mpr hnd)
  rw [hidx] at hmodel
  let E := e.trans eM
  let π : E₃ → E2 := fun x => P (x - p)
  have hπC : ContDiff ℝ (⊤ : ℕ∞) π := P.contDiff.comp (contDiff_id.sub contDiff_const)
  let U' : Set E₃ := U ∩ π ⁻¹' eM.source
  have hEF : ∀ x : S, E x = eM (π x) := fun x => by
    change eM (e x) = eM (P ((x : E₃) - p))
    rw [heP]
  refine ⟨E, U', fun x => eM (π x), hU.inter (eM.open_source.preimage hπC.continuous),
    ⟨hpU, ?_⟩, ?_, ?_, ?_, ?_, hEF, ?_, ?_⟩
  · change P (p - p) ∈ eM.source
    simpa using h0M
  · ext x
    simp only [E, U', π, OpenPartialHomeomorph.trans_source, hsrc, mem_inter_iff, mem_preimage,
      heP]
  · refine ⟨hps, ?_⟩
    change e ⟨p, hcrit.1⟩ ∈ eM.source
    rw [he0]; exact h0M
  · change eM (e ⟨p, hcrit.1⟩) = 0
    rw [he0, heM0]
  · exact hMC.comp hπC.contDiffOn fun x hx => hx.2
  · have hsymm : (fun y => (E.symm y : E₃)) = (fun y => (e.symm y : E₃)) ∘ eM.symm := rfl
    rw [hsymm, OpenPartialHomeomorph.trans_target]
    exact hψC.comp (hMiC.mono inter_subset_left) fun y hy => hy.2
  · intro x hx
    have hxe : x ∈ e.source := hx.1
    have hxM : e x ∈ eM.source := hx.2
    have h1 := hmodel (e x) hxM
    have h2 : chartPullback e h p (e x) = h x - h p := by
      simp only [chartPullback, e.left_inv hxe]
    change h x = h p + morseModel (surfaceIndex S n h p) (eM (e x))
    linarith

end LiquidDrop
