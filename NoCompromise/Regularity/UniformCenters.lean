module

public import NoCompromise.Regularity.EpsReg

@[expose] public section

/-!
# Uniform smallness at every nearby boundary centre

Blueprint `lem:uniform-centers`. The change-of-centre estimate
`excess_change_center` turns one small-excess hypothesis at `(x, r)` into the
same smallness hypothesis at every boundary point of the eighth cylinder, at
scale `r / 8`. Consequently the normal-selection statement `normals_cauchy`
runs at all those centres with the single threshold fixed in advance.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace LiquidDrop

/-- Blueprint `lem:uniform-centers`, transfer of the smallness hypothesis.
The threshold `ε'` is chosen before all geometric data, and the conclusion is
the hypothesis `(eq:eps-reg-hyp)` at the new centre `z` and scale `r / 8`. -/
theorem uniform_centers_smallness :
    ∀ ε > 0, ∃ ε' > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν‖ = 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν + ω * r ≤ ε' →
      ∀ z ∈ frontier (densityOne E) ∩ cylinder x (r / 8) ν,
        cylindricalExcess E hE.locallyFinite hE.nullMeasurable z (r / 8) ν +
          ω * (r / 8) ≤ ε := by
  intro ε hε
  refine ⟨ε / 64, by positivity, ?_⟩
  intro E ω hE x r ν hr _ hν hsmall z hz
  have hcenter := excess_change_center E hE.locallyFinite hE.nullMeasurable hr hν hz.2
  have hωr : 0 ≤ ω * r := mul_nonneg hE.nonneg hr.le
  linarith

/-- Blueprint `lem:uniform-centers`, the iteration itself. With a single
threshold `ε₀'` fixed in advance, the full conclusion of `normals_cauchy`
holds at every boundary centre `z` of the eighth cylinder, at scale `r / 8`
and with the same initial axis `ν₀`. -/
theorem normals_cauchy_uniform_centers :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 32 ∧ ∃ ε₀' > 0, ∃ C > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε₀' →
      ∀ z ∈ frontier (densityOne E) ∩ cylinder x (r / 8) ν₀,
      ∃ (ν : ℕ → AmbientSpace) (νlim : AmbientSpace),
        ν 0 = ν₀ ∧ (∀ j, ‖ν j‖ = 1) ∧ ‖νlim‖ = 1 ∧ Tendsto ν atTop (𝓝 νlim) ∧
        let e := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable
          z (θ ^ j * (r / 8)) (ν j)
        ∀ j, e j + ω * (θ ^ j * (r / 8)) ≤ 64 * ε₀' ∧
          e j + ω * (θ ^ j * (r / 8)) ≤ C * θ ^ j * (e 0 + ω * (r / 8)) ∧
          ‖ν (j + 1) - ν j‖ ^ 2 ≤ C * (e j + ω * (θ ^ j * (r / 8))) ∧
          ‖ν j - νlim‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt (e 0 + ω * (r / 8)) := by
  obtain ⟨θ, hθ, hθ32, ε, hε, C, hC, hmain⟩ := normals_cauchy
  refine ⟨θ, hθ, hθ32, ε / 64, by positivity, C, hC, ?_⟩
  intro E ω hE x r ν₀ hr hr1 hν₀ _ hsmall z hz
  have hr8 : 0 < r / 8 := by linarith
  have hr81 : r / 8 ≤ 1 := by linarith
  have hcenter := excess_change_center E hE.locallyFinite hE.nullMeasurable hr hν₀ hz.2
  have hωr : 0 ≤ ω * r := mul_nonneg hE.nonneg hr.le
  have hsmall' :
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable z (r / 8) ν₀ +
        ω * (r / 8) ≤ ε := by linarith
  obtain ⟨ν, νlim, hinit, hunit, hnlim, htend, hrest⟩ :=
    hmain E ω hE z (r / 8) ν₀ hr8 hr81 hν₀ hz.1 hsmall'
  refine ⟨ν, νlim, hinit, hunit, hnlim, htend, ?_⟩
  dsimp only
  intro j
  obtain ⟨hs, henergy, hincr, hrate⟩ := hrest j
  exact ⟨by linarith, henergy, hincr, hrate⟩

end LiquidDrop
