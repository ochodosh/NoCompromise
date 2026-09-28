import NoCompromise.DeGiorgi.BlowupLimits
import NoCompromise.DeGiorgi.HalfspaceRigidity
import NoCompromise.DeGiorgi.BlowupPolar
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Identification and convergence of perimeter blow-ups

The compactness and quantitative density theorems apply to every reduced point.
A constant-polar limit is therefore the halfspace through the origin with the
prescribed outward normal. Sequential extraction then gives the full radius limit.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- A positive-radius limit follows from subsequential convergence along every
positive sequence of radii tending to zero. No monotonicity of the radii is assumed. -/
lemma tendsto_nhdsGT_of_positive_sequences_subseq {g : ℝ → ℝ} {a : ℝ}
    (hg : ∀ r : ℕ → ℝ, (∀ j, 0 < r j) → Tendsto r atTop (𝓝 0) →
      ∃ σ : ℕ → ℕ, Tendsto (fun j => g (r (σ j))) atTop (𝓝 a)) :
    Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  apply tendsto_of_subseq_tendsto
  intro r ht
  have he : ∀ᶠ j in atTop, 0 < r j := ht.eventually self_mem_nhdsWithin
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hp : ∀ j : ℕ, 0 < r (j + N) := fun j => hN _ (Nat.le_add_left N j)
  have ht' : Tendsto (fun j : ℕ => r (j + N)) atTop (𝓝 0) :=
    (ht.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N)
  obtain ⟨σ, hσ⟩ := hg (fun j => r (j + N)) hp ht'
  exact ⟨fun j => σ j + N, hσ⟩

/-- Density rules out empty, full, or translated-halfspace limits once the limiting
constant-polar identity has been established. -/
theorem blowup_limit_eq_halfspace_of_constant_polar (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {F : Set AmbientSpace} (hF : NullMeasurableSet F volume)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0))
    {μ : Measure AmbientSpace}
    (hpolar : HasConstantIndicatorPolar F μ (reducedNormal E hE hmE x)) :
    F =ᵐ[volume] {y : AmbientSpace | inner ℝ (reducedNormal E hE hmE x) y < 0} :=
  halfspace_rigidity_of_constant_indicator_polar hF (norm_reducedNormal E hE hmE hx)
    hpolar (blowup_limit_volume_sides_pos E hE hmE hx hr ht hF hlim)

/-- Every locally L¹ convergent sequence of blow-ups at a reduced point has the
prescribed halfspace as its limit, up to a Lebesgue-null set. -/
theorem blowup_limit_eq_halfspace (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {F : Set AmbientSpace} (hF : NullMeasurableSet F volume)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ y in K,
        |(blowupSet E x (r j)).indicator (fun _ => (1 : ℝ)) y -
          F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0)) :
    F =ᵐ[volume] {y : AmbientSpace | inner ℝ (reducedNormal E hE hmE x) y < 0} := by
  obtain ⟨μ, τ, hτ, hμ, hμfin, hpolar, htest⟩ :=
    exists_blowup_constant_polar_limit E hE hmE hx hr ht hF hlim
  exact blowup_limit_eq_halfspace_of_constant_polar E hE hmE hx hr ht hF hlim hpolar

/-- The actual rescaled indicators converge locally in L¹ to the halfspace with
outward reduced normal, along the full positive-radius filter at every reduced point. -/
theorem halfspace_blowup (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    (K : Set AmbientSpace) (hK : IsCompact K) :
    Tendsto (fun r : ℝ => ∫ y in K,
      |(blowupSet E x r).indicator (fun _ => (1 : ℝ)) y -
        {z : AmbientSpace | inner ℝ (reducedNormal E hE hmE x) z < 0}.indicator
          (fun _ => (1 : ℝ)) y|) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_nhdsGT_of_positive_sequences_subseq
  intro r hr ht
  obtain ⟨F, hF, hFper, σ, hσ, hlim⟩ := exists_blowup_subsequence E hE hmE hx hr ht
  have heq := blowup_limit_eq_halfspace E hE hmE hx (fun j => hr (σ j))
    (ht.comp hσ.tendsto_atTop) hF.nullMeasurableSet hlim
  refine ⟨σ, (hlim K hK).congr' (Eventually.of_forall fun j => ?_)⟩
  apply setIntegral_congr_ae hK.measurableSet
  filter_upwards [indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) heq] with y hy
  intro _
  rw [hy]

/-- Every positive sequence of radii has a subsequence whose rescaled perimeter
measures converge on compact tests to a regular measure with the halfspace polar. -/
theorem exists_halfspace_blowup_measure_limit (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) :
    ∃ (μ : Measure AmbientSpace) (τ : ℕ → ℕ), StrictMono τ ∧ μ.Regular ∧
      IsFiniteMeasureOnCompacts μ ∧
      HasConstantIndicatorPolar
        {y : AmbientSpace | inner ℝ (reducedNormal E hE hmE x) y < 0}
        μ (reducedNormal E hE hmE x) ∧
      ∀ φ : CompactlySupportedContinuousMap AmbientSpace ℝ,
        Tendsto (fun j => ∫ y, φ y ∂blowupPolarMeasure
          (canonicalPerimeterMeasure E hE hmE) x (r (τ j))) atTop (𝓝 (∫ y, φ y ∂μ)) := by
  have ht' : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r ht (Eventually.of_forall hr)
  apply exists_blowup_constant_polar_limit E hE hmE hx hr ht
    (isOpen_lt (by fun_prop) continuous_const).measurableSet.nullMeasurableSet
  exact fun K hK => (halfspace_blowup E hE hmE hx K hK).comp ht'

end LiquidDrop
