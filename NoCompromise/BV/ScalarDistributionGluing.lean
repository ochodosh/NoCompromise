import NoCompromise.BV.ScalarDistributionUniqueness
import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing local scalar derivative identities

An open neighborhood identity at every point determines the same derivative
globally. A countable subcover permits the exceptional null sets to be combined;
Radon–Nikodym densities handle different underlying positive measures.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

theorem ae_eq_density_of_locally_coordinate_pairings {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (hτ : LocallyIntegrable τ μ)
    (hlocal : ∀ x, ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧
      ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
        ContDiff ℝ 1 φ → tsupport φ ⊆ U →
          (∫ y, φ y * σ y i ∂μ) = ∫ y, φ y * τ y i ∂μ) : σ =ᵐ[μ] τ := by
  classical
  choose U hU hxU hp using hlocal
  obtain ⟨s, hs, hcover⟩ := isLindelof_univ.elim_countable_subcover U hU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  have heq : σ =ᵐ[μ.restrict (⋃ x ∈ s, U x)] τ :=
    (ae_eq_restrict_biUnion_iff U hs σ τ).mpr (fun x _ =>
      ae_eq_density_on_of_coordinate_pairings (hU x) hσ hτ (hp x))
  have hfull : (⋃ x ∈ s, U x) = univ := univ_subset_iff.mp hcover
  simpa only [hfull, Measure.restrict_univ] using heq

/-- Local supported-test identities determine all Borel-restricted vector
pairings, including noncompact fields and infinite ambient measures. -/
theorem setIntegral_inner_eq_of_locally_coordinate_pairings {n : ℕ}
    {μ ρ : Measure (EuclideanSpace ℝ (Fin n))} [SigmaFinite μ] [SigmaFinite ρ]
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (hτ : LocallyIntegrable τ ρ)
    (hlocal : ∀ x, ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧
      ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
        ContDiff ℝ 1 φ → tsupport φ ⊆ U →
          (∫ y, φ y * σ y i ∂μ) = ∫ y, φ y * τ y i ∂ρ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    (∫ x in A, inner ℝ (X x) (σ x) ∂μ) = ∫ x in A, inner ℝ (X x) (τ x) ∂ρ := by
  let κ := μ + ρ
  have hμκ : μ ≪ κ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hρκ : ρ ≪ κ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  let S := fun x => (μ.rnDeriv κ x).toReal • σ x
  let T := fun x => (ρ.rnDeriv κ x).toReal • τ x
  have hS := locallyIntegrable_rnDeriv_smul hσ hμκ
  have hT := locallyIntegrable_rnDeriv_smul hτ hρκ
  have heq : S =ᵐ[κ] T := ae_eq_density_of_locally_coordinate_pairings hS hT (by
    intro x
    obtain ⟨U, hU, hxU, hp⟩ := hlocal x
    refine ⟨U, hU, hxU, fun i φ hφ hsφ => ?_⟩
    simp only [S, T, PiLp.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (φ _) _]
    rw [integral_toReal_rnDeriv_mul hμκ, integral_toReal_rnDeriv_mul hρκ]
    exact hp i φ hφ hsφ)
  calc
    _ = ∫ x in A, inner ℝ (X x) (S x) ∂κ := by
      simpa only [S, inner_smul_right] using
        (setIntegral_toReal_rnDeriv_mul hμκ hA
          (f := fun x => inner ℝ (X x) (σ x))).symm
    _ = ∫ x in A, inner ℝ (X x) (T x) ∂κ := integral_congr_ae
      ((ae_restrict_of_ae heq).mono fun x hx => congrArg (fun v => inner ℝ (X x) v) hx)
    _ = _ := by
      simpa only [T, inner_smul_right] using
        (setIntegral_toReal_rnDeriv_mul hρκ hA
          (f := fun x => inner ℝ (X x) (τ x)))

/-- In particular, all ambient vector pairings agree. -/
theorem integral_inner_eq_of_locally_coordinate_pairings {n : ℕ}
    {μ ρ : Measure (EuclideanSpace ℝ (Fin n))} [SigmaFinite μ] [SigmaFinite ρ]
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (hτ : LocallyIntegrable τ ρ)
    (hlocal : ∀ x, ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧
      ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
        ContDiff ℝ 1 φ → tsupport φ ⊆ U →
          (∫ y, φ y * σ y i ∂μ) = ∫ y, φ y * τ y i ∂ρ)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    (∫ x, inner ℝ (X x) (σ x) ∂μ) = ∫ x, inner ℝ (X x) (τ x) ∂ρ := by
  simpa only [Measure.restrict_univ] using
    setIntegral_inner_eq_of_locally_coordinate_pairings hσ hτ hlocal MeasurableSet.univ X

end LiquidDrop
