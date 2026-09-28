import NoCompromise.Capacity.FluxIdentity
import NoCompromise.Hull.Defs

/-!
# Translation invariance of the capacitary problem

The blueprint proof of `thm:capacitary-potential` begins by translating so that
`0 ∈ int K`. This file transports the capacitary data along `x ↦ x + a`: the
distributional Laplacian, the capacitary boundary-value problem, the filled hull,
and the capacity itself. Sets are pulled back as `(fun x => x + a) ⁻¹' S`.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped ENNReal NNReal Gradient
namespace LiquidDrop

section General

variable {n : ℕ}

/-- The coordinate derivative of a translate is the translate of the coordinate derivative. -/
lemma poissonCoordinateDerivative_comp_add_right (i : Fin n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    poissonCoordinateDerivative i (fun x => g (x + a)) =
      fun x => poissonCoordinateDerivative i g (x + a) := by
  funext x
  simp only [poissonCoordinateDerivative, fderiv_comp_add_right]

/-- The classical Laplacian commutes with translation. -/
lemma laplacianN_comp_add_right (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    laplacianN (fun y => g (y + a)) x = laplacianN g (x + a) := by
  simp only [laplacianN, poissonCoordinateDerivative_comp_add_right]

lemma measurePreserving_add_right_euclidean (a : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun x => x + a) (volume : Measure (EuclideanSpace ℝ (Fin n))) volume :=
  measurePreserving_add_right volume a

lemma measurableEmbedding_add_right_euclidean (a : EuclideanSpace ℝ (Fin n)) :
    MeasurableEmbedding (fun x : EuclideanSpace ℝ (Fin n) => x + a) :=
  (MeasurableEquiv.addRight a).measurableEmbedding

/-- Set integrals over a pulled-back set: `∫_{U - a} g(x + a) dx = ∫_U g`. -/
lemma setIntegral_preimage_add_right (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x in (fun x => x + a) ⁻¹' U, g (x + a) = ∫ y in U, g y :=
  (measurePreserving_add_right_euclidean a).setIntegral_preimage_emb
    (measurableEmbedding_add_right_euclidean a) g U

/-- Local integrability on a set transports to the translated function on the pulled-back set. -/
lemma locallyIntegrableOn_comp_add_right {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (h : LocallyIntegrableOn g U)
    (a : EuclideanSpace ℝ (Fin n)) :
    LocallyIntegrableOn (fun x => g (x + a)) ((fun x => x + a) ⁻¹' U) := by
  intro x hx
  obtain ⟨t, ht, hint⟩ := h (x + a) hx
  refine ⟨(fun x => x + a) ⁻¹' t, ?_, ?_⟩
  · have hT : Tendsto (fun x => x + a) (𝓝[(fun x => x + a) ⁻¹' U] x) (𝓝[U] (x + a)) :=
      ((continuous_add_const a).continuousWithinAt).tendsto_nhdsWithin (mapsTo_preimage _ _)
    exact hT ht
  · exact ((measurePreserving_add_right_euclidean a).integrableOn_comp_preimage
      (measurableEmbedding_add_right_euclidean a)).2 hint

/-- Translating a distributional Poisson equation `Δu = f` on `U` along `x ↦ x + a`. -/
theorem HasDistributionalLaplacianOn.comp_add_right
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasDistributionalLaplacianOn u f U) (a : EuclideanSpace ℝ (Fin n)) :
    HasDistributionalLaplacianOn (fun x => u (x + a)) (fun x => f (x + a))
      ((fun x => x + a) ⁻¹' U) where
  locallyIntegrable_function := locallyIntegrableOn_comp_add_right h.locallyIntegrable_function a
  locallyIntegrable_source := locallyIntegrableOn_comp_add_right h.locallyIntegrable_source a
  test_eq := by
    intro φ hφ hcpt hsupp
    set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => φ (y + -a) with hψdef
    have hφψ : φ = fun x => ψ (x + a) := by
      funext x; simp [hψdef]
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.add contDiff_const)
    have hψcpt : HasCompactSupport ψ := hcpt.comp_homeomorph (Homeomorph.addRight (-a))
    have hψsupp : tsupport ψ ⊆ U := by
      intro y hy
      have hy' : y + -a ∈ tsupport φ :=
        tsupport_comp_subset_preimage φ (continuous_add_const (-a)) hy
      simpa using hsupp hy'
    have key := h.test_eq ψ hψ hψcpt hψsupp
    rw [hφψ]
    simp only [laplacianN_comp_add_right]
    rw [setIntegral_preimage_add_right (fun y => u y * laplacianN ψ y) U a,
      setIntegral_preimage_add_right (fun y => f y * ψ y) U a]
    exact key

/-- The distributional Poisson equation is invariant under translation. -/
theorem hasDistributionalLaplacianOn_comp_add_right_iff
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (a : EuclideanSpace ℝ (Fin n)) :
    HasDistributionalLaplacianOn (fun x => u (x + a)) (fun x => f (x + a))
        ((fun x => x + a) ⁻¹' U) ↔
      HasDistributionalLaplacianOn u f U := by
  refine ⟨fun h => ?_, fun h => h.comp_add_right a⟩
  have h' := h.comp_add_right (-a)
  simpa [Set.preimage_preimage] using h'

/-- The gradient of a translate is the translate of the gradient (unconditionally). -/
lemma gradient_comp_add_right (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => g (y + a)) x = gradient g (x + a) := by
  simp only [gradient, fderiv_comp_add_right]

end General

/-! ### Topological and metric transports in `AmbientSpace` -/

lemma interior_preimage_add_right (S : Set AmbientSpace) (a : AmbientSpace) :
    interior ((fun x => x + a) ⁻¹' S) = (fun x => x + a) ⁻¹' interior S :=
  ((Homeomorph.addRight a).preimage_interior S).symm

lemma closure_preimage_add_right (S : Set AmbientSpace) (a : AmbientSpace) :
    closure ((fun x => x + a) ⁻¹' S) = (fun x => x + a) ⁻¹' closure S :=
  ((Homeomorph.addRight a).preimage_closure S).symm

lemma frontier_preimage_add_right (S : Set AmbientSpace) (a : AmbientSpace) :
    frontier ((fun x => x + a) ⁻¹' S) = (fun x => x + a) ⁻¹' frontier S :=
  ((Homeomorph.addRight a).preimage_frontier S).symm

lemma isBounded_preimage_add_right_iff (S : Set AmbientSpace) (a : AmbientSpace) :
    Bornology.IsBounded ((fun x => x + a) ⁻¹' S) ↔ Bornology.IsBounded S := by
  simp only [Metric.isBounded_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx y hy => ?_⟩
    have h := hC (x := x + -a) (by simpa using hx) (y := y + -a) (by simpa using hy)
    simpa using h
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx y hy => ?_⟩
    have h := hC hx hy
    simpa using h

lemma connectedComponentIn_preimage_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (F : Set Y) (x : X) :
    connectedComponentIn (h ⁻¹' F) x = h ⁻¹' connectedComponentIn F (h x) := by
  by_cases hx : x ∈ h ⁻¹' F
  · have himg := h.image_connectedComponentIn hx
    rw [h.image_preimage] at himg
    rw [← himg, h.preimage_image]
  · rw [connectedComponentIn_eq_empty hx,
      connectedComponentIn_eq_empty (show h x ∉ F from hx), preimage_empty]

lemma connectedComponentIn_preimage_add_right (F : Set AmbientSpace) (a x : AmbientSpace) :
    connectedComponentIn ((fun x => x + a) ⁻¹' F) x =
      (fun x => x + a) ⁻¹' connectedComponentIn F (x + a) :=
  connectedComponentIn_preimage_homeomorph (Homeomorph.addRight a) F x

/-- The unbounded exterior of the hull commutes with translation. -/
theorem hullExterior_preimage_add (Ω : Set AmbientSpace) (a : AmbientSpace) :
    hullExterior ((fun x => x + a) ⁻¹' Ω) = (fun x => x + a) ⁻¹' hullExterior Ω := by
  ext x
  simp only [hullExterior, mem_ofPred_eq, mem_preimage]
  rw [closure_preimage_add_right, ← preimage_compl, connectedComponentIn_preimage_add_right,
    isBounded_preimage_add_right_iff]

/-- Blueprint `def:hull`: the filled hull commutes with translation. -/
theorem filledHull_preimage_add (Ω : Set AmbientSpace) (a : AmbientSpace) :
    filledHull ((fun x => x + a) ⁻¹' Ω) = (fun x => x + a) ⁻¹' filledHull Ω := by
  simp only [filledHull, hullExterior_preimage_add, preimage_compl]

/-! ### The capacitary problem and the capacity -/

/-- The capacitary boundary-value problem is invariant under translation. -/
theorem capacitary_problem_comp_add_right_iff {K : Set AmbientSpace} (a : AmbientSpace)
    {u : AmbientSpace → ℝ} :
    (Continuous (fun x => u (x + a)) ∧
      HasDistributionalLaplacianOn (fun x => u (x + a)) (fun _ => 0)
        ((fun x => x + a) ⁻¹' K)ᶜ ∧
      (∀ x ∈ (fun x => x + a) ⁻¹' K, u (x + a) = 1) ∧
      Tendsto (fun x => u (x + a)) (cocompact AmbientSpace) (𝓝 0)) ↔
    (Continuous u ∧ HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ ∧ (∀ x ∈ K, u x = 1) ∧
      Tendsto u (cocompact AmbientSpace) (𝓝 0)) := by
  have hc : Continuous (fun x => u (x + a)) ↔ Continuous u :=
    (Homeomorph.addRight a).comp_continuous_iff'
  have hL : HasDistributionalLaplacianOn (fun x => u (x + a)) (fun _ => 0)
      ((fun x => x + a) ⁻¹' K)ᶜ ↔ HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ := by
    rw [← preimage_compl]
    exact hasDistributionalLaplacianOn_comp_add_right_iff (f := fun _ => 0) a
  have hb : (∀ x ∈ (fun x => x + a) ⁻¹' K, u (x + a) = 1) ↔ ∀ x ∈ K, u x = 1 := by
    constructor
    · intro h y hy
      have := h (y + -a) (by simpa using hy)
      simpa using this
    · intro h x hx
      exact h _ hx
  have ht : Tendsto (fun x => u (x + a)) (cocompact AmbientSpace) (𝓝 0) ↔
      Tendsto u (cocompact AmbientSpace) (𝓝 0) := by
    have hmap := tendsto_map'_iff (f := u) (g := ⇑(Homeomorph.addRight a))
      (x := cocompact AmbientSpace) (y := 𝓝 (0 : ℝ))
    rw [(Homeomorph.addRight a).map_cocompact] at hmap
    exact hmap.symm
  rw [hc, hL, hb, ht]

/-- Blueprint `def:capacity`: the capacity is invariant under translation. -/
theorem capacityOf_comp_add_right (K : Set AmbientSpace) (u : AmbientSpace → ℝ)
    (a : AmbientSpace) :
    capacityOf ((fun x => x + a) ⁻¹' K) (fun x => u (x + a)) = capacityOf K u := by
  unfold capacityOf
  rw [← preimage_compl]
  simp only [gradient_comp_add_right]
  rw [setIntegral_preimage_add_right (fun y => ‖gradient u y‖ ^ 2) Kᶜ a]

/-- A `C²` extension transports along the translation. -/
lemma contDiff_comp_add_right {k : WithTop ℕ∞} {g : AmbientSpace → ℝ}
    (hg : ContDiff ℝ k g) (a : AmbientSpace) : ContDiff ℝ k (fun x => g (x + a)) :=
  hg.comp (contDiff_id.add contDiff_const)

/-- The boundary-regularity witness `EqOn u g (closure Kᶜ)` transports along the translation. -/
lemma eqOn_closure_compl_comp_add_right {K : Set AmbientSpace} {u g : AmbientSpace → ℝ}
    (h : EqOn u g (closure Kᶜ)) (a : AmbientSpace) :
    EqOn (fun x => u (x + a)) (fun x => g (x + a)) (closure ((fun x => x + a) ⁻¹' K)ᶜ) := by
  rw [← preimage_compl, closure_preimage_add_right]
  exact fun x hx => h hx

/-! ### `C¹` boundary charts under translation -/

/-- A `C¹` boundary chart moved along `x ↦ x - a`, so that it serves the pulled-back set. -/
def C1BoundaryChart.translate (c : C1BoundaryChart) (a : AmbientSpace) : C1BoundaryChart where
  height := c.height
  height_contDiff := c.height_contDiff
  placement := c.placement.trans (AffineIsometryEquiv.constVAdd ℝ AmbientSpace (-a))
  region := (fun x => x + a) ⁻¹' c.region
  isOpen_region := c.isOpen_region.preimage (continuous_add_const a)
  bounded_region := (isBounded_preimage_add_right_iff _ a).2 c.bounded_region

lemma C1BoundaryChart.translate_placement_symm_apply (c : C1BoundaryChart) (a z : AmbientSpace) :
    (c.translate a).placement.symm z = c.placement.symm (z + a) := by
  change (c.placement.trans (AffineIsometryEquiv.constVAdd ℝ AmbientSpace (-a))).symm z = _
  rw [AffineIsometryEquiv.symm_apply_eq, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.apply_symm_apply, AffineIsometryEquiv.coe_constVAdd]
  change z = -a + (z + a)
  abel

lemma C1BoundaryChart.IsChartFor.translate {c : C1BoundaryChart} {E : Set AmbientSpace}
    (hc : c.IsChartFor E) (a : AmbientSpace) :
    (c.translate a).IsChartFor ((fun x => x + a) ⁻¹' E) := by
  intro z hz
  rw [C1BoundaryChart.translate_placement_symm_apply]
  exact hc (z + a) hz

lemma C1BoundaryChart.translate_outwardNormal (c : C1BoundaryChart) (a z : AmbientSpace) :
    (c.translate a).outwardNormal z = c.outwardNormal (z + a) := by
  simp only [C1BoundaryChart.outwardNormal, C1BoundaryChart.translate_placement_symm_apply]
  rfl

/-- A `C¹` boundary transports along translation. -/
theorem HasC1Boundary.preimage_add_right {D : Set AmbientSpace} (h : HasC1Boundary D)
    (a : AmbientSpace) : HasC1Boundary ((fun x => x + a) ⁻¹' D) := by
  intro x hx
  rw [frontier_preimage_add_right] at hx
  obtain ⟨c, hc, hxc⟩ := h (x + a) hx
  exact ⟨c.translate a, hc.translate a, hxc⟩

/-- The outward normal of the translated domain is the translated outward normal. -/
theorem HasC1Boundary.outwardNormal_preimage_add_right {D : Set AmbientSpace}
    (h : HasC1Boundary D) (a : AmbientSpace) (h' : HasC1Boundary ((fun x => x + a) ⁻¹' D))
    (z : AmbientSpace) : h'.outwardNormal z = h.outwardNormal (z + a) := by
  by_cases hz : z ∈ frontier ((fun x => x + a) ⁻¹' D)
  · have hz' : z + a ∈ frontier D := by
      rw [frontier_preimage_add_right] at hz
      exact hz
    obtain ⟨c, hc, hzc⟩ := h (z + a) hz'
    rw [h.outwardNormal_eq_chart hc hz' hzc,
      h'.outwardNormal_eq_chart (hc.translate a) hz hzc, c.translate_outwardNormal]
  · have hz' : z + a ∉ frontier D := by
      rw [frontier_preimage_add_right] at hz
      exact hz
    rw [h'.outwardNormal_eq_zero hz, h.outwardNormal_eq_zero hz']

end LiquidDrop
