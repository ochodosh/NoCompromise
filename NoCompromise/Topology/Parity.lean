module

public import NoCompromise.Topology.Handshake
public import NoCompromise.Topology.TransversalityMain

@[expose] public section

/-!
# Orientation by parity (partial)

The evenness step of `prop:orientation-parity`(i): a smooth disk transverse to a compact
surface, whose boundary loop is also transverse, meets the surface along its boundary in an
even number of points. This combines `cor:transv-preimage` (disk case, with the
boundary-transversality correction) and `lem:handshake`.
-/

noncomputable section
open Set

namespace LiquidDrop

/-- prop:orientation-parity (i), evenness step: the boundary loop of a transverse disk
with transverse boundary meets the surface an even number of times. -/
theorem even_ncard_boundary_intersections_of_boundary_transverse {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {g : EuclideanSpace ℝ (Fin 2) → E₃} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (htr : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, TransverseAt S g p)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, BoundaryTransverseAt S g p) :
    Even (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S).ncard := by
  obtain ⟨hC, hM, hB⟩ := transverse_preimage_disk_of_boundary_transverse hS hc hg htr hbd
  rw [← hB]
  exact even_ncard_oneManifoldBoundary hC hM

/-- The same count after the relative perturbation of `thm:transversality`: a smooth disk
transverse near its boundary circle and with transverse boundary loop can be perturbed,
fixing a boundary collar, so that its boundary intersections are even in number. -/
theorem even_ncard_boundary_intersections_of_perturbation {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin 2) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsOpen W)
    (hWb : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ W)
    (hfW : ∀ p ∈ W ∩ Metric.closedBall 0 1, TransverseAt S f p)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, BoundaryTransverseAt S f p) :
    Even (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ f ⁻¹' S).ncard := by
  obtain ⟨g, hg, -, ⟨V, -, hVb, hgf⟩, htr, hbdg⟩ :=
    exists_transverse_perturbation_of_boundary_transverse (Or.inr rfl) hS hc hf hW hWb hfW
      hbd one_pos
  have heq : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ f ⁻¹' S =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨hp, hpS⟩
      exact ⟨hp, by rw [mem_preimage, hgf p (hVb hp)]; exact hpS⟩
    · rintro ⟨hp, hpS⟩
      exact ⟨hp, by rw [mem_preimage, ← hgf p (hVb hp)]; exact hpS⟩
  rw [heq]
  exact even_ncard_boundary_intersections_of_boundary_transverse hS hc hg htr hbdg

/-- The path step of `prop:orientation-parity`(i): a smooth path with endpoints off a
compact surface can be perturbed, `C¹`-closely and fixing a neighbourhood of its endpoints,
to a transverse path meeting the surface in finitely many points. -/
theorem exists_transverse_path_perturbation_finite {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin 1) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hend : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, f p ∉ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
        ‖g p - f p‖ < ε ∧ ‖fderiv ℝ g p - fderiv ℝ f p‖ < ε) ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin 1)), IsOpen V ∧
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ⊆ V ∧ ∀ p ∈ V, g p = f p) ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S g p) ∧
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ g ⁻¹' S).Finite := by
  have hW : IsOpen (f ⁻¹' Sᶜ) := hc.isClosed.isOpen_compl.preimage hf.continuous
  obtain ⟨g, hg, hsmall, hV, htr⟩ := exists_transverse_perturbation (Or.inl rfl) hS hc hf hW
    (fun p hp => hend p hp) (fun p hp hfp => absurd hfp hp.1) hε
  exact ⟨g, hg, hsmall, hV, htr, finite_transverse_preimage_path hS hc hg htr⟩

/-- In a regular defining chart, a nonzero composite differential gives transversality. -/
theorem transverseAt_of_comp_ne_zero {S : Set E₃} {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → E₃} {q : EuclideanSpace ℝ (Fin k)}
    {U : Set E₃} {φ : E₃ → ℝ} (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : S ∩ U = {x ∈ U | φ x = 0}) (hreg : ∀ x ∈ S ∩ U, gradient φ x ≠ 0)
    (hqU : f q ∈ U) (hne : (fderiv ℝ φ (f q)).comp (fderiv ℝ f q) ≠ 0) :
    TransverseAt S f q := by
  intro hqS
  have hT : tangentPlane S (f q) = (ℝ ∙ gradient φ (f q))ᗮ :=
    tangentPlane_eq hU hqU (hφ.contDiffAt.of_le (by exact_mod_cast le_top)) hzero hqS
      (hreg _ ⟨hqS, hqU⟩)
  obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ φ (f q) (fderiv ℝ f q u) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (ContinuousLinearMap.ext fun u => hall u)
  apply top_unique
  intro y _
  set a := fderiv ℝ φ (f q) (fderiv ℝ f q u)
  set c := fderiv ℝ φ (f q) y / a
  have hmem : y - c • fderiv ℝ f q u ∈ tangentPlane S (f q) := by
    rw [hT, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left,
      map_sub, map_smul, smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hu).symm
  have hy : y = c • fderiv ℝ f q u + (y - c • fderiv ℝ f q u) := by abel
  rw [hy]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ c ⟨u, rfl⟩) hmem

/-- Transversality of the boundary loop forces transversality of the disk on an open
neighbourhood of the boundary circle. -/
theorem exists_open_transverse_nhds_sphere_of_boundary_transverse {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin 2) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, BoundaryTransverseAt S f p) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 2)), IsOpen W ∧
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ W ∧ ∀ p ∈ W, TransverseAt S f p := by
  let Ch : Set ((Set E₃) × (E₃ → ℝ)) := {D | IsOpen D.1 ∧ ContDiff ℝ (⊤ : ℕ∞) D.2 ∧
    S ∩ D.1 = {x ∈ D.1 | D.2 x = 0} ∧ ∀ x ∈ S ∩ D.1, gradient D.2 x ≠ 0}
  let O : (Set E₃) × (E₃ → ℝ) → Set (EuclideanSpace ℝ (Fin 2)) := fun D =>
    {q | f q ∈ D.1 ∧ (fderiv ℝ D.2 (f q)).comp (fderiv ℝ f q) ≠ 0}
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hO : ∀ D ∈ Ch, IsOpen (O D) := by
    intro D hD
    have hφd : Continuous (fderiv ℝ D.2) := hD.2.1.continuous_fderiv (by simp)
    have hcont : Continuous fun q => (fderiv ℝ D.2 (f q)).comp (fderiv ℝ f q) :=
      (hφd.comp hf.continuous).clm_comp hfd
    exact (hD.1.preimage hf.continuous).inter (isOpen_ne_fun hcont continuous_const)
  refine ⟨f ⁻¹' Sᶜ ∪ ⋃ D ∈ Ch, O D,
    (hc.isClosed.isOpen_compl.preimage hf.continuous).union (isOpen_biUnion hO), ?_, ?_⟩
  · intro p hp
    by_cases hpS : f p ∈ S
    · right
      obtain ⟨U, φ, hU, hpU, hφ, hzero, hreg⟩ := hS (f p) hpS
      refine mem_iUnion₂.mpr ⟨(U, φ), ⟨hU, hφ, hzero, hreg⟩, hpU, ?_⟩
      intro h0
      have hT : tangentPlane S (f p) = (ℝ ∙ gradient φ (f p))ᗮ :=
        tangentPlane_eq hU hpU (hφ.contDiffAt.of_le (by exact_mod_cast le_top)) hzero hpS
          (hreg _ ⟨hpS, hpU⟩)
      have hle : Submodule.map (fderiv ℝ f p : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃)
          (ℝ ∙ p)ᗮ ≤ tangentPlane S (f p) := by
        rintro _ ⟨w, -, rfl⟩
        rw [hT, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
        exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L w) h0
      have htop : tangentPlane S (f p) = ⊤ := by
        simpa only [sup_eq_right.mpr hle] using hbd p hp hpS
      have hdim := hS.finrank_tangentPlane hpS
      rw [htop] at hdim
      norm_num [E₃] at hdim
    · exact Or.inl hpS
  · rintro q (hq | hq)
    · exact fun hqS => absurd hqS hq
    · obtain ⟨D, hD, hqU, hne⟩ := mem_iUnion₂.mp hq
      exact transverseAt_of_comp_ne_zero hD.1 hD.2.1 hD.2.2.1 hD.2.2.2 hqU hne

/-- prop:orientation-parity (i), evenness step, with only the boundary-loop hypothesis:
a smooth disk whose boundary loop is transverse to the surface meets it along the boundary
in an even number of points. -/
theorem even_ncard_boundary_intersections_of_boundary_loop_transverse {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin 2) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, BoundaryTransverseAt S f p) :
    Even (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ f ⁻¹' S).ncard := by
  obtain ⟨W, hW, hWb, hWt⟩ :=
    exists_open_transverse_nhds_sphere_of_boundary_transverse hS hc hf hbd
  exact even_ncard_boundary_intersections_of_perturbation hS hc hf hW hWb
    (fun p hp => hWt p hp.1) hbd

end LiquidDrop
