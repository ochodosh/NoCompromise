module

public import NoCompromise.Surface.MorseDischarged

@[expose] public section

/-!
# The saddle case of `lem:sublevel-closure`: local lower trace

Near an index-one critical point `p` the lower trace `S ∩ U ∩ {h < h p}` is the union of the two
connected lower sectors `S⁻₁₂`, `S⁻₃₄` (chart images), both adjoining `p`, and every level point of
`S ∩ U` adjoins one of them (`lem:local-sectors` (iii) with the flanking relations).
-/

noncomputable section

open Set

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- `lem:sublevel-closure`, case `λ = 1` (local ingredient): near an index-one critical point `p`
the lower trace is the union of two connected sets `T₁`, `T₂` (the lower sectors `S⁻₁₂`, `S⁻₃₄`)
whose closures contain `p`, and every level-`h p` point of `S ∩ U` lies in the closure of one of
them. -/
theorem exists_saddle_sublevel_nhds {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) (hk : surfaceIndex S n h p = 1) :
    ∃ U : Set E₃, IsOpen U ∧ p ∈ U ∧ ∃ T₁ T₂ : Set E₃,
      S ∩ U ∩ {x | h x < h p} = T₁ ∪ T₂ ∧ IsConnected T₁ ∧ IsConnected T₂ ∧
      p ∈ closure T₁ ∧ p ∈ closure T₂ ∧
      ∀ q ∈ S ∩ U, h q = h p → q ∈ closure T₁ ∪ closure T₂ := by
  obtain ⟨E, -, ρ, -, -, hρ, hD, hps, hE0, -, -, h1⟩ :=
    surface_local_sectors hS hn hh hcrit hnd
  obtain ⟨hlt, heq, -⟩ := h1 hk
  have hO : IsOpen (E.source ∩ E ⁻¹' morseDisk ρ) :=
    E.isOpen_inter_preimage Metric.isOpen_ball
  obtain ⟨V, hV, hVO⟩ := isOpen_induced_iff.mp hO
  have hmemO : ∀ x (hxS : x ∈ S), x ∈ V → (⟨x, hxS⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
    intro x hxS hxV
    rw [← hVO]; exact hxV
  have hpO : (⟨p, hcrit.1⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
    refine ⟨hps, ?_⟩
    change E ⟨p, hcrit.1⟩ ∈ morseDisk ρ
    rw [hE0]
    exact Metric.mem_ball_self hρ
  have hpV : p ∈ V := by
    have : (⟨p, hcrit.1⟩ : S) ∈ Subtype.val ⁻¹' V := hVO ▸ hpO
    exact this
  have hsymm0 : E.symm 0 = ⟨p, hcrit.1⟩ := by
    rw [← hE0]; exact E.left_inv hps
  have h0D : (0 : E2) ∈ morseDisk ρ := Metric.mem_ball_self hρ
  have hSm12 : morseSm12 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have hSm34 : morseSm34 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have hconn := morse_rays_sectors_connected hρ
  have hz := morse_sectors_zero_mem_closure hρ
  have hfl := morse_rays_flanking hρ
  -- closure transport into the ambient space
  have hcl : ∀ {T : Set E2}, T ⊆ morseDisk ρ → ∀ {y : E2}, y ∈ morseDisk ρ → y ∈ closure T →
      ((E.symm y : S) : E₃) ∈ closure (Subtype.val '' (E.symm '' T)) := by
    intro T hT y hy hyT
    exact image_closure_subset_closure_image continuous_subtype_val
      ⟨E.symm y, (morse_model_closure_transport E hD hT hy).mpr hyT, rfl⟩
  refine ⟨V, hV, hpV, Subtype.val '' (E.symm '' morseSm12 ρ),
    Subtype.val '' (E.symm '' morseSm34 ρ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨⟨hxS, hxV⟩, hxl⟩
      have : (⟨x, hxS⟩ : S) ∈ {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x < h p} :=
        ⟨hmemO x hxS hxV, hxl⟩
      rw [hlt, image_union] at this
      rcases this with hx | hx
      · exact Or.inl ⟨_, hx, rfl⟩
      · exact Or.inr ⟨_, hx, rfl⟩
    · have hsub : ∀ y : S, y ∈ E.symm '' (morseSm12 ρ ∪ morseSm34 ρ) →
          (y : E₃) ∈ S ∩ V ∩ {x | h x < h p} := by
        intro y hy
        rw [← hlt] at hy
        obtain ⟨hyO, hyl⟩ := hy
        have hyV : y ∈ Subtype.val ⁻¹' V := hVO.symm ▸ hyO
        exact ⟨⟨y.2, hyV⟩, hyl⟩
      rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact hsub y (image_mono subset_union_left hy)
      · exact hsub y (image_mono subset_union_right hy)
  · exact (morse_model_connected_transport E hD hSm12 hconn.2.2.2.2.1).image _
      continuous_subtype_val.continuousOn
  · exact (morse_model_connected_transport E hD hSm34 hconn.2.2.2.2.2.2.1).image _
      continuous_subtype_val.continuousOn
  · have := hcl hSm12 h0D hz.1
    rwa [hsymm0] at this
  · have := hcl hSm34 h0D hz.2.2.1
    rwa [hsymm0] at this
  · rintro q ⟨hqS, hqV⟩ hqc
    have hq : (⟨q, hqS⟩ : S) ∈ {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x = h p} :=
      ⟨hmemO q hqS hqV, hqc⟩
    rw [heq] at hq
    obtain ⟨y, hy, hyq⟩ := hq
    have hq' : q = ((E.symm y : S) : E₃) := by rw [hyq]
    rw [hq']
    rcases hy with ((((hy0 | hy1) | hy2) | hy3) | hy4)
    · rw [mem_singleton_iff] at hy0
      subst hy0
      exact Or.inl (hcl hSm12 h0D hz.1)
    · exact Or.inl (hcl hSm12 hy1.1 (hfl.1 hy1).2)
    · exact Or.inl (hcl hSm12 hy2.1 (hfl.2.1 hy2).1)
    · exact Or.inr (hcl hSm34 hy3.1 (hfl.2.2.1 hy3).2)
    · exact Or.inr (hcl hSm34 hy4.1 (hfl.2.2.2 hy4).1)

end LiquidDrop
