module

public import NoCompromise.Surface.MorseSurfaceChart

@[expose] public section

/-!
# Local ingredients of `lem:sublevel-closure`

At an index-zero critical point `p` of a smooth function `h` on an embedded surface, `p` is an
isolated point of the closed sublevel `S ∩ {h ≤ h p}` (the case `λ = 0` of the proof of
`lem:sublevel-closure`, from `lem:local-sectors` (i)); at an index-two critical point a punctured
neighbourhood is a connected subset of `{h < h p}` (the case `λ = 2`, from (ii)).
-/

noncomputable section

open Set

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- `lem:sublevel-closure`, case `λ = 0` (local ingredient): an index-zero critical point `p` is
an isolated point of `S ∩ {h ≤ h p}`.
PARTIAL: the planar Morse lemma is the named hypothesis `h_morse_coords`. -/
theorem exists_isolated_sublevel_of_index_zero {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p))
    (h_morse_coords : MorseCoordsStatement) (hk : surfaceIndex S n h p = 0) :
    ∃ U : Set E₃, IsOpen U ∧ p ∈ U ∧ U ∩ (S ∩ {x | h x ≤ h p}) = {p} := by
  obtain ⟨E, -, ρ, -, -, hρ, -, hps, hE0, h0, -, -⟩ :=
    exists_surface_local_sectors hS hn hh hcrit hnd h_morse_coords
  obtain ⟨hlt, heq, -⟩ := h0 hk
  have hO : IsOpen (E.source ∩ E ⁻¹' morseDisk ρ) :=
    E.isOpen_inter_preimage Metric.isOpen_ball
  obtain ⟨V, hV, hVO⟩ := isOpen_induced_iff.mp hO
  have hpO : (⟨p, hcrit.1⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
    refine ⟨hps, ?_⟩
    change E ⟨p, hcrit.1⟩ ∈ morseDisk ρ
    rw [hE0]
    exact Metric.mem_ball_self hρ
  have hpV : p ∈ V := by
    have : (⟨p, hcrit.1⟩ : S) ∈ Subtype.val ⁻¹' V := hVO ▸ hpO
    exact this
  refine ⟨V, hV, hpV, ?_⟩
  ext x
  constructor
  · rintro ⟨hxV, hxS, hxle⟩
    have hxO : (⟨x, hxS⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
      rw [← hVO]; exact hxV
    rcases lt_or_eq_of_le (show h x ≤ h p from hxle) with hl | he
    · have : (⟨x, hxS⟩ : S) ∈ {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x < h p} := ⟨hxO, hl⟩
      rw [hlt] at this
      exact this.elim
    · have : (⟨x, hxS⟩ : S) ∈ {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x = h p} := ⟨hxO, he⟩
      rw [heq] at this
      exact congrArg Subtype.val (mem_singleton_iff.mp this)
  · rintro rfl
    exact ⟨hpV, hcrit.1, show h x ≤ h x from le_rfl⟩

/-- `lem:sublevel-closure`, case `λ = 2` (local ingredient): near an index-two critical point `p`
the surface lies in `{h ≤ h p}`, and the punctured neighbourhood is a connected subset of
`{h < h p}`.
PARTIAL: the planar Morse lemma is the named hypothesis `h_morse_coords`. -/
theorem exists_punctured_sublevel_of_index_two {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p))
    (h_morse_coords : MorseCoordsStatement) (hk : surfaceIndex S n h p = 2) :
    ∃ U : Set E₃, IsOpen U ∧ p ∈ U ∧ U ∩ S ⊆ {x | h x ≤ h p} ∧
      (U ∩ S) \ {p} ⊆ {x | h x < h p} ∧ IsConnected ((U ∩ S) \ {p}) := by
  obtain ⟨E, -, ρ, -, -, hρ, hD, hps, hE0, -, h2, -⟩ :=
    exists_surface_local_sectors hS hn hh hcrit hnd h_morse_coords
  obtain ⟨hlt, heq, hgt⟩ := h2 hk
  have hO : IsOpen (E.source ∩ E ⁻¹' morseDisk ρ) :=
    E.isOpen_inter_preimage Metric.isOpen_ball
  obtain ⟨V, hV, hVO⟩ := isOpen_induced_iff.mp hO
  have hpO : (⟨p, hcrit.1⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
    refine ⟨hps, ?_⟩
    change E ⟨p, hcrit.1⟩ ∈ morseDisk ρ
    rw [hE0]
    exact Metric.mem_ball_self hρ
  have hpV : p ∈ V := by
    have : (⟨p, hcrit.1⟩ : S) ∈ Subtype.val ⁻¹' V := hVO ▸ hpO
    exact this
  have hmemO : ∀ x (hxS : x ∈ S), x ∈ V → (⟨x, hxS⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
    intro x hxS hxV
    rw [← hVO]; exact hxV
  have hle : V ∩ S ⊆ {x | h x ≤ h p} := by
    rintro x ⟨hxV, hxS⟩
    by_contra hc
    have : (⟨x, hxS⟩ : S) ∈ {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h p < h x} :=
      ⟨hmemO x hxS hxV, lt_of_not_ge hc⟩
    rw [hgt] at this
    exact this
  have hset : (V ∩ S) \ {p} =
      Subtype.val '' {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x < h p} := by
    ext x
    constructor
    · rintro ⟨⟨hxV, hxS⟩, hxp⟩
      refine ⟨⟨x, hxS⟩, ⟨hmemO x hxS hxV, ?_⟩, rfl⟩
      rcases lt_or_eq_of_le (show h x ≤ h p from hle ⟨hxV, hxS⟩) with hl | he
      · exact hl
      · have : (⟨x, hxS⟩ : S) ∈ {x ∈ E.source ∩ E ⁻¹' morseDisk ρ | h x = h p} :=
          ⟨hmemO x hxS hxV, he⟩
        rw [heq] at this
        exact (hxp (congrArg Subtype.val (mem_singleton_iff.mp this))).elim
    · rintro ⟨y, ⟨hyO, hyl⟩, rfl⟩
      have hyV : (y : E₃) ∈ V := by
        have : y ∈ Subtype.val ⁻¹' V := hVO.symm ▸ hyO
        exact this
      refine ⟨⟨hyV, y.2⟩, ?_⟩
      intro hyp
      rw [mem_singleton_iff] at hyp
      change h y < h p at hyl
      rw [hyp] at hyl
      exact lt_irrefl _ hyl
  refine ⟨V, hV, hpV, hle, ?_, ?_⟩
  · rw [hset]
    rintro _ ⟨y, ⟨-, hyl⟩, rfl⟩
    exact hyl
  · rw [hset, hlt]
    exact (morse_model_connected_transport E hD sdiff_subset
      (morse_punctured_disk_connected hρ)).image _ continuous_subtype_val.continuousOn

end LiquidDrop
