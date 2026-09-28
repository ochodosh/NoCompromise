import NoCompromise.Surface.MorseDischarged

/-!
# A Morse chart at a saddle, in ambient terms (`lem:local-sectors` (iii))

At an index-one critical point `p` of `h` on an embedded surface: one Morse chart `E` on a disk
`morseDisk ρ` whose domain is the trace of an ambient open set `V`, with the sub/superlevel and
level points of `S ∩ V` read off in chart coordinates. Used in `lem:merge-disjoint`.
-/

noncomputable section

open Set

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- `lem:local-sectors` (iii) in ambient form: a Morse chart `E` at a saddle `p`, a radius `ρ`
and an open `V ∋ p` whose trace on `S` is the chart preimage of `morseDisk ρ`, with
`h = h p + (E x)₀² - (E x)₁²` there. -/
theorem exists_saddle_chart {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hcrit : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) (hk : surfaceIndex S n h p = 1) :
    ∃ (E : OpenPartialHomeomorph S E2) (ρ : ℝ) (V : Set E₃), 0 < ρ ∧ morseDisk ρ ⊆ E.target ∧
      IsOpen V ∧ p ∈ V ∧ (⟨p, hcrit.1⟩ : S) ∈ E.source ∧ E ⟨p, hcrit.1⟩ = 0 ∧
      (∀ x : S, (x : E₃) ∈ V ↔ x ∈ E.source ∧ E x ∈ morseDisk ρ) ∧
      ∀ x : S, x ∈ E.source → h x = h p + ((E x) 0 ^ 2 - (E x) 1 ^ 2) := by
  obtain ⟨E, U, -, -, hsrc, hps, hE0, hmodel⟩ := surface_morse_chart hS hn hh hcrit hnd
  have h0t : (0 : E2) ∈ E.target := hE0 ▸ E.map_source hps
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp E.open_target 0 h0t
  have hO : IsOpen (E.source ∩ E ⁻¹' morseDisk ρ) :=
    E.isOpen_inter_preimage Metric.isOpen_ball
  obtain ⟨V, hV, hVO⟩ := isOpen_induced_iff.mp hO
  have hpO : (⟨p, hcrit.1⟩ : S) ∈ E.source ∩ E ⁻¹' morseDisk ρ := by
    refine ⟨hps, ?_⟩
    change E ⟨p, hcrit.1⟩ ∈ morseDisk ρ
    rw [hE0]
    exact Metric.mem_ball_self hρ
  refine ⟨E, ρ, V, hρ, hball, hV, ?_, hps, hE0, fun x => ?_, fun x hx => ?_⟩
  · have : (⟨p, hcrit.1⟩ : S) ∈ Subtype.val ⁻¹' V := hVO ▸ hpO
    exact this
  · change x ∈ Subtype.val ⁻¹' V ↔ x ∈ E.source ∩ E ⁻¹' morseDisk ρ
    rw [hVO]
  · rw [hmodel x hx, hk]
    simp [morseModel]

section chart

variable {h : E₃ → ℝ} {p : E₃} {E : OpenPartialHomeomorph S E2} {ρ : ℝ} {V : Set E₃}

/-- Points of the chart domain, classified by the sign of the model form. -/
theorem saddle_chart_mem {hp : p ∈ S} (hps : (⟨p, hp⟩ : S) ∈ E.source)
    (hE0 : E ⟨p, hp⟩ = 0)
    (hVE : ∀ x : S, (x : E₃) ∈ V ↔ x ∈ E.source ∧ E x ∈ morseDisk ρ)
    (hmod : ∀ x : S, x ∈ E.source → h x = h p + ((E x) 0 ^ 2 - (E x) 1 ^ 2))
    {y : E₃} (hyS : y ∈ S) (hyV : y ∈ V) :
    (h y < h p → E ⟨y, hyS⟩ ∈ morseSm12 ρ ∪ morseSm34 ρ) ∧
    (h p < h y → E ⟨y, hyS⟩ ∈ morseSp23 ρ ∪ morseSp41 ρ) ∧
    (h y = h p → y ≠ p →
      E ⟨y, hyS⟩ ∈ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ) := by
  obtain ⟨hsrc, hdisk⟩ := (hVE ⟨y, hyS⟩).mp hyV
  have hm := hmod ⟨y, hyS⟩ hsrc
  change h y = h p + _ at hm
  refine ⟨fun hlt => ?_, fun hgt => ?_, fun heq hne => ?_⟩
  · rw [← morse_saddle_negative_set]
    exact ⟨hdisk, by linarith⟩
  · rw [← morse_saddle_positive_set]
    exact ⟨hdisk, by linarith⟩
  · have hmem : E ⟨y, hyS⟩ ∈ {x ∈ morseDisk ρ | x 0 ^ 2 - x 1 ^ 2 = 0} := ⟨hdisk, by linarith⟩
    have hρ : 0 < ρ := by
      have := hdisk
      simp only [morseDisk, Metric.mem_ball, dist_zero_right] at this
      exact lt_of_le_of_lt (norm_nonneg _) this
    rw [morse_saddle_zero_set hρ] at hmem
    rcases hmem with ((((h0 | h1) | h2) | h3) | h4)
    · exfalso
      apply hne
      rw [mem_singleton_iff, ← hE0] at h0
      exact congrArg Subtype.val (E.injOn hsrc hps h0)
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr h3)
    · exact Or.inr h4

end chart

end LiquidDrop
