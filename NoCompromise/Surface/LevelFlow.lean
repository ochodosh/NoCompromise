module

public import NoCompromise.Surface.Morse
public import NoCompromise.Surface.TangentFlow

@[expose] public section

/-!
# Integral curves of the rotated gradient `levelTangentField`

Smoothness of `levelTangentField n h = n × ∇_Σ h` near the surface, its zeros (exactly the
critical points), complete integral curves on a compact surface, and uniqueness in the form of
time shifts. Used in `lem:merge-disjoint` (`blueprint/chapters/14-flows.tex`).
-/

noncomputable section

open Set

namespace LiquidDrop

/-- The cross product of two `C^k` fields is `C^k`. -/
theorem ContDiffOn.cross3 {k : ℕ∞} {U : Set E₃} {f g : E₃ → E₃} (hf : ContDiffOn ℝ k f U)
    (hg : ContDiffOn ℝ k g U) : ContDiffOn ℝ k (fun x => cross3 (f x) (g x)) U := by
  have hc : ∀ i : Fin 3, ContDiffOn ℝ k (fun x => f x i) U := fun i =>
    (contDiffOn_piLp 2).mp hf i
  have hd : ∀ i : Fin 3, ContDiffOn ℝ k (fun x => g x i) U := fun i =>
    (contDiffOn_piLp 2).mp hg i
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [cross3, crossProduct] using ((hc 1).mul (hd 2)).sub ((hc 2).mul (hd 1))
  · simpa [cross3, crossProduct] using ((hc 2).mul (hd 0)).sub ((hc 0).mul (hd 2))
  · simpa [cross3, crossProduct] using ((hc 0).mul (hd 1)).sub ((hc 1).mul (hd 0))

/-- `levelTangentField n h` is smooth wherever `n` is smooth. -/
theorem contDiffOn_levelTangentField {n : E₃ → E₃} {U : Set E₃}
    (hnU : ContDiffOn ℝ (⊤ : ℕ∞) n U) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (levelTangentField n h) U := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradient h) := by
    have : gradient h = fun x => (InnerProductSpace.toDual ℝ E₃).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ E₃).symm.toContinuousLinearEquiv.contDiff.comp
      (hh.fderiv_right (m := (⊤ : ℕ∞)) le_rfl)
  have hsg : ContDiffOn ℝ (⊤ : ℕ∞) (surfaceGradient n h) U := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => inner ℝ (n x) (gradient h x)) U :=
      hnU.inner ℝ hgrad.contDiffOn
    exact hgrad.contDiffOn.sub (h1.smul hnU)
  exact ContDiffOn.cross3 hnU hsg

/-- The rotated gradient vanishes exactly at the critical points. -/
theorem levelTangentField_eq_zero_iff {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ} {x : E₃}
    (hx : x ∈ S) : levelTangentField n h x = 0 ↔ IsSurfaceCriticalPoint S h x := by
  rw [isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hx, ← norm_eq_zero,
    norm_levelTangentField hn hx, norm_eq_zero]

/-- Complete integral curves of the rotated gradient on a compact surface. -/
theorem exists_levelTangentField_curve {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {x : E₃} (hx : x ∈ S) :
    ∃ γ : ℝ → E₃, γ 0 = x ∧ ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t := by
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  exact exists_complete_integralCurve_of_tangent hS hc hU hSU
    ((contDiffOn_levelTangentField hnU hh).of_le (by norm_cast))
    (fun p hp => levelTangentField_mem_tangentPlane hS hn hp) hx

/-- Uniqueness of integral curves of the rotated gradient on the surface, as time shifts. -/
theorem levelTangentField_curve_shift {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {γ δ : ℝ → E₃} (hγ : ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t)
    (hδ : ∀ t, δ t ∈ S ∧ HasDerivAt δ (levelTangentField n h (δ t)) t) {t s : ℝ}
    (hts : γ t = δ s) (u : ℝ) : γ (t + u) = δ (s + u) := by
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  have hX : ContDiffOn ℝ 1 (levelTangentField n h) U :=
    (contDiffOn_levelTangentField hnU hh).of_le (by norm_cast)
  have hshift : ∀ {c : ℝ} {η : ℝ → E₃},
      (∀ t, η t ∈ S ∧ HasDerivAt η (levelTangentField n h (η t)) t) →
      ∀ v ∈ (univ : Set ℝ), (fun u => η (c + u)) v ∈ U ∧
        HasDerivAt (fun u => η (c + u)) (levelTangentField n h ((fun u => η (c + u)) v)) v := by
    intro c η hη v _
    refine ⟨hSU (hη (c + v)).1, ?_⟩
    have := (hη (c + v)).2.scomp v ((hasDerivAt_id' v).const_add c)
    simpa [Function.comp_def] using this
  have := integralCurve_unique_of_contDiffOn hU hX ordConnected_univ (mem_univ 0)
    (hshift hγ) (hshift hδ) (by simpa using hts)
  exact this (mem_univ u)

/-- An integral curve of the rotated gradient that starts away from a critical point never
reaches it. -/
theorem levelTangentField_curve_ne {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {γ : ℝ → E₃}
    (hγ : ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) (h0 : γ 0 ≠ p) (t : ℝ) : γ t ≠ p := by
  intro ht
  have hconst : ∀ t, (fun _ : ℝ => p) t ∈ S ∧
      HasDerivAt (fun _ : ℝ => p) (levelTangentField n h ((fun _ : ℝ => p) t)) t := by
    intro t
    refine ⟨hp.1, ?_⟩
    rw [(levelTangentField_eq_zero_iff hS hn hp.1).mpr hp]
    exact hasDerivAt_const t p
  have := levelTangentField_curve_shift hn hh hγ hconst (s := 0) (by simpa using ht) (-t)
  simp at this
  exact h0 this

end LiquidDrop
