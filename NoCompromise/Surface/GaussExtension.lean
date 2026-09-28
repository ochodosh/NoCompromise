import NoCompromise.Topology.Tubular
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# A smooth Lipschitz extension of the Gauss map

A cutoff of the normal field composed with the tubular projection gives a
compactly supported smooth extension. Agreement on the surface identifies
its differential on tangent vectors.
-/

noncomputable section
open Set Filter Function
open scoped Topology

namespace LiquidDrop

/-- The Gauss map of a compact smooth embedded surface has a smooth Lipschitz
ambient extension with the same tangential differential. -/
theorem exists_gaussMap_extension {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∃ N : E₃ → E₃, ContDiff ℝ (⊤ : ℕ∞) N ∧ (∃ K, LipschitzWith K N) ∧
      (∀ p ∈ S, N p = n p) ∧
      ∀ p ∈ S, ∀ X ∈ tangentPlane S p, fderiv ℝ N p X = fderiv ℝ n p X := by
  obtain ⟨ε, hε, _, hT, hST, proj, dist, hproj, _, hinv⟩ :=
    tubular_neighbourhood hS hc hn
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  have hprojS : ∀ p ∈ S, proj p = p := by
    intro p hp
    simpa using (hinv p hp 0 ⟨neg_neg_of_pos hε, hε⟩).1
  let O := normalTube S n ε ∩ proj ⁻¹' U
  have hO : IsOpen O := hproj.continuousOn.isOpen_inter_preimage hT hU
  have hSO : S ⊆ O := by
    intro p hp
    exact ⟨hST hp, by simpa only [mem_preimage, hprojS p hp] using hSU hp⟩
  obtain ⟨χ, hχ, hcχ, hsχ, hχone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hc hO hSO
  let N : E₃ → E₃ := fun x => χ x • n (proj x)
  have hN : ContDiff ℝ (⊤ : ℕ∞) N := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hxO := hsχ hx
      exact hχ.contDiffAt.smul
        ((hnU.contDiffAt (hU.mem_nhds hxO.2)).comp x
          (hproj.contDiffAt (hT.mem_nhds hxO.1)))
    · apply (contDiffAt_const (c := (0 : E₃))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [N, hy]
  have hcN : HasCompactSupport N := hcχ.smul_right
  have hNS : ∀ p ∈ S, N p = n p := by
    intro p hp
    have hone : χ p = 1 :=
      (hχone.filter_mono (nhds_le_nhdsSet hp)).self_of_nhds
    simp [N, hone, hprojS p hp]
  refine ⟨N, hN, ContDiff.lipschitzWith_of_hasCompactSupport hcN hN (by simp), hNS, ?_⟩
  intro p hp X hX
  apply fderiv_eq_on_tangentPlane
    (hN.differentiable (by simp) p) ((hn.contDiffAt hp).differentiableAt (by simp)) _ hX
  exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin hNS

end LiquidDrop
