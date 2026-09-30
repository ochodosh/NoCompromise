module

public import NoCompromise.Elliptic.SobolevChainClassical
public import NoCompromise.Elliptic.SobolevChainContinuous
public import NoCompromise.Elliptic.SobolevChainDerivatives

@[expose] public section

/-!
# Local classical representatives of weak Sobolev functions

The weak derivative hierarchy is converted to classical regularity on smaller balls.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

/-- Local identification of a continuous weak gradient on an open domain. -/
theorem HasWeakGradientOn.hasFDerivAt_of_continuous_on {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasWeakGradientOn u G U) (hu : Continuous u) (hG : Continuous G)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasFDerivAt u (toDual ℝ _ (G x)) x := by
  obtain ⟨η, hη, hcη, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact
    isCompact_singleton hU (singleton_subset_iff.mpr hx)
  have hnear : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    simpa only [nhdsSet_singleton, Filter.EventuallyEq] using hone
  have hηx : η x = 1 := hnear.self_of_nhds
  have hgη : gradient η x = 0 := by
    unfold gradient
    rw [hnear.fderiv_eq]
    simp
  have hglobal := h.mul_compact_cutoff (hη.of_le (by simp)) hcη hsη
  have hd := hglobal.hasFDerivAt_of_continuous (hη.continuous.mul hu)
      ((hη.continuous.smul hG).add
        (hu.smul (continuous_gradient_of_contDiff (hη.of_le (by simp))))) x
  simp only [hηx, hgη, one_smul, smul_zero, add_zero] at hd
  have heq : (fun y => η y * u y) =ᶠ[𝓝 x] u :=
    hnear.mono fun y hy => by simp [hy]
  exact hd.congr_of_eventuallyEq heq.symm

/-- A classical derivative gains one order from a smooth representative of the weak gradient. -/
theorem HasWeakGradientOn.contDiffOn_succ_of_continuous {n k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasWeakGradientOn u G U) (hu : Continuous u) (hG : ContDiff ℝ k G) :
    ContDiffOn ℝ (k + 1) u U := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
  refine ⟨by simp, fun x => toDual ℝ _ (G x), ?_, ?_⟩
  · exact ((toDual ℝ _).contDiff.comp hG).contDiffOn
  · intro x hx
    exact (h.hasFDerivAt_of_continuous_on hU hu hG.continuous hx).hasFDerivWithinAt

/-- Multiplication by a smooth cutoff strictly inside an open domain gives global regularity. -/
theorem sobolevChain_contDiff_cutoff {n : ℕ} {k : WithTop ℕ∞}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ k u U) (hη : ContDiff ℝ k η) (hsη : tsupport η ⊆ U) :
    ContDiff ℝ k (fun x => η x * u x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hη.contDiffAt.mul ((hu x hx).contDiffAt (hU.mem_nhds hx))
  · have hs : x ∉ tsupport η := fun h => hx (hsη h)
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hs)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [hy]

/-- H² functions in dimensions at most three have continuous representatives on smaller balls. -/
theorem interior_sobolevOrder_two_continuous {n : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasSobolevOrderOn 2 u (ball z R)) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, Continuous w ∧
      w =ᵐ[volume.restrict (ball z r)] u := by
  obtain ⟨G, H, hH⟩ := hasSobolevOrderOn_two_iff.mp hu
  obtain ⟨h, hf⟩ := hH.hasDistributionalLaplacianOn
  obtain ⟨C, _, hb⟩ := interior_poisson_continuous hn z hrR
  obtain ⟨w, hw, heq, _⟩ := hb u _ h hu.memLp hf
  exact ⟨w, hw, heq⟩

/-- Actual weak H^(k+2) regularity gives a C^k representative on each smaller ball. -/
theorem interior_sobolev_contDiff {n k : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasSobolevOrderOn (k + 2) u (ball z R)) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ k w ∧
      w =ᵐ[volume.restrict (ball z r)] u := by
  classical
  induction k generalizing r R u with
  | zero =>
    obtain ⟨w, hw, heq⟩ := interior_sobolevOrder_two_continuous hn z hrR hu
    exact ⟨w, contDiff_zero.mpr hw, heq⟩
  | succ k ih =>
    let s := (r + R) / 2
    have hrs : r < s := by dsimp [s]; linarith
    have hsR : s < R := by dsimp [s]; linarith
    obtain ⟨w, hw, hweq⟩ := interior_sobolevOrder_two_continuous hn z hsR
      (hu.of_le (by omega))
    obtain ⟨G, hG, hGi⟩ := hu
    choose v hv hveq using fun i => ih hsR (hGi i)
    let W (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => v i x)
    have hW : ContDiff ℝ k W := contDiff_euclidean.mpr (fun i => hv i)
    have hWeq : W =ᵐ[volume.restrict (ball z s)] G := by
      filter_upwards [ae_all_iff.mpr hveq] with x hx
      exact PiLp.ext (fun i => hx i)
    have hweak : HasWeakGradientOn w W (ball z s) :=
      ((hG.mono (ball_subset_ball hsR.le)).congr_ae hweq.symm hWeq.symm).toHasWeakGradientOn
    have hcw := hweak.contDiffOn_succ_of_continuous isOpen_ball hw hW
    obtain ⟨η, hη, _, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact
      (isCompact_closedBall z r) isOpen_ball (closedBall_subset_ball hrs)
    refine ⟨fun x => η x * w x,
      sobolevChain_contDiff_cutoff isOpen_ball hcw (hη.of_le (by simp)) hsη, ?_⟩
    have heq := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrs.le) hweq
    filter_upwards [heq, ae_restrict_mem measurableSet_ball] with x hx hxr
    have hηx : η x = 1 := (hone.filter_mono
      (nhds_le_nhdsSet (mem_closedBall.mpr (mem_ball.mp hxr).le))).self_of_nhds
    rw [hηx, one_mul, hx]

end LiquidDrop
