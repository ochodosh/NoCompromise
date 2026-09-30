module

public import NoCompromise.Elliptic.SobolevChainCompact
public import NoCompromise.Elliptic.SobolevChainHarmonic
public import NoCompromise.Elliptic.HarmonicMeanValueLocal
public import NoCompromise.Sobolev.SpatialGN

@[expose] public section

/-!
# The Sobolev chain to classical regularity

Our precise Hᵐ norm convention is a finite L² sum. At order zero it is the L² norm.
At each successor it is the L² norm of the function, plus the L² norm of its genuine
weak vector gradient, plus the sum of the preceding-order norms of all coordinates
of that gradient. Thus every term is an actual weak derivative of order at most m;
repeated ordered mixed derivatives are retained. On open domains uniqueness of weak
derivatives proves independence of every representative choice. We do not identify
this sum norm literally with a quadratic Sobolev norm.

The classical estimate bounds the operator norm of every iterated Fréchet derivative
through order k on the specified compact closure. The representative is constructed
from the original L² class. No continuity or classical derivative is assumed of it.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

/-- The canonical finite L² sum norm of genuine weak derivatives, zero off Hᵐ. -/
def sobolevSumNorm {n : ℕ} (m : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : ℝ := by
  classical
  exact if h : HasSobolevOrderOn m u U then
    (Classical.choice (hasSobolevOrderOn_iff_nonempty_derivativeData.mp h)).norm else 0

lemma sobolevSumNorm_nonneg {n m : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} : 0 ≤ sobolevSumNorm m u U := by
  unfold sobolevSumNorm
  split
  · exact SobolevDerivativeData.norm_nonneg _
  · exact le_rfl

/-- The canonical norm equals the explicit norm of every valid derivative witness. -/
theorem SobolevDerivativeData.norm_eq_sobolevSumNorm {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (d : SobolevDerivativeData U m u) :
    d.norm = sobolevSumNorm m u U := by
  rw [sobolevSumNorm, dite_eq_left d.hasSobolevOrderOn]
  exact d.norm_congr_ae hU _ EventuallyEq.rfl

/-- In dimensions two and three the strict Sobolev threshold is an integer gap of two. -/
lemma sobolevChain_order_gap {n m k : ℕ} (hn : n = 2 ∨ n = 3)
    (hm : (k : ℝ) + (n : ℝ) / 2 < (m : ℝ)) : k + 2 ≤ m := by
  have hk : (k : ℝ) + 1 < (m : ℝ) := by
    rcases hn with hn | hn <;> rw [hn] at hm <;> norm_num at hm <;> linarith
  have hk' : k + 1 < m := by exact_mod_cast hk
  omega

/-- The full local Hᵐ-to-Cᵏ estimate in dimensions two and three, in the explicit sum norm.
The constant depends only on the domains and orders, and precedes the original function. -/
theorem sobolev_Hm_Ck {n m k : ℕ} (hn : n = 2 ∨ n = 3)
    (hm : (k : ℝ) + (n : ℝ) / 2 < (m : ℝ))
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    (hcV : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ), HasSobolevOrderOn m u U →
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ k w ∧
        w =ᵐ[volume.restrict V] u ∧ ∀ j ≤ k, ∀ x ∈ closure V,
          ‖iteratedFDeriv ℝ j w x‖ ≤ C * sobolevSumNorm m u U := by
  have hn4 : n < 4 := by rcases hn with h | h <;> omega
  obtain ⟨C, hC, hb⟩ := compact_sobolev_contDiff_bound hn4 (sobolevChain_order_gap hn hm)
    hU hcV hVU
  refine ⟨C, hC, ?_⟩
  intro u hu
  obtain ⟨d⟩ := hasSobolevOrderOn_iff_nonempty_derivativeData.mp hu
  obtain ⟨w, hw, hweq, hwb⟩ := hb u d V hV.measurableSet subset_closure
  refine ⟨w, hw, hweq, ?_⟩
  simpa only [d.norm_eq_sobolevSumNorm hU] using hwb

/-- The global weak H¹-to-L⁶ estimate in three dimensions. -/
theorem sobolev_H1_L6 {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u G univ) : MemLp u 6 volume ∧
      lpNorm u 6 volume ≤ 4 * lpNorm G 2 volume :=
  ⟨hu.memLp_six, hu.lpNorm_six_le⟩

/-- Local Sobolev regularity means actual weak regularity on a neighborhood ball of each point. -/
def HasSobolevOrderLocallyOn {n : ℕ} (m : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧ HasSobolevOrderOn m u (ball x r)

lemma HasSobolevOrderLocallyOn.of_le {n m j : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasSobolevOrderLocallyOn m u U) (hjm : j ≤ m) :
    HasSobolevOrderLocallyOn j u U := by
  intro x hx
  obtain ⟨r, hr, hs, h⟩ := hu x hx
  exact ⟨r, hr, hs, h.of_le hjm⟩

/-- The local elliptic bootstrap follows directly from the interior L² Poisson estimate.
Even local L², rather than local H¹, suffices for the original function. -/
theorem HasDistributionalLaplacianOn.sobolevOrderLocally {n k : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasDistributionalLaplacianOn u f U)
    (hu : HasSobolevOrderLocallyOn 0 u U) (hf : HasSobolevOrderLocallyOn k f U) :
    HasSobolevOrderLocallyOn (k + 2) u U := by
  intro x hx
  obtain ⟨r, hr, hs, hur⟩ := hu x hx
  obtain ⟨s, hs0, _, hfs⟩ := hf x hx
  let R := min r s
  have hR : 0 < R := lt_min hr hs0
  have hRr : ball x R ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have hRs : ball x R ⊆ ball x s := ball_subset_ball (min_le_right _ _)
  refine ⟨R / 2, half_pos hR, (ball_subset_ball (half_le_self hR.le)).trans (hRr.trans hs), ?_⟩
  exact interior_poisson_sobolev_order x (half_lt_self hR) (h.mono (hRr.trans hs))
    ((hur.mono hRr).memLp) (hfs.mono hRs)

/-- Locally L² weakly harmonic functions have smooth harmonic representatives near each point. -/
theorem HasDistributionalLaplacianOn.harmonic_smooth_locally {n : ℕ} (hn : n < 4)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U)
    (hu : HasSobolevOrderLocallyOn 0 u U) :
    ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
        w =ᵐ[volume.restrict (ball x r)] u ∧ ∀ y ∈ ball x r, laplacianN w y = 0 := by
  intro x hx
  obtain ⟨r, hr, hs, hur⟩ := hu x hx
  refine ⟨r / 2, half_pos hr, (ball_subset_ball (half_le_self hr.le)).trans hs, ?_⟩
  exact interior_harmonic_smooth hn x (half_lt_self hr) (h.mono hs) hur.memLp

/-- One smooth representative on the entire domain for a locally L² weakly harmonic function. -/
theorem HasDistributionalLaplacianOn.harmonic_smooth {n : ℕ} (hn : n < 4)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) U)
    (hu : HasSobolevOrderLocallyOn 0 u U) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
      v =ᵐ[volume.restrict U] u ∧ ∀ x ∈ U, laplacianN v x = 0 := by
  have hU : IsOpen U := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r, hr, hs, _⟩ := hu x hx
    exact ⟨r, hr, hs⟩
  apply exists_contDiffOn_representative_of_local hU
  intro x hx
  obtain ⟨r, hr, hs, w, hw, heq, hzero⟩ := h.harmonic_smooth_locally hn hu x hx
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hs, w, hw, heq, hzero⟩

end LiquidDrop
