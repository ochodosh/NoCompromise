module

public import NoCompromise.Capacity.Levels
public import NoCompromise.Topology.ComponentCountMain

@[expose] public section

/-!
# Level connectedness (blueprint `lem:level-connected`), unconditional

`level_connected_of_component_count` in `Capacity/Levels.lean` took the component-count
theorem as a named hypothesis; `componentCountStatement_holds` (blueprint
`thm:component-count`, `Topology/ComponentCountMain.lean`) discharges it.
-/

open Filter Topology

namespace LiquidDrop

/-- Blueprint `lem:level-connected`: for a continuous `u` equal to one on a compact connected
`K`, harmonic and smooth off `K`, tending to zero at infinity and strictly between zero and one
off `K`, every regular level `{u = s}` with `0 < s < 1` is connected. -/
theorem level_connected {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hconn : IsConnected K) {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hKval : ∀ x ∈ K, u x = 1)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0))
    (hstrict : ∀ x ∉ K, 0 < u x ∧ u x < 1)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hreg : ∀ x ∈ levelSet u s, gradient u x ≠ 0) : IsConnected (levelSet u s) :=
  level_connected_of_component_count componentCountStatement_holds hK hconn hu hKval hh hsmooth
    hinf hstrict hs hs1 hreg

end LiquidDrop
