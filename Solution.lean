module

public import Singh

@[expose] public section

/-!
# Singh Theorem: proof

The statements of `Challenge.lean`, proved from the development in `Singh`.
-/

open Filter Topology

namespace Singh

theorem singh_theorem {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun s => cueV N s / s ^ 2) (𝓝[>] 0)
      (𝓝 (Real.pi ^ 2 / 15 * (1 - 4 / (N : ℝ) ^ 2))) :=
  theorem_cN_CUE hN

theorem singh_theorem_isLittleO {N : ℕ} (hN : 2 ≤ N) :
    (fun s => cueV N s - Real.pi ^ 2 / 15 * (1 - 4 / (N : ℝ) ^ 2) * s ^ 2)
      =o[𝓝[>] 0] (fun s => s ^ 2) :=
  theorem_cN_CUE_isLittleO hN

end Singh
