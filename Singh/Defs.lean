module

public import Mathlib

@[expose] public section

/-!
# Singh Theorem: definitions

Shared definitions; `Challenge.lean` restates this text verbatim.
-/

open MeasureTheory Finset Real Filter Topology

namespace Singh

variable {n : ℕ}

/-- Ordered pairs `a < b`. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

/-- `fL x = log|sin(x/2)|`; `log|e^{iφ}-e^{iψ}| = log 2 + fL(φ-ψ)`. -/
noncomputable def fL (x : ℝ) : ℝ := Real.log (sin (x / 2))

/-- `log|Λ'(θ₁)| - log|Λ'(θ₂)|` for eigenangles `θ₁ = -δ/2`, `θ₂ = δ/2` and the remaining
angles `θ`: the common factor `|e^{iθ₁}-e^{iθ₂}|` cancels. -/
noncomputable def Xd (δ : ℝ) (θ : Fin n → ℝ) : ℝ := ∑ k, (fL (θ k + δ / 2) - fL (θ k - δ / 2))

/-- Adjacency: no remaining angle lies in the arc `(-δ/2, δ/2)`. -/
noncomputable def boxD (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo (δ / 2) (2 * π - δ / 2)

/-- Weyl density of the remaining angles given eigenangles at `±δ/2`, before restriction:
`∏_{a<b} |e^{iθ_a}-e^{iθ_b}|^2 ∏_k |e^{iθ_k}-e^{-iδ/2}|^2 |e^{iθ_k}-e^{iδ/2}|^2`
up to a constant factor. -/
noncomputable def pwRaw (δ : ℝ) (θ : Fin n → ℝ) : ℝ :=
  (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2)
    * ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2)

/-- Conditional (Palm) weight of the remaining angles for an adjacent pair at gap `δ`. -/
noncomputable def pw (δ : ℝ) (θ : Fin n → ℝ) : ℝ := (boxD n δ).indicator (pwRaw δ) θ

/-- Conditional variance of `Xd δ` under the Palm weight. -/
noncomputable def palmVar (n : ℕ) (δ : ℝ) : ℝ :=
  (∫ θ : Fin n → ℝ, Xd δ θ ^ 2 * pw δ θ) / (∫ θ : Fin n → ℝ, pw δ θ)
    - ((∫ θ : Fin n → ℝ, Xd δ θ * pw δ θ) / (∫ θ : Fin n → ℝ, pw δ θ)) ^ 2

/-- `V s = Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s)` for an adjacent pair at normalized gap `s`,
under the Weyl density of the remaining `N-2` eigenangles. -/
noncomputable def cueV (N : ℕ) (s : ℝ) : ℝ := palmVar (N - 2) (2 * Real.pi / N * s)

end Singh
