module

public import Singh.Hua
public import Singh.Loop
public import Singh.Cayley
public import Singh.Linear

@[expose] public section

/-!
# Singh Theorem: analytic statement

For `U ∈ U(N)` Haar distributed, adjacent eigenangles `θ₁ < θ₂` with normalized gap
`s = N(θ₂-θ₁)/(2π)`, and `x - y = log|Λ'(θ₁)| - log|Λ'(θ₂)|`,
`Var(x - y | s) = c_N s^2 (1 + o(1))` as `s → 0`, with `c_N = (π^2/15)(1 - 4/N^2)`.

The analytic inputs are recorded as named fields of `CUEPairData`:
* `linearization`: conditioning on the pair via the Weyl integration formula and the
  Taylor linearization, giving `Var(x-y|s)/s^2 → (2π/N)^2 E_{w₀}[S^2]`;
The Cayley transform `u = cot(θ/2)` identifying `E_{w₀}[S^2] = circleE (N-2)` with the
Hua ensemble moment `E_{n,2}[(∑u/2)^2]` is `circleE_eq_hua` in `Singh.Cayley`.
The loop equations `huaMeasure_loopA`, `huaMeasure_loopB` are proved in `Singh.Loop`
by integration by parts. The Hua measure `huaMeasure` is defined explicitly by its density; its normalization,
absolute continuity and the needed integrability are proved in `Singh.Hua`.
The linearization is proved in `Singh.Linear` (`palmVar_tendsto`) for the conditional
variance `palmVar` under the Weyl density of the remaining `N-2` angles given an adjacent
pair at gap `2πs/N`; `cuePairData` supplies it, and `theorem_cN_CUE` is the resulting
statement with no remaining inputs.
-/

open MeasureTheory Filter Topology Finset

namespace Singh

variable {n : ℕ}

/-- Second moment of `∑ u_k` in the Hua ensemble from the two loop equations. -/
theorem hua_second_moment (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 4 * h ^ 2 - 1 ≠ 0)
    (hinj : ∀ᵐ u ∂μ, Function.Injective u)
    (hF : Integrable (fun u : Fin n → ℝ => (∑ k, u k) ^ 2) μ)
    (hQ : Integrable (fun u : Fin n → ℝ => ∑ k, u k ^ 2) μ)
    (hA : ∫ u, divA h u ∂μ = 0) (hB : ∫ u, divB h u ∂μ = 0) :
    ∫ u, (∑ k, u k) ^ 2 ∂μ = (n : ℝ) * ((n : ℝ) + 2 * h) / (4 * h ^ 2 - 1) := by
  have eA : ∫ u, divA h u ∂μ
      = ∫ u, ((n : ℝ) + ∑ k, u k ^ 2 - 2 * h * (∑ k, u k) ^ 2) ∂μ :=
    integral_congr_ae (hinj.mono fun u hu => divA_eq h u hu)
  have eB : ∫ u, divB h u ∂μ
      = ∫ u, ((n : ℝ) ^ 2 - 2 * h * ∑ k, u k ^ 2 + (∑ k, u k) ^ 2) ∂μ :=
    integral_congr_ae (hinj.mono fun u hu => divB_eq h u hu)
  have c1 : Integrable (fun _ : Fin n → ℝ => (n : ℝ)) μ := integrable_const _
  have c2 : Integrable (fun _ : Fin n → ℝ => (n : ℝ) ^ 2) μ := integrable_const _
  have iA : Integrable (fun u : Fin n → ℝ => (n : ℝ) + ∑ k, u k ^ 2) μ := c1.add hQ
  have iF : Integrable (fun u : Fin n → ℝ => 2 * h * (∑ k, u k) ^ 2) μ := hF.const_mul _
  have iQ : Integrable (fun u : Fin n → ℝ => 2 * h * ∑ k, u k ^ 2) μ := hQ.const_mul _
  have iB : Integrable (fun u : Fin n → ℝ => (n : ℝ) ^ 2 - 2 * h * ∑ k, u k ^ 2) μ :=
    c2.sub iQ
  rw [eA, integral_sub iA iF, integral_add c1 hQ, integral_const_mul, integral_const] at hA
  rw [eB, integral_add iB hF, integral_sub c2 iQ, integral_const_mul, integral_const] at hB
  simp only [probReal_univ, smul_eq_mul, one_mul] at hA hB
  exact loop_solution _ _ _ _ hh (by linarith) hB

/-- `E_{n,2}[(∑u)^2] = n(n+4)/15` for the Hua ensemble. -/
theorem huaMeasure_second_moment (n : ℕ) :
    ∫ u, (∑ k, u k) ^ 2 ∂(huaMeasure n) = (n : ℝ) * ((n : ℝ) + 4) / 15 := by
  have := hua_second_moment (huaMeasure n) 2 (by norm_num) huaMeasure_ae_injective
    huaMeasure_int_sq_sum huaMeasure_int_sum_sq huaMeasure_loopA huaMeasure_loopB
  rw [this]; ring

/-- Analytic inputs for the CUE close-pair problem at matrix size `N`. -/
structure CUEPairData (N : ℕ) where
  /-- `V s = Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s)`. -/
  V : ℝ → ℝ
  linearization :
    Tendsto (fun s => V s / s ^ 2) (𝓝[>] 0) (𝓝 ((2 * Real.pi / N) ^ 2 * circleE (N - 2)))

/-- `E_{w₀}[S^2] = (N^2-4)/60`. -/
theorem Ew0_eq {N : ℕ} (hN : 2 ≤ N) :
    circleE (N - 2) = ((N : ℝ) ^ 2 - 4) / 60 := by
  have hm := huaMeasure_second_moment (N - 2)
  have hc : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub hN]; norm_num
  rw [circleE_eq_hua]
  have : (fun u : Fin (N - 2) → ℝ => ((∑ k, u k) / 2) ^ 2)
      = fun u => (1 / 4 : ℝ) * (∑ k, u k) ^ 2 := by
    funext u; ring
  rw [this, integral_const_mul, hm, hc]
  ring

/-- **Singh Theorem.** `Var(x - y | s) / s^2 → c_N = (π^2/15)(1 - 4/N^2)` as `s → 0⁺`. -/
theorem theorem_cN {N : ℕ} (hN : 2 ≤ N) (D : CUEPairData N) :
    Tendsto (fun s => D.V s / s ^ 2) (𝓝[>] 0) (𝓝 (cN N)) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  have h := D.linearization
  rwa [Ew0_eq hN, cN_closed_form _ hN0] at h

/-- **Singh Theorem**, little-o form: `Var(x - y | s) = c_N s^2 + o(s^2)`. -/
theorem theorem_cN_isLittleO {N : ℕ} (hN : 2 ≤ N) (D : CUEPairData N) :
    (fun s => D.V s - cN N * s ^ 2) =o[𝓝[>] 0] (fun s => s ^ 2) := by
  have ht := theorem_cN hN D
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have : (fun s => (D.V s - cN N * s ^ 2) / s ^ 2) =ᶠ[𝓝[>] 0]
        fun s => D.V s / s ^ 2 - cN N := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have : s ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
      rw [sub_div, mul_div_assoc, div_self this, mul_one]
    rw [tendsto_congr' this]
    simpa using ht.sub_const (cN N)
  · filter_upwards [self_mem_nhdsWithin] with s hs h0
    exact absurd h0 (pow_ne_zero _ (ne_of_gt hs))

/-- `V s = Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s)` for an adjacent pair at normalized gap `s`,
under the Weyl density of the remaining `N-2` eigenangles. -/
noncomputable def cueV (N : ℕ) (s : ℝ) : ℝ := palmVar (N - 2) (2 * Real.pi / N * s)

theorem cueV_linearization {N : ℕ} (hN : 0 < N) :
    Tendsto (fun s => cueV N s / s ^ 2) (𝓝[>] 0)
      (𝓝 ((2 * Real.pi / N) ^ 2 * circleE (N - 2))) := by
  have hc : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hg : Tendsto (fun s : ℝ => 2 * Real.pi / N * s) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => 2 * Real.pi / N * s) (𝓝 0) (𝓝 (2 * Real.pi / N * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hc hs
  have h := ((palmVar_tendsto (N - 2)).comp hg).const_mul ((2 * Real.pi / N) ^ 2)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  simp only [Function.comp, cueV]
  field_simp

/-- The analytic input, supplied by `Singh.Linear`. -/
noncomputable def cuePairData {N : ℕ} (hN : 0 < N) : CUEPairData N where
  V := cueV N
  linearization := cueV_linearization hN

/-- **Singh Theorem**: `Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s) / s^2 → c_N` as `s → 0⁺`. -/
theorem theorem_cN_CUE {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun s => cueV N s / s ^ 2) (𝓝[>] 0) (𝓝 (cN N)) :=
  theorem_cN hN (cuePairData (by omega))

/-- **Singh Theorem**, little-o form: `Var(x - y | s) = c_N s^2 + o(s^2)`. -/
theorem theorem_cN_CUE_isLittleO {N : ℕ} (hN : 2 ≤ N) :
    (fun s => cueV N s - cN N * s ^ 2) =o[𝓝[>] 0] (fun s => s ^ 2) :=
  theorem_cN_isLittleO hN (cuePairData (by omega))

end Singh
