module

public import Mathlib

@[expose] public section

/-!
# Singh Theorem: algebraic core

Pointwise loop-equation identities for the Hua (Cauchy) ensemble
`P_{n,h}(u) ∝ ∏ (1+u_k^2)^{-(n+h)} ∏_{j<k} (u_j-u_k)^2`,
the solution of the two loop equations, and the closed form
`c_N = (π^2/15)(1 - 4/N^2)`.
-/

open Finset BigOperators

namespace Singh

variable {n : ℕ}

/-- Antisymmetrization: for distinct points,
`∑_{k≠j} a_k/(u_k-u_j) = (1/2) ∑_{k≠j} (a_k-a_j)/(u_k-u_j)`. -/
theorem pair_sum_symm (u a : Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, a k / (u k - u j)
      = (1/2) * ∑ k, ∑ j ∈ univ.erase k, (a k - a j) / (u k - u j) := by
  have hswap : ∑ k, ∑ j ∈ univ.erase k, a k / (u k - u j)
      = ∑ k, ∑ j ∈ univ.erase k, (- a j) / (u k - u j) := by
    have h1 : ∀ f : Fin n → Fin n → ℝ,
        ∑ k, ∑ j ∈ univ.erase k, f k j = ∑ k, ∑ j ∈ univ.erase k, f j k := by
      intro f
      simp only [sum_erase_eq_sub (mem_univ _)]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]
    rw [h1]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    rw [show u j - u k = -(u k - u j) by ring, div_neg, neg_div]
  have : ∑ k, ∑ j ∈ univ.erase k, (a k - a j) / (u k - u j)
      = ∑ k, ∑ j ∈ univ.erase k, a k / (u k - u j)
        + ∑ k, ∑ j ∈ univ.erase k, (- a j) / (u k - u j) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [this, ← hswap]; ring

/-- Sum over ordered pairs `k ≠ j` of a constant. -/
theorem sum_offdiag_const (c : ℝ) :
    ∑ k : Fin n, ∑ _j ∈ univ.erase k, c = (n : ℝ) * (n - 1) * c := by
  simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rcases n with _ | m
  · simp
  · push_cast; ring

/-- `∑_{k≠j} (u_k + u_j) = 2(n-1) ∑ u`. -/
theorem sum_offdiag_add (u : Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, (u k + u j) = 2 * ((n : ℝ) - 1) * ∑ k, u k := by
  have e : ∀ k, ∑ j ∈ univ.erase k, (u k + u j)
      = ((n : ℝ) - 1) * u k + (∑ j, u j - u k) := by
    intro k
    rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, nsmul_eq_mul, sum_erase_eq_sub (mem_univ _)]
    rcases n with _ | m
    · exact (Fin.elim0 k)
    · push_cast; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_sum]
  ring

/-- `∑_k u_k ∑_{j≠k} u_j = (∑ u)^2 - ∑ u^2`. -/
theorem sum_offdiag_mul (u : Fin n → ℝ) :
    ∑ k, u k * ∑ j ∈ univ.erase k, u j = (∑ k, u k) ^ 2 - ∑ k, u k ^ 2 := by
  have e : ∀ k, u k * ∑ j ∈ univ.erase k, u j = u k * ∑ j, u j - u k ^ 2 := by
    intro k
    rw [sum_erase_eq_sub (mem_univ _)]; ring
  simp only [e, sum_sub_distrib, ← sum_mul]
  ring

/-- `∑_{k≠j} (u_k^2 + u_j^2) = 2(n-1) ∑ u^2`. -/
theorem sum_offdiag_sq (u : Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, (u k ^ 2 + u j ^ 2) = 2 * ((n : ℝ) - 1) * ∑ k, u k ^ 2 :=
  sum_offdiag_add (fun k => u k ^ 2)

/-- Additivity of off-diagonal sums. -/
theorem sum_offdiag_add3 (f g e : Fin n → Fin n → ℝ) :
    ∑ k, ∑ j ∈ univ.erase k, (f k j + (g k j + e k j))
      = ∑ k, ∑ j ∈ univ.erase k, f k j + (∑ k, ∑ j ∈ univ.erase k, g k j
        + ∑ k, ∑ j ∈ univ.erase k, e k j) := by
  simp only [sum_add_distrib]

/-- First pair identity: `∑_{k≠j} 2(1+u_k^2)/(u_k-u_j) = 2(n-1) ∑ u_k`. -/
theorem pair_identity_a (u : Fin n → ℝ) (hu : Function.Injective u) :
    ∑ k, ∑ j ∈ univ.erase k, 2 * (1 + u k ^ 2) / (u k - u j)
      = 2 * ((n : ℝ) - 1) * ∑ k, u k := by
  rw [pair_sum_symm]
  have : ∀ k, ∀ j ∈ univ.erase k,
      (2 * (1 + u k ^ 2) - 2 * (1 + u j ^ 2)) / (u k - u j) = 2 * (u k + u j) := by
    intro k j hj
    have hne : u k - u j ≠ 0 := sub_ne_zero.mpr (hu.ne (ne_of_mem_erase hj).symm)
    field_simp; ring
  rw [sum_congr rfl fun k _ => sum_congr rfl (this k)]
  simp only [← mul_sum]
  rw [sum_offdiag_add]; ring

/-- Second pair identity:
`∑_{k≠j} 2u_k(1+u_k^2)/(u_k-u_j) = n(n-1) + 2(n-1)∑u^2 + (∑u)^2 - ∑u^2`. -/
theorem pair_identity_b (u : Fin n → ℝ) (hu : Function.Injective u) :
    ∑ k, ∑ j ∈ univ.erase k, 2 * (u k * (1 + u k ^ 2)) / (u k - u j)
      = (n : ℝ) * (n - 1) + 2 * ((n : ℝ) - 1) * ∑ k, u k ^ 2
        + (∑ k, u k) ^ 2 - ∑ k, u k ^ 2 := by
  rw [pair_sum_symm]
  have : ∀ k, ∀ j ∈ univ.erase k,
      (2 * (u k * (1 + u k ^ 2)) - 2 * (u j * (1 + u j ^ 2))) / (u k - u j)
        = 2 * 1 + (2 * (u k ^ 2 + u j ^ 2) + 2 * (u k * u j)) := by
    intro k j hj
    have hne : u k - u j ≠ 0 := sub_ne_zero.mpr (hu.ne (ne_of_mem_erase hj).symm)
    field_simp; ring
  rw [sum_congr rfl fun k _ => sum_congr rfl (this k)]
  have e := sum_offdiag_add3 (fun _ _ => 2 * (1 : ℝ)) (fun k j => 2 * (u k ^ 2 + u j ^ 2))
    (fun k j => 2 * (u k * u j))
  rw [e]
  simp only [← mul_sum]
  rw [sum_offdiag_const, sum_offdiag_sq, sum_offdiag_mul]; ring

/-- Logarithmic derivative of the Hua density in the variable `u_k`. -/
noncomputable def logDeriv (h : ℝ) (u : Fin n → ℝ) (k : Fin n) : ℝ :=
  -(2 * ((n : ℝ) + h) * u k) / (1 + u k ^ 2) + ∑ j ∈ univ.erase k, 2 / (u k - u j)

/-- Divergence integrand for loop equation (a):
`∑_k P^{-1} ∂_k[(1+u_k^2) F P]` with `F = ∑ u`. -/
noncomputable def divA (h : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ k, (2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (1 + u k ^ 2) * (∑ j, u j) * logDeriv h u k)

/-- Divergence integrand for loop equation (b):
`∑_k P^{-1} ∂_k[(1+u_k^2) u_k P]`. -/
noncomputable def divB (h : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ k, ((1 + 3 * u k ^ 2) + (1 + u k ^ 2) * u k * logDeriv h u k)

private lemma pos_sq (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity

/-- Pointwise form of loop equation (a). -/
theorem divA_eq (h : ℝ) (u : Fin n → ℝ) (hu : Function.Injective u) :
    divA h u = (n : ℝ) + ∑ k, u k ^ 2 - 2 * h * (∑ k, u k) ^ 2 := by
  have hk : ∀ k, (1 + u k ^ 2) * logDeriv h u k
      = -(2 * ((n : ℝ) + h) * u k)
        + ∑ j ∈ univ.erase k, 2 * (1 + u k ^ 2) / (u k - u j) := by
    intro k
    unfold logDeriv
    rw [mul_add, mul_sum]
    congr 1
    · field_simp [pos_sq (u k)]
    · exact sum_congr rfl fun j _ => by ring
  unfold divA
  have : ∀ k, 2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (1 + u k ^ 2) * (∑ j, u j) * logDeriv h u k
      = 2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (∑ j, u j) * (-(2 * ((n : ℝ) + h) * u k))
        + (∑ j, u j) * ∑ j ∈ univ.erase k, 2 * (1 + u k ^ 2) / (u k - u j) := by
    intro k
    rw [show (1 + u k ^ 2) * (∑ j, u j) * logDeriv h u k
        = (∑ j, u j) * ((1 + u k ^ 2) * logDeriv h u k) by ring, hk]; ring
  rw [sum_congr rfl fun k _ => this k]
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul, sum_neg_distrib]
  rw [pair_identity_a u hu]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Pointwise form of loop equation (b). -/
theorem divB_eq (h : ℝ) (u : Fin n → ℝ) (hu : Function.Injective u) :
    divB h u = (n : ℝ) ^ 2 - 2 * h * ∑ k, u k ^ 2 + (∑ k, u k) ^ 2 := by
  have hk : ∀ k, (1 + u k ^ 2) * u k * logDeriv h u k
      = -(2 * ((n : ℝ) + h) * u k ^ 2)
        + ∑ j ∈ univ.erase k, 2 * (u k * (1 + u k ^ 2)) / (u k - u j) := by
    intro k
    unfold logDeriv
    rw [mul_add, mul_sum]
    congr 1
    · field_simp [pos_sq (u k)]
    · exact sum_congr rfl fun j _ => by ring
  unfold divB
  rw [sum_congr rfl fun k _ => by rw [hk k]]
  simp only [sum_add_distrib, ← mul_sum, sum_neg_distrib]
  rw [pair_identity_b u hu]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Solution of the two loop equations. If `n + Q = 2h M` and
`n^2 - 2h Q + M = 0` with `4h^2 ≠ 1`, then `M = n(n+2h)/(4h^2-1)`. -/
theorem loop_solution (n h M Q : ℝ) (hh : 4 * h ^ 2 - 1 ≠ 0)
    (ha : n + Q = 2 * h * M) (hb : n ^ 2 - 2 * h * Q + M = 0) :
    M = n * (n + 2 * h) / (4 * h ^ 2 - 1) := by
  rw [eq_div_iff hh]
  have hQ : Q = 2 * h * M - n := by linarith
  subst hQ
  linear_combination -hb

/-- At `h = 2` and `n = N - 2`: `E[S^2] = M/4 = (N^2-4)/60`. -/
theorem moment_h2 (N : ℝ) :
    (N - 2) * ((N - 2) + 2 * 2) / (4 * 2 ^ 2 - 1) / 4 = (N ^ 2 - 4) / 60 := by
  ring

/-- Closed form of the constant: `(2π/N)^2 (N^2-4)/60 = (π^2/15)(1-4/N^2)`. -/
theorem cN_closed_form (N : ℝ) (hN : N ≠ 0) :
    (2 * Real.pi / N) ^ 2 * ((N ^ 2 - 4) / 60) = Real.pi ^ 2 / 15 * (1 - 4 / N ^ 2) := by
  field_simp; ring

/-- The Singh constant. -/
noncomputable def cN (N : ℕ) : ℝ := Real.pi ^ 2 / 15 * (1 - 4 / (N : ℝ) ^ 2)

/-- `c_N → π^2/15` as `N → ∞`. -/
theorem cN_tendsto :
    Filter.Tendsto cN Filter.atTop (nhds (Real.pi ^ 2 / 15)) := by
  have h : Filter.Tendsto (fun N : ℕ => (4 : ℝ) / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h2
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  unfold cN
  simpa using (tendsto_const_nhds (x := Real.pi ^ 2 / 15)).mul this

end Singh
