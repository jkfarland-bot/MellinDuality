module

public import MellinDuality.Defs

@[expose] public section

/-!
# Half systems, the multiplier constant and its Bernoulli form

* `sum_univ_eq_sum_half`: a sum over `ZMod p` of a function vanishing at `0` is the sum over the
  half system of `f(n) + f(-n)`;
* `G_eq_two_mul_half`: for odd `φ`, `𝒢(φ) = 2 ∑_{0 < n < p/2} φ(n) (-1)^n`;
* `G_eq_zero_of_even`: `𝒢(φ) = 0` for even `φ`;
* `G_eq_two_mul_char_two_mul_half`: `𝒢(ψ) = 2 ψ(2) ∑_{0 < m < p/2} ψ(m)` for odd `ψ`;
* `bernoulli_form`: the classical half-sum identity in the form `p 𝒢(ψ) = 2 (1 - 2ψ(2)) T(ψ)`,
  i.e. `𝒢(ψ) = 2 (1 - 2ψ(2)) B_{1,ψ}`, for odd `ψ` (Paper II, (1)).
-/

namespace MellinDuality

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma odd_p (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2

lemma val_neg_of_ne_zero' {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by
  rw [ZMod.neg_val, ite_eq_right_iff.mpr (fun h => absurd h hx)]

lemma val_pos_of_ne_zero {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hx

lemma neg_one_pow_sub (hp2 : p ≠ 2) {v : ℕ} (hv : v ≤ p) :
    (-1 : ℤ) ^ (p - v) = -(-1) ^ v := by
  have ho := odd_p hp2
  calc (-1 : ℤ) ^ (p - v) = (-1) ^ (p - v) * ((-1) ^ v * (-1) ^ v) := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
    _ = (-1) ^ (p - v + v) * (-1) ^ v := by ring
    _ = -(-1) ^ v := by rw [Nat.sub_add_cancel hv, ho.neg_one_pow]; ring

lemma parSign_neg (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : parSign (-x) = -parSign x := by
  unfold parSign
  rw [val_neg_of_ne_zero' hx, neg_one_pow_sub hp2 (ZMod.val_lt x).le]

omit hp in
lemma parSign_sq (x : ZMod p) : parSign x * parSign x = 1 := by
  unfold parSign; rw [← pow_add, ← two_mul, pow_mul]; simp

lemma mem_half_iff {x : ZMod p} : x ∈ half p ↔ 2 * x.val < p := by simp [half]

lemma zero_mem_half : (0 : ZMod p) ∈ half p := by
  rw [mem_half_iff, ZMod.val_zero]; exact hp.out.pos

lemma neg_mem_half_iff (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : -x ∈ half p ↔ x ∉ half p := by
  rw [mem_half_iff, mem_half_iff, val_neg_of_ne_zero' hx]
  have h1 := ZMod.val_lt x
  have h2 := val_pos_of_ne_zero hx
  obtain ⟨k, hk⟩ := odd_p hp2
  omega

/-- A sum over `ZMod p` of a function vanishing at `0` is the sum over the half system of
`f(n) + f(-n)`. -/
theorem sum_univ_eq_sum_half (hp2 : p ≠ 2) {M : Type*} [AddCommMonoid M] (f : ZMod p → M)
    (h0 : f 0 = 0) : ∑ x, f x = ∑ n ∈ half p, (f n + f (-n)) := by
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not univ (· ∈ half p)]
  congr 1
  · congr 1; ext x; simp
  · rw [← sum_erase (half p) (a := 0) (f := fun n => f (-n)) (by simp [h0])]
    refine sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have hx0 : x ≠ 0 := by rintro rfl; exact hx zero_mem_half
      simp only [mem_erase, ne_eq, neg_eq_zero]
      exact ⟨hx0, (neg_mem_half_iff hp2 hx0).2 hx⟩
    · intro x hx
      simp only [mem_erase, ne_eq] at hx
      simp only [mem_filter, mem_univ, true_and]
      exact fun h => ((neg_mem_half_iff hp2 hx.1).1 h) hx.2
    · intro x _; simp
    · intro x _; simp
    · intro x _; simp

variable {R : Type*} [CommRing R]

lemma apply_neg_of_odd (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) (x : ZMod p) :
    φ (-x) = -φ x := by
  rw [neg_eq_neg_one_mul, map_mul, hφ]; ring

lemma apply_neg_of_even (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) (x : ZMod p) :
    φ (-x) = φ x := by
  rw [neg_eq_neg_one_mul, map_mul, hφ]; ring

/-- For odd `φ`, `𝒢(φ) = 2 ∑_{0 < n < p/2} φ(n) (-1)^n`. -/
theorem G_eq_two_mul_half (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) :
    G φ = 2 * ∑ n ∈ half p, φ n * (parSign n : R) := by
  unfold G
  rw [sum_univ_eq_sum_half hp2 _ (by simp [MulChar.map_zero]), mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · rw [apply_neg_of_odd φ hφ, parSign_neg hp2 hn]; push_cast; ring

/-- `𝒢(φ) = 0` for even `φ`. -/
theorem G_eq_zero_of_even (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) : G φ = 0 := by
  unfold G
  rw [sum_univ_eq_sum_half hp2 _ (by simp [MulChar.map_zero])]
  refine sum_eq_zero fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · rw [apply_neg_of_even φ hφ, parSign_neg hp2 hn]; push_cast; ring

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)

lemma val_two_mul_of_mem_half {n : ZMod p} (hn : n ∈ half p) : (2 * n).val = 2 * n.val := by
  rw [mem_half_iff] at hn
  have : (2 * n : ZMod p) = ((2 * n.val : ℕ) : ZMod p) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast_of_lt hn]

/-- Reindexing by `x = 2y`. -/
lemma sum_mul_two (hp2 : p ≠ 2) {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ x, f x = ∑ y, f (2 * y) :=
  (Fintype.sum_bijective _ (Equiv.mulLeft₀ (2 : ZMod p) (two_ne_zero_zmod hp2)).bijective
    (fun y => f (2 * y)) f fun _ => rfl).symm

/-- `𝒢(ψ) = 2 ψ(2) ∑_{0 < m < p/2} ψ(m)` for odd `ψ`. -/
theorem G_eq_two_mul_char_two_mul_half (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R)
    (hψ : ψ (-1) = -1) : G ψ = 2 * ψ 2 * ∑ n ∈ half p, ψ n := by
  unfold G
  rw [sum_mul_two hp2]
  simp only [map_mul]
  simp_rw [mul_assoc (ψ 2)]
  rw [← mul_sum, sum_univ_eq_sum_half hp2 (fun y => ψ y * (parSign (2 * y) : R))
    (by simp [MulChar.map_zero]), mul_sum, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  by_cases hn0 : n = 0
  · subst hn0; simp [MulChar.map_zero]
  · have h2n : (2 * n : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_zmod hp2) hn0
    have hs : parSign (2 * n) = 1 := by
      unfold parSign; rw [val_two_mul_of_mem_half hn, pow_mul]; simp
    rw [show (2 : ZMod p) * -n = -(2 * n) by ring, parSign_neg hp2 h2n, hs,
      apply_neg_of_odd ψ hψ]
    push_cast; ring

/-- **The half-sum identity** (classical), in the form `p 𝒢(ψ) = 2 (1 - 2ψ(2)) T(ψ)` with
`T(ψ) = ∑ ψ(m) m = p B_{1,ψ}`; that is, `𝒢(ψ) = 2 (1 - 2ψ(2)) B_{1,ψ}` for odd `ψ`
(Paper II, (1)). -/
theorem bernoulli_form (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R) (hψ : ψ (-1) = -1) :
    (p : R) * G ψ = 2 * (1 - 2 * ψ 2) * T ψ := by
  set U := ∑ n ∈ half p, ψ n with hU
  set Th := ∑ n ∈ half p, ψ n * (n.val : R) with hTh
  have ha := G_eq_two_mul_char_two_mul_half hp2 ψ hψ
  have hb : T ψ = 2 * Th - p * U := by
    unfold T
    rw [sum_univ_eq_sum_half hp2 _ (by simp [MulChar.map_zero]), hTh, hU, mul_sum, mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn0 : n = 0
    · subst hn0; simp [MulChar.map_zero]
    · rw [apply_neg_of_odd ψ hψ, val_neg_of_ne_zero' hn0,
        Nat.cast_sub (ZMod.val_lt n).le]
      ring
  have hc' : ∑ y : ZMod p, ψ y * ((2 * y).val : R) = 4 * Th - p * U := by
    rw [sum_univ_eq_sum_half hp2 (fun y => ψ y * ((2 * y).val : R))
      (by simp [MulChar.map_zero]), hTh, hU, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    by_cases hn0 : n = 0
    · subst hn0; simp [MulChar.map_zero]
    · have h2n : (2 * n : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_zmod hp2) hn0
      have hv := val_two_mul_of_mem_half hn
      have hle : 2 * n.val ≤ p := by rw [← hv]; exact (ZMod.val_lt _).le
      rw [show (2 : ZMod p) * -n = -(2 * n) by ring, val_neg_of_ne_zero' h2n, hv,
        apply_neg_of_odd ψ hψ, Nat.cast_sub hle]
      push_cast; ring
  have hc : T ψ = ψ 2 * (4 * Th - p * U) := by
    unfold T
    rw [sum_mul_two hp2, ← hc', mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [map_mul]; ring
  rw [ha]
  linear_combination (-2 : R) * hc + 4 * ψ 2 * hb

end MellinDuality
