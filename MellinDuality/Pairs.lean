module

public import MellinDuality.Quartic
public import MellinDuality.Parseval

@[expose] public section

/-!
# The pair structure

`sum_pairs_gcd`: every pair `(n, n')` in `[1, N]²` is `(ar, br)` for exactly one coprime pair
`(a, b)` in `[1, N]²` and one `r ≤ ⌊N / max(a, b)⌋`, namely `r = gcd(n, n')`.

`pair_structure` (Proposition 6.3 of Paper II): for `p ≡ 5 (mod 8)`, a quartic `χ`,
`N = (p - 1)/2`, `ε_n = (-1)^{⌊n²/p⌋}`, `S = ∑_{n ≤ N} χ(n)` and `𝒞 = ∑_{n ≤ N} χ(n) ε_n`, with
all outer sums over coprime `a, b ≤ N` and `K = ⌊N / max(a, b)⌋`:

  `𝒞 S̄ = ∑ χ(a) χ̄(b) ∑_{r ≤ K} ε_{ar}`,         `𝒞 S = ∑ χ(ab) ∑_{r ≤ K} (r/p) ε_{ar}`,
  `|𝒞|² = ∑ χ(a) χ̄(b) ∑_{r ≤ K} ε_{ar} ε_{br}`,   `𝒞² = ∑ χ(ab) ∑_{r ≤ K} (r/p) ε_{ar} ε_{br}`.

The bounds of Lemma 6.2 that follow these identities in the paper are not formalized.
-/

namespace MellinDuality

open Finset

/-- **The gcd decomposition.** `∑_{n, n' ≤ N} F(n, n') = ∑_{(a,b) coprime} ∑_{r ≤ K(a,b)} F(ar, br)`. -/
theorem sum_pairs_gcd {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) := by
  rw [← sum_product' (f := F), sum_sigma']
  symm
  refine sum_nbij' (fun x => (x.1.1 * x.2, x.1.2 * x.2))
    (fun y => ⟨(y.1 / Nat.gcd y.1 y.2, y.2 / Nat.gcd y.1 y.2), Nat.gcd y.1 y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, r⟩ h
    simp only [coprimePairs, pairRange, mem_sigma, mem_filter, mem_product,
      mem_Icc] at h
    obtain ⟨⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, -⟩, hr1, hrK⟩ := h
    have hmax : max a b * (N / max a b) ≤ N := Nat.mul_div_le N (max a b)
    have hra : a * r ≤ max a b * (N / max a b) :=
      Nat.mul_le_mul (le_max_left a b) hrK
    have hrb : b * r ≤ max a b * (N / max a b) :=
      Nat.mul_le_mul (le_max_right a b) hrK
    simp only [mem_product, mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), by omega⟩,
      ⟨Nat.one_le_iff_ne_zero.2 (by positivity), by omega⟩⟩
  · rintro ⟨n, n'⟩ h
    simp only [mem_product, mem_Icc] at h
    obtain ⟨⟨hn1, hnN⟩, hn'1, hn'N⟩ := h
    have hg : 0 < Nat.gcd n n' := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdn : Nat.gcd n n' ∣ n := Nat.gcd_dvd_left n n'
    have hdn' : Nat.gcd n n' ∣ n' := Nat.gcd_dvd_right n n'
    have e1 : n / Nat.gcd n n' * Nat.gcd n n' = n := Nat.div_mul_cancel hdn
    have e2 : n' / Nat.gcd n n' * Nat.gcd n n' = n' := Nat.div_mul_cancel hdn'
    have hq1 : 1 ≤ n / Nat.gcd n n' := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hg
    have hq2 : 1 ≤ n' / Nat.gcd n n' := Nat.div_pos (Nat.le_of_dvd (by omega) hdn') hg
    have hq1N : n / Nat.gcd n n' ≤ N := (Nat.div_le_self _ _).trans hnN
    have hq2N : n' / Nat.gcd n n' ≤ N := (Nat.div_le_self _ _).trans hn'N
    simp only [coprimePairs, pairRange, mem_sigma, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨⟨hq1, hq1N⟩, hq2, hq2N⟩, Nat.coprime_div_gcd_div_gcd hg⟩, hg, ?_⟩
    rw [Nat.le_div_iff_mul_le (lt_of_lt_of_le zero_lt_one (le_max_of_le_left hq1))]
    rcases le_total (n / Nat.gcd n n') (n' / Nat.gcd n n') with h | h
    · rw [max_eq_right h, mul_comm, e2]; exact hn'N
    · rw [max_eq_left h, mul_comm, e1]; exact hnN
  · rintro ⟨⟨a, b⟩, r⟩ h
    simp only [coprimePairs, pairRange, mem_sigma, mem_filter, mem_product,
      mem_Icc] at h
    obtain ⟨⟨⟨⟨ha1, -⟩, hb1, -⟩, hab⟩, hr1, -⟩ := h
    have hgcd : Nat.gcd (a * r) (b * r) = r := by
      rw [Nat.gcd_mul_right, hab, one_mul]
    simp only [hgcd, Nat.mul_div_cancel _ (show 0 < r by omega)]
  · rintro ⟨n, n'⟩ _
    simp only [Nat.div_mul_cancel (Nat.gcd_dvd_left n n'),
      Nat.div_mul_cancel (Nat.gcd_dvd_right n n')]
  · rintro ⟨⟨a, b⟩, r⟩ _; rfl

section Quartic

variable {p : ℕ} [hp : Fact p.Prime]

/-- `𝒞 = ∑_{n ≤ N} χ(n) ε_n`. -/
theorem bandSum_eq_Icc (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) := by
  unfold bandSumPow
  rw [← sum_erase (half p) (a := 0) (by simp [MulChar.map_zero])]
  have hpo := odd_p hp2
  refine sum_nbij' (fun x => x.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_erase, mem_half_iff] at hx
    have := val_pos_of_ne_zero hx.1
    rw [mem_Icc]; obtain ⟨k, hk⟩ := hpo; omega
  · intro n hn
    have hn0 := natCast_ne_zero_of_mem (p := p) hn
    rw [mem_Icc] at hn
    rw [mem_erase, mem_half_iff, ZMod.val_natCast_of_lt (by omega)]
    exact ⟨hn0, by omega⟩
  · intro x _; simp
  · intro n hn
    rw [mem_Icc] at hn
    simp only [ZMod.val_natCast_of_lt (show n < p by omega)]
  · intro x _
    simp [bandSignE, eps]

lemma mem_Icc_of_mem_pairRange {N : ℕ} {ab : ℕ × ℕ} {r : ℕ}
    (hr : r ∈ pairRange N ab) : r ∈ Icc 1 N := by
  simp only [pairRange, mem_Icc] at hr ⊢
  refine ⟨hr.1, hr.2.trans (Nat.div_le_self _ _)⟩

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

lemma char_mul_star {x : ZMod p} (hx : x ≠ 0) : χ x * star (χ x) = 1 := by
  rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide

lemma char_mul_self {r : ℕ} (hr : (r : ZMod p) ≠ 0) :
    χ r * χ r = ((legendreSym p r : ℤ) : GaussianInt) := by
  rw [← sq, ← quadraticChar_eq_sq hχ hr, legendreSym, Int.cast_natCast]

/-- **The pair structure** (Proposition 6.3 of Paper II). For `p ≡ 5 (mod 8)` and a quartic
`χ`, with `N = (p - 1)/2`, `𝒞 = bandSumPow χ 2`, `S = halfSum χ`, the outer sums over coprime
`a, b ≤ N` and the inner sums over `r ≤ ⌊N / max(a, b)⌋`:
`𝒞 S̄ = ∑ χ(a) χ̄(b) ∑ ε_{ar}`, `𝒞 S = ∑ χ(ab) ∑ (r/p) ε_{ar}`,
`𝒞 𝒞̄ = ∑ χ(a) χ̄(b) ∑ ε_{ar} ε_{br}` and `𝒞² = ∑ χ(ab) ∑ (r/p) ε_{ar} ε_{br}`. -/
theorem pair_structure (hp8 : p % 8 = 5) :
    bandSumPow χ 2 * star (halfSum χ) =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ ab.1 * star (χ ab.2) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab, (eps p (ab.1 * r) : GaussianInt) ∧
      bandSumPow χ 2 * halfSum χ =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ (ab.1 * ab.2 : ℕ) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab,
            ((legendreSym p r : ℤ) : GaussianInt) * (eps p (ab.1 * r) : GaussianInt) ∧
      bandSumPow χ 2 * star (bandSumPow χ 2) =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ ab.1 * star (χ ab.2) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab,
            (eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt) ∧
      bandSumPow χ 2 * bandSumPow χ 2 =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ (ab.1 * ab.2 : ℕ) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab, ((legendreSym p r : ℤ) : GaussianInt) *
            ((eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt)) := by
  have hp2 := hp2_of hp8
  have hC := bandSum_eq_Icc hp2 χ
  have hstarC : star (bandSumPow χ 2) =
      ∑ n ∈ Icc 1 ((p - 1) / 2), star (χ (n : ZMod p)) * (eps p n : GaussianInt) := by
    rw [hC, star_sum]
    exact sum_congr rfl fun n _ => by rw [star_mul', star_intCast]
  have hr0 : ∀ ab ∈ coprimePairs ((p - 1) / 2), ∀ r ∈ pairRange ((p - 1) / 2) ab,
      ((r : ℕ) : ZMod p) ≠ 0 :=
    fun ab _ r hr => natCast_ne_zero_of_mem (mem_Icc_of_mem_pairRange hr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hC, halfSum, star_sum, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_star hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul, star_mul']
    linear_combination (χ ab.1 * star (χ ab.2) * (eps p (ab.1 * r) : GaussianInt)) * h1
  · rw [hC, halfSum, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_self hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul]
    linear_combination (χ ab.1 * χ ab.2 * (eps p (ab.1 * r) : GaussianInt)) * h1
  · rw [hstarC, hC, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_star hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul, star_mul']
    linear_combination (χ ab.1 * star (χ ab.2) * (eps p (ab.1 * r) : GaussianInt) *
      (eps p (ab.2 * r) : GaussianInt)) * h1
  · rw [hC, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_self hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul]
    linear_combination (χ ab.1 * χ ab.2 * (eps p (ab.1 * r) : GaussianInt) *
      (eps p (ab.2 * r) : GaussianInt)) * h1

end Quartic

end MellinDuality
