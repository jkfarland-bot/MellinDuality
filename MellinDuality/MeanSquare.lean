module

public import MellinDuality.Pairs

@[expose] public section

/-!
# The Bernoulli mean square

Parseval over the odd characters (`parseval_odd`): with `N = (p - 1)/2` and any weight `w` with
`w(n)² = 1`, `∑_{χ odd} |∑_{n ≤ N} χ(n) w(n)|² = ((p - 1)/2) N`, because `n ≢ -n'` for
`n, n' ≤ N`.

Through Mellin duality (`mellin_bernoulli`) every member of the multiplier family is such a sum:
`𝒞_χ(a) = ∑_{n ≤ N} χ(n) (-1)^{n + ⟨a n²⟩}` (`fam_eq_Icc`). Hence (`bernoulli_mean_square`), for
`a ≠ 0`, the bilinear Bernoulli form
`X_χ(a) = ∑_{ψ odd} ψ(a) (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`
has the exact second moment `∑_{χ odd} |X_χ(a)|² = ((p - 1)/2)⁴`.
-/

namespace MellinDuality

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma natCast_add_ne_zero_of_mem {n n' : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2))
    (hn' : n' ∈ Icc 1 ((p - 1) / 2)) : (n' : ZMod p) ≠ -(n : ZMod p) := by
  rw [mem_Icc] at hn hn'
  intro h
  have h' : ((n' + n : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by omega) h'
  omega

lemma char_neg_one_sq (ψ : DirichletCharacter ℂ p) : ψ (-1) * ψ (-1) = 1 := by
  rw [← map_mul]; simp

/-- The twisted Parseval sum vanishes: `∑_ψ ψ(-1) |∑_{n ≤ N} ψ(n) w(n)|² = 0`. -/
lemma parseval_twisted (w : ℕ → ℤ) :
    ∑ ψ : DirichletCharacter ℂ p,
        ψ (-1) * (((‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) = 0 := by
  set I := Icc 1 ((p - 1) / 2)
  have hconj : ∀ ψ : DirichletCharacter ℂ p,
      ψ (-1) * (((‖∑ n ∈ I, ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, (w n * w n' : ℂ) * (ψ n'⁻¹ * ψ (-(n : ZMod p))) := by
    intro ψ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n' _ => ?_
    rw [map_mul, map_intCast]
    have : (starRingEnd ℂ) (ψ n') = ψ n'⁻¹ := by
      rw [← MulChar.inv_apply', ← MulChar.star_apply']; rfl
    rw [this, show -(n : ZMod p) = -1 * n by ring, map_mul]; ring
  simp_rw [hconj]
  rw [sum_comm]
  refine sum_eq_zero fun n hn => ?_
  rw [sum_comm]
  refine sum_eq_zero fun n' hn' => ?_
  rw [← mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
    (isUnit_iff_ne_zero.2 (natCast_ne_zero_of_mem hn')) (-(n : ZMod p)),
    ite_eq_right (natCast_add_ne_zero_of_mem hn hn'), mul_zero]

/-- **Parseval over the odd characters**: for any weight `w` with `w(n)² = 1`,
`∑_{χ odd} |∑_{n ≤ N} χ(n) w(n)|² = ((p - 1)/2) N`. -/
theorem parseval_odd (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ ∈ oddChars p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) / 2 * ((p - 1) / 2 : ℕ) := by
  have hall := parseval_general (p := p) w hw
  have htw := parseval_twisted (p := p) w
  have hsplit : ∀ (ψ : DirichletCharacter ℂ p) (x : ℝ),
      ((if ψ (-1) = -1 then x else 0 : ℝ) : ℂ) = ((x : ℂ) - ψ (-1) * (x : ℂ)) / 2 := by
    intro ψ x
    rcases mul_self_eq_one_iff.1 (char_neg_one_sq ψ) with h | h
    · rw [ite_eq_right (by rw [h]; norm_num), h]; push_cast; ring
    · rw [ite_eq_left h, h]; ring
  apply Complex.ofReal_injective
  rw [oddChars, sum_filter, Complex.ofReal_sum]
  simp_rw [hsplit]
  rw [← sum_div, sum_sub_distrib, htw, sub_zero, ← Complex.ofReal_sum, hall]
  push_cast; ring

/-- Every member of the multiplier family is a half-interval sum with a `±1` weight:
`𝒞_χ(a) = ∑_{n ≤ N} χ(n) (-1)^{n + ⟨a n²⟩}`. -/
theorem fam_eq_Icc (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (a : ZMod p) :
    fam χ 2 a = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) *
      (((-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val) : ℤ) : R) := by
  unfold fam
  rw [← sum_erase (half p) (a := 0) (by simp [MulChar.map_zero])]
  have hpo := odd_p hp2
  refine sum_nbij' (fun x => x.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_erase, mem_half_iff] at hx
    have := ZMod.val_pos.2 hx.1
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
    simp

/-- **The Bernoulli mean square.** For an odd prime `p` and `a ≠ 0`,
`∑_{χ odd} |∑_{ψ odd} ψ(a) (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}|² = ((p - 1)/2)⁴`. -/
theorem bernoulli_mean_square (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ∑ χ ∈ oddChars p, ‖∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
        (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2)‖ ^ 2 =
      (((p : ℝ) - 1) / 2) ^ 4 := by
  set w : ℕ → ℤ := fun n => (-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val)
  have hw : ∀ n, w n * w n = 1 := fun n => by
    simp only [w]; rw [← pow_add, ← two_mul, pow_mul]; simp
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hp.out.one_lt.ne'
  have hX : ∀ χ ∈ oddChars p,
      ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) * (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ *
          bern (χ * ψ ^ 2) =
        ((p : ℂ) - 1) / 2 * ∑ n ∈ Icc 1 ((p - 1) / 2), χ n * (w n : ℂ) := by
    intro χ hχ
    have hodd : χ (-1) = -1 := (mem_filter.1 hχ).2
    have h := mellin_bernoulli hp2 χ hodd ha
    rw [fam_eq_Icc hp2 χ a] at h
    rw [h]; field_simp
  have hN : (((p - 1) / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
    obtain ⟨k, hk⟩ := odd_p hp2
    subst hk
    rw [show (2 * k + 1 - 1) / 2 = k by omega]; push_cast; ring
  calc ∑ χ ∈ oddChars p, ‖∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
          (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2)‖ ^ 2
      = ∑ χ ∈ oddChars p, (((p : ℝ) - 1) / 2) ^ 2 *
          ‖∑ n ∈ Icc 1 ((p - 1) / 2), χ n * (w n : ℂ)‖ ^ 2 := by
        refine sum_congr rfl fun χ hχ => ?_
        rw [hX χ hχ, norm_mul, mul_pow]
        congr 2
        rw [norm_div, Complex.norm_ofNat]
        congr 1
        have : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        have := hp.out.one_lt
        have : (1 : ℝ) < p := by exact_mod_cast this
        linarith
    _ = (((p : ℝ) - 1) / 2) ^ 4 := by
        rw [← mul_sum, parseval_odd w hw, hN]; ring

end MellinDuality
