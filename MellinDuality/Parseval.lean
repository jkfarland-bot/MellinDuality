module

public import MellinDuality.Mellin

@[expose] public section

/-!
# Parseval

`parseval` (Proposition 7.1 of Paper II): with `N = (p - 1)/2` and `ε_n = (-1)^{⌊n²/p⌋}`,
`∑_{ψ mod p} |∑_{n ≤ N} ψ(n) ε_n|² = (p - 1) N`. It holds for any weight with `ε_n² = 1`
(`parseval_general`), since distinct `n ≤ N` are distinct modulo `p`.
-/

namespace MellinDuality

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma natCast_ne_zero_of_mem {n : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2)) : (n : ZMod p) ≠ 0 := by
  rw [mem_Icc] at hn
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  have := hp.out.two_le
  omega

lemma natCast_inj_of_mem {n n' : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2))
    (hn' : n' ∈ Icc 1 ((p - 1) / 2)) : (n : ZMod p) = n' ↔ n = n' := by
  rw [mem_Icc] at hn hn'
  constructor
  · intro h
    have h' := congrArg ZMod.val h
    have := hp.out.two_le
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h'
  · rintro rfl; rfl

/-- **Parseval** for any weight `w` with `w(n)² = 1`. -/
theorem parseval_general (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by
  set I := Icc 1 ((p - 1) / 2)
  have hconj : ∀ ψ : DirichletCharacter ℂ p,
      (((‖∑ n ∈ I, ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, (w n * w n' : ℂ) * (ψ n'⁻¹ * ψ n) := by
    intro ψ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
    rw [map_mul, map_intCast]
    have : (starRingEnd ℂ) (ψ n') = ψ n'⁻¹ := by
      rw [← MulChar.inv_apply', ← MulChar.star_apply']; rfl
    rw [this]; ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [hconj]
  rw [sum_comm]
  have horth : ∀ n ∈ I, ∀ n' ∈ I, ∑ ψ : DirichletCharacter ℂ p, ψ (n' : ZMod p)⁻¹ * ψ n =
      if n' = n then (p : ℂ) - 1 else 0 := by
    intro n hn n' hn'
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      (isUnit_iff_ne_zero.2 (natCast_ne_zero_of_mem hn')) (n : ZMod p), totient_cast]
    simp only [natCast_inj_of_mem hn' hn]
  calc ∑ n ∈ I, ∑ ψ : DirichletCharacter ℂ p, ∑ n' ∈ I, (w n * w n' : ℂ) * (ψ n'⁻¹ * ψ n)
      = ∑ n ∈ I, ∑ n' ∈ I, (w n * w n' : ℂ) * (if n' = n then (p : ℂ) - 1 else 0) := by
        refine sum_congr rfl fun n hn => ?_
        rw [sum_comm]
        refine sum_congr rfl fun n' hn' => ?_
        rw [← mul_sum, horth n hn n' hn']
    _ = ∑ n ∈ I, ((p : ℂ) - 1) := by
        refine sum_congr rfl fun n hn => ?_
        simp only [mul_ite, mul_zero, sum_ite_eq', hn, ite_true]
        have := hw n
        have h' : (w n * w n : ℂ) = 1 := by exact_mod_cast this
        rw [h', one_mul]
    _ = (((((p : ℝ) - 1) * ((p - 1) / 2 : ℕ)) : ℝ) : ℂ) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- **Parseval** (Proposition 7.1 of Paper II): with `N = (p - 1)/2` and
`ε_n = (-1)^{⌊n²/p⌋}`, `∑_{ψ mod p} |∑_{n ≤ N} ψ(n) ε_n|² = (p - 1) N`. -/
theorem parseval :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (eps p n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) :=
  parseval_general (eps p) fun n => by
    unfold eps; rw [← pow_add, ← two_mul, pow_mul]; simp

end MellinDuality
