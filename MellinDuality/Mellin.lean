module

public import MellinDuality.Half

@[expose] public section

/-!
# Mellin duality

For an odd prime `p`, an odd character `χ` modulo `p` and `m ≥ 0`, the multiplier family
`𝒞_χ^{(2m)}(a) = ∑_{0 < n < p/2} χ(n) (-1)^{n + ⟨a n^{2m}⟩}` satisfies, for every character `ψ`,

  `2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χ ψ^{2m})`   (`mellin_forward`, any commutative ring),

and, inverting over the complex characters,

  `𝒞_χ^{(2m)}(a) = (1 / (2(p - 1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χ ψ^{2m})`   (`mellin_inversion`).

The case `m = 1` is Theorem 3.1 of Paper II; `mellin_bernoulli` is its form in first Bernoulli
numbers, and `exponent_family`, `exponent_collapse_one` and `exponent_collapse_two` are
Corollary 3.2. `fam_one_eq_bandSumPow` is the parity dictionary `𝒞_χ^{(e)}(1) = 𝒞_e`.
-/

namespace MellinDuality

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

section Ring

variable {R : Type*} [CommRing R]

lemma pow_apply_of_ne_zero (ψ : MulChar (ZMod p) R) (k : ℕ) {x : ZMod p} (hx : x ≠ 0) :
    (ψ ^ k) x = ψ x ^ k := by
  simpa using MulChar.pow_apply_coe ψ k (Units.mk0 x hx)

lemma apply_neg_one_sq (ψ : MulChar (ZMod p) R) : ψ (-1) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

/-- `ψ^{2m}` is even. -/
lemma pow_two_mul_apply_neg_one (ψ : MulChar (ZMod p) R) (m : ℕ) : (ψ ^ (2 * m)) (-1) = 1 := by
  rw [pow_apply_of_ne_zero ψ _ (neg_ne_zero.2 one_ne_zero), pow_mul, apply_neg_one_sq, one_pow]

/-- `χ ψ^{2m}` is odd when `χ` is. -/
lemma mul_pow_two_mul_odd (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) (m : ℕ) :
    (χ * ψ ^ (2 * m)) (-1) = -1 := by
  rw [MulChar.mul_apply, hχ, pow_two_mul_apply_neg_one, mul_one]

lemma inv_apply_neg_one (ψ : MulChar (ZMod p) R) : ψ⁻¹ (-1) = ψ (-1) := by
  rw [MulChar.inv_apply', inv_neg, inv_one]

/-- The family as a product of parity signs. -/
lemma fam_eq (χ : MulChar (ZMod p) R) (e : ℕ) (a : ZMod p) :
    fam χ e a = ∑ n ∈ half p, χ n * (parSign n : R) * (parSign (a * n ^ e) : R) := by
  unfold fam parSign
  refine sum_congr rfl fun n _ => ?_
  rw [pow_add]; push_cast; ring

/-- The substitution `b = a c`: `∑_a ψ̄(a) s(a c) = ψ(c) 𝒢(ψ̄)` for `c ≠ 0`. -/
lemma sum_inv_mul_parSign (ψ : MulChar (ZMod p) R) {c : ZMod p} (hc : c ≠ 0) :
    ∑ a, ψ⁻¹ a * (parSign (a * c) : R) = ψ c * G ψ⁻¹ := by
  unfold G
  rw [mul_sum]
  refine Fintype.sum_bijective (· * c) (Equiv.mulRight₀ c hc).bijective _ _ fun a => ?_
  have hcc : ψ c * ψ⁻¹ c = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hc, map_one]
  simp only [map_mul]
  linear_combination (-(ψ⁻¹ a * (parSign (a * c) : R))) * hcc

/-- **Mellin duality** (Theorem 3.1 of Paper II, forward form, for the exponent `2m`). For an odd
prime `p`, an odd character `χ` and any character `ψ` with values in a commutative ring,
`2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem mellin_forward (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) (m : ℕ) :
    2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  have step : ∑ a, ψ⁻¹ a * fam χ (2 * m) a =
      G ψ⁻¹ * ∑ n ∈ half p, (χ * ψ ^ (2 * m)) n * (parSign n : R) := by
    simp_rw [fam_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · subst hn; simp [MulChar.map_zero]
    · calc ∑ a, ψ⁻¹ a * (χ n * (parSign n : R) * (parSign (a * n ^ (2 * m)) : R))
          = χ n * (parSign n : R) * ∑ a, ψ⁻¹ a * (parSign (a * n ^ (2 * m)) : R) := by
            rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
        _ = χ n * (parSign n : R) * (ψ (n ^ (2 * m)) * G ψ⁻¹) := by
            rw [sum_inv_mul_parSign ψ (pow_ne_zero _ hn)]
        _ = G ψ⁻¹ * ((χ * ψ ^ (2 * m)) n * (parSign n : R)) := by
            rw [MulChar.mul_apply, pow_apply_of_ne_zero _ _ hn, map_pow]; ring
  rw [step, G_eq_two_mul_half hp2 _ (mul_pow_two_mul_odd χ ψ hχ m)]
  ring

/-- **The parity dictionary**: `𝒞_χ^{(e)}(1) = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋}` for `e ≥ 1`. -/
theorem fam_one_eq_bandSumPow (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) {e : ℕ} (he : 1 ≤ e) :
    fam χ e 1 = bandSumPow χ e := by
  unfold fam bandSumPow bandSignE
  refine sum_congr rfl fun n _ => ?_
  congr 2
  rw [one_mul]
  have hval : (n ^ e).val = n.val ^ e % p := by
    rw [show (n ^ e : ZMod p) = ((n.val ^ e : ℕ) : ZMod p) by
      push_cast; rw [ZMod.natCast_zmod_val], ZMod.val_natCast]
  rw [hval]
  have hpo := odd_p hp2
  set v := n.val
  have hdec := Nat.div_add_mod (v ^ e) p
  have hpar : v ^ e % 2 = v % 2 := by
    rcases Nat.even_or_odd v with h | h
    · rw [Nat.even_iff.1 h, Nat.even_iff.1 (h.pow_of_ne_zero (by omega))]
    · rw [Nat.odd_iff.1 h, Nat.odd_iff.1 (h.pow)]
  have hpq : (p * (v ^ e / p)) % 2 = (v ^ e / p) % 2 := by
    rw [Nat.mul_mod, Nat.odd_iff.1 hpo, one_mul, Nat.mod_mod]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := v ^ e / p)]
  congr 1
  omega

/-- **The exponent family collapses** (Corollary 3.2, first case): if `(p - 1) ∣ 2m` then
`2 𝒞_{2m} = -𝒢(χ)`. -/
theorem exponent_collapse_one (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) (hdiv : p - 1 ∣ 2 * m) : 2 * bandSumPow χ (2 * m) = -G χ := by
  rw [← fam_one_eq_bandSumPow hp2 χ (by omega), fam_eq, G_eq_two_mul_half hp2 χ hχ, ← neg_mul,
    mul_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · obtain ⟨j, hj⟩ := hdiv
    have h1 : (1 : ZMod p) * n ^ (2 * m) = 1 := by
      rw [one_mul, hj, pow_mul, ZMod.pow_card_sub_one_eq_one hn, one_pow]
    have hs : parSign (1 : ZMod p) = -1 := by
      unfold parSign; rw [ZMod.val_one]; norm_num
    rw [h1, hs]; push_cast; ring

lemma quad_cast_eq_pow (hp2 : p ≠ 2) (n : ZMod p) :
    ((quadraticChar (ZMod p) n : ℤ) : ZMod p) = n ^ (p / 2) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  simpa [ZMod.card] using quadraticChar_eq_pow_of_char_ne_two' hF n

/-- **The exponent family collapses** (Corollary 3.2, second case): if `(p - 1) ∣ 4m` but
`(p - 1) ∤ 2m`, then `2 𝒞_{2m} = -𝒢(χ · (·/p))`. (For the quartic character `χ (·/p) = χ̄`.) -/
theorem exponent_collapse_two (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) {m : ℕ}
    (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) := by
  have hpo := odd_p hp2
  have hp3 : 3 ≤ p := by have := hp.out.two_le; obtain ⟨k, hk⟩ := hpo; omega
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at h2
    · exact h
  -- `2m = (p/2) j` with `j` odd, and `p/2` even
  have hh : p - 1 = 2 * (p / 2) := by obtain ⟨k, hk⟩ := hpo; omega
  obtain ⟨j, hj⟩ : p / 2 ∣ 2 * m := by
    rw [hh] at h4; obtain ⟨c, hc⟩ := h4; exact ⟨c, by linarith⟩
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | h
    · exact absurd ⟨i, by rw [hh, hj]; ring⟩ h2
    · exact h
  have hheven : Even (p / 2) := by
    rcases Nat.even_or_odd (p / 2) with h | ⟨k, hk⟩
    · exact h
    · exfalso
      have hcop : Nat.Coprime (p / 2) 2 := by rw [hk]; simp [Nat.coprime_two_right]
      have : p / 2 ∣ m := hcop.dvd_of_dvd_mul_left ⟨j, by linarith⟩
      obtain ⟨c, hc⟩ := this
      exact h2 ⟨c, by rw [hh, hc]; ring⟩
  have hquad_odd : (χ * quadR p R) (-1) = -1 := by
    have hq : quadraticChar (ZMod p) (-1) = 1 := by
      have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
      rw [quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.2 one_ne_zero), ZMod.card,
        hheven.neg_one_pow]
      simp
    simp [quadR, MulChar.mul_apply, MulChar.ringHomComp_apply, hχ, hq]
  rw [← fam_one_eq_bandSumPow hp2 χ (by omega), fam_eq,
    G_eq_two_mul_half hp2 _ hquad_odd, ← neg_mul, mul_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · have hq := quadraticChar_dichotomy (F := ZMod p) hn
    have hpow : (1 : ZMod p) * n ^ (2 * m) = ((quadraticChar (ZMod p) n : ℤ) : ZMod p) := by
      rw [one_mul, hj, pow_mul, ← quad_cast_eq_pow hp2]
      rcases hq with h | h <;> rw [h]
      · simp
      · push_cast; exact hjodd.neg_one_pow
    have hs : (parSign (((quadraticChar (ZMod p) n : ℤ) : ZMod p)) : ℤ) =
        -quadraticChar (ZMod p) n := by
      unfold parSign
      rcases hq with h | h <;> rw [h]
      · simp [ZMod.val_one]
      · rw [Int.cast_neg, Int.cast_one, val_neg_of_ne_zero' one_ne_zero, ZMod.val_one]
        have : Even (p - 1) := by rw [hh]; exact even_two_mul _
        rw [this.neg_one_pow]; norm_num
    rw [hpow, hs]
    simp only [quadR, MulChar.mul_apply, MulChar.ringHomComp_apply, eq_intCast]
    push_cast; ring

end Ring

section Complex

lemma totient_cast : ((Nat.totient p : ℕ) : ℂ) = (p : ℂ) - 1 := by
  rw [Nat.totient_prime hp.out, Nat.cast_sub hp.out.one_le, Nat.cast_one]

lemma p_sub_one_ne_zero : (p : ℂ) - 1 ≠ 0 := by
  rw [← totient_cast]; exact_mod_cast (Nat.totient_pos.2 hp.out.pos).ne'

/-- Only odd characters contribute: for even `ψ`, `𝒢(ψ̄) = 0`. -/
lemma sum_oddChars_eq_sum (F : DirichletCharacter ℂ p → ℂ)
    (hF : ∀ ψ : DirichletCharacter ℂ p, ψ (-1) = 1 → F ψ = 0) :
    ∑ ψ ∈ oddChars p, F ψ = ∑ ψ, F ψ := by
  unfold oddChars
  refine sum_filter_of_ne fun ψ _ hψ => ?_
  have h : ψ (-1) * ψ (-1) = 1 := by rw [← sq]; exact apply_neg_one_sq ψ
  rcases mul_self_eq_one_iff.1 h with h | h
  · exact absurd (hF ψ h) hψ
  · exact h

/-- **Mellin duality, inverted** (Theorem 3.1 of Paper II, for the exponent `2m`). For an odd
prime `p`, an odd complex character `χ` and a unit `a`,
`𝒞_χ^{(2m)}(a) = (1/(2(p - 1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem mellin_inversion (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  rw [sum_oddChars_eq_sum _ (fun ψ hψ => by
    rw [G_eq_zero_of_even hp2 ψ⁻¹ (by rw [inv_apply_neg_one, hψ])]; ring)]
  have key : ∑ ψ : DirichletCharacter ℂ p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) =
      2 * ((p : ℂ) - 1) * fam χ (2 * m) a := by
    calc ∑ ψ : DirichletCharacter ℂ p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m))
        = ∑ ψ : DirichletCharacter ℂ p, ∑ b, 2 * fam χ (2 * m) b * (ψ a * ψ⁻¹ b) := by
          refine sum_congr rfl fun ψ _ => ?_
          rw [mul_assoc, ← mellin_forward hp2 χ ψ hχ m, mul_sum, mul_sum]
          exact sum_congr rfl fun b _ => by ring
      _ = ∑ b, 2 * fam χ (2 * m) b * ∑ ψ : DirichletCharacter ℂ p, ψ a * ψ⁻¹ b := by
          rw [sum_comm]; simp_rw [mul_sum]
      _ = ∑ b, 2 * fam χ (2 * m) b * (if b = a then (p : ℂ) - 1 else 0) := by
          refine sum_congr rfl fun b _ => ?_
          congr 1
          by_cases hb : b = 0
          · subst hb
            simp [MulChar.map_zero, Ne.symm ha]
          · have h' : ∀ ψ : DirichletCharacter ℂ p, ψ a * ψ⁻¹ b = ψ b⁻¹ * ψ a := fun ψ => by
              rw [MulChar.inv_apply', mul_comm]
            rw [sum_congr rfl fun ψ _ => h' ψ,
              DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_iff_ne_zero.2 hb) a,
              totient_cast]
      _ = 2 * ((p : ℂ) - 1) * fam χ (2 * m) a := by
          simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]; ring
  rw [key]
  field_simp [p_sub_one_ne_zero]

/-- `𝒢(φ) = 2 (1 - 2φ(2)) B_{1,φ}` for an odd complex character (Paper II, (1)). -/
theorem G_eq_bern (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p) (hφ : φ (-1) = -1) :
    G φ = 2 * (1 - 2 * φ 2) * bern φ := by
  have h := bernoulli_form hp2 φ hφ
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold bern
  field_simp
  linear_combination h

/-- **Mellin duality in Bernoulli form** (Theorem 3.1 of Paper II): for an odd complex character
`χ` and a unit `a`,
`𝒞_χ(a) = (2/(p-1)) ∑_{ψ odd} ψ(a) (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`. -/
theorem mellin_bernoulli (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by
  have h := mellin_inversion hp2 χ hχ 1 ha
  rw [mul_one] at h
  rw [h, mul_sum, mul_sum]
  refine sum_congr rfl fun ψ hψ => ?_
  have hψo : ψ (-1) = -1 := (mem_filter.1 hψ).2
  rw [G_eq_bern hp2 ψ⁻¹ (by rw [inv_apply_neg_one, hψo]),
    G_eq_bern hp2 (χ * ψ ^ 2) (by simpa using mul_pow_two_mul_odd χ ψ hχ 1),
    MulChar.mul_apply, pow_apply_of_ne_zero ψ 2 (two_ne_zero_zmod hp2)]
  field_simp [p_sub_one_ne_zero]

/-- **The quartic case** (Theorem 3.1 of Paper II, last display): for an odd complex character
with `χ(2) = i` (the quartic character at `p ≡ 5 (mod 8)`),
`𝒞 = (2/(p-1)) ∑_{ψ odd} (1 - 2ψ̄(2)) (1 - 2iψ(2)²) B_{1,ψ̄} B_{1,χψ²}`. -/
theorem mellin_quartic (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by
  rw [← fam_one_eq_bandSumPow hp2 χ (by norm_num), mellin_bernoulli hp2 χ hχ one_ne_zero, hpin]
  simp only [map_one, one_mul]

/-- **The exponent family** (Corollary 3.2 of Paper II): for `m ≥ 1`,
`𝒞_{2m} = (1/(2(p-1))) ∑_{ψ odd} 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem exponent_family (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  rw [← fam_one_eq_bandSumPow hp2 χ (by omega), mellin_inversion hp2 χ hχ m one_ne_zero]
  simp only [map_one, one_mul]

end Complex

end MellinDuality
