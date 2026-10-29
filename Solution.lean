module

public import MellinDuality

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `MellinDuality/`. The definitions used in the statements come from
`MellinDuality/Basic.lean` (`gi`) and `MellinDuality/Defs.lean`, and are compared with the copies
in `Challenge.lean`.
-/

namespace MellinDuality

open Finset

section Statements

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The half sums** (Paper II, §2). For an odd character `φ`, `𝒢(φ) = 2 ∑_{0<n<p/2} φ(n)(-1)^n` and
`𝒢(φ) = 2 φ(2) ∑_{0<m<p/2} φ(m)`. -/
theorem multiplier_constant_half {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) :
    G φ = 2 * ∑ n ∈ half p, φ n * (parSign n : R) ∧ G φ = 2 * φ 2 * ∑ n ∈ half p, φ n :=
  ⟨G_eq_two_mul_half hp2 φ hφ, G_eq_two_mul_char_two_mul_half hp2 φ hφ⟩

/-- `𝒢(φ) = 0` for an even character `φ` (Paper II, §2). -/
theorem multiplier_constant_even {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) :
    G φ = 0 :=
  G_eq_zero_of_even hp2 φ hφ

/-- **The half-sum identity** (classical input; Paper II, (1)): for odd `ψ`,
`p 𝒢(ψ) = 2 (1 - 2ψ(2)) T(ψ)` with `T(ψ) = ∑ ψ(m) m = p B_{1,ψ}`. -/
theorem half_sum_identity {R : Type*} [CommRing R] (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R) (hψ : ψ (-1) = -1) :
    (p : R) * G ψ = 2 * (1 - 2 * ψ 2) * T ψ :=
  bernoulli_form hp2 ψ hψ

/-- `𝒢(φ) = 2 (1 - 2φ(2)) B_{1,φ}` for an odd complex character (Paper II, (1)). -/
theorem multiplier_constant_bern (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p) (hφ : φ (-1) = -1) :
    G φ = 2 * (1 - 2 * φ 2) * bern φ :=
  G_eq_bern hp2 φ hφ

/-- **Mellin duality** (Theorem 3.1, with the exponent `2m` of Corollary 3.2). For an odd prime `p`, an
odd character `χ` and any character `ψ` with values in a commutative ring,
`2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem mellin_duality {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    (m : ℕ) : 2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) :=
  mellin_forward hp2 χ ψ hχ m

/-- **Mellin duality, inverted** (Theorem 3.1). For an odd complex character `χ` and a unit `a`,
`𝒞_χ^{(2m)}(a) = (1/(2(p-1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem mellin_duality_inverse (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) :=
  mellin_inversion hp2 χ hχ m ha

/-- **Mellin duality in Bernoulli form** (Theorem 3.1): `𝒞_χ(a) = (2/(p-1)) ∑_{ψ odd} ψ(a)
(1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`. -/
theorem mellin_duality_bernoulli (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) :=
  mellin_bernoulli hp2 χ hχ ha

/-- **The quartic case** (Theorem 3.1, last display): if `χ` is odd with `χ(2) = i`,
`𝒞 = (2/(p-1)) ∑_{ψ odd} (1 - 2ψ̄(2)) (1 - 2iψ(2)²) B_{1,ψ̄} B_{1,χψ²}`. -/
theorem mellin_duality_quartic (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) :=
  mellin_quartic hp2 χ hχ hpin

/-- **The parity dictionary** (Paper II, §2; Paper I, Lemma 2.5): `𝒞_χ^{(e)}(1) = ∑_{0<n<p/2} χ(n)(-1)^{⌊n^e/p⌋}`
for `e ≥ 1`. -/
theorem parity_dictionary {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) {e : ℕ} (he : 1 ≤ e) :
    fam χ e 1 = bandSumPow χ e :=
  fam_one_eq_bandSumPow hp2 χ he

/-- **The exponent family** (Corollary 3.2): for `m ≥ 1`,
`𝒞_{2m} = (1/(2(p-1))) ∑_{ψ odd} 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem exponent_family_dual (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) :=
  exponent_family hp2 χ hχ hm

/-- **The collapse** (Corollary 3.2): if `(p - 1) ∣ 2m`, then `2 𝒞_{2m} = -𝒢(χ)`. -/
theorem exponent_collapse_first {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (hm : 1 ≤ m) (hdiv : p - 1 ∣ 2 * m) : 2 * bandSumPow χ (2 * m) = -G χ :=
  exponent_collapse_one hp2 χ hχ hm hdiv

/-- **The collapse** (Corollary 3.2): if `(p - 1) ∣ 4m` and `(p - 1) ∤ 2m`, then
`2 𝒞_{2m} = -𝒢(χ (·/p))`. -/
theorem exponent_collapse_second {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) :=
  exponent_collapse_two hp2 χ hχ h4 h2

/-- **The cosets** (Paper II, §2). At `p ≡ 5 (mod 8)` a quartic `χ` is odd, its fibre over `1` is
the group `H` of nonzero fourth powers, and if `χ(2) = i` its fibre over `i` is `2H`. -/
theorem cosets_as_fibers {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    χ (-1) = -1 ∧ fiber χ 1 = univ.filter (fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x) ∧
      (χ 2 = gi → fiber χ gi = (fiber χ 1).image (2 * ·)) :=
  ⟨quartic_odd hp8 hχ, fiber_one_eq hχ, fun hpin => fiber_gi_eq hp8 hpin⟩

/-- **Lemma 2.1.** `Re 𝒞(a) = ∑_{u ∈ H} s(u) s(au²)` and `Im 𝒞(a) = ∑_{u ∈ F_i} s(u) s(au²)`, where
`F_i` is the fibre of `χ` over `i` (which is `2H` when `χ(2) = i`). -/
theorem coset_decomposition {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) :=
  coset_lemma hp8 hχ a

/-- `𝒢(χ) = 2γ` with `γ = A + iB`, and `p γ = (1 - 2i) T(χ)` when `χ(2) = i`, i.e. `γ = (1 - 2i)β`. -/
theorem gamma_identities {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    G χ = 2 * gamma χ ∧ (χ 2 = gi → (p : GaussianInt) * gamma χ = (1 - 2 * gi) * T χ) :=
  ⟨G_eq_two_gamma hp8 hχ, gamma_bernoulli hp8 hχ⟩

/-- **The terminal values** (Corollary 3.2, quartic case): if `(p - 1) ∣ 4m` then `𝒞_{2m} = -γ`
when `(p - 1) ∣ 2m` and `𝒞_{2m} = -γ̄` otherwise. -/
theorem exponent_terminal_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) :=
  quartic_terminal hp8 hχ hm h4

/-- **The coset trace** (Corollary 3.3): for `c ∈ {1, i, -1, -i}`,
`∑_{χ(a) = c} 𝒞(a) = Re(c̄ γ) γ̄`. -/
theorem coset_trace_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) :=
  coset_trace hp8 hχ hc

/-- **The coset trace, second form** (Corollary 3.3): `2 ∑_{χ(a) = c} 𝒞(a) = c̄ |γ|² + c γ̄²`. -/
theorem coset_trace_second {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 :=
  coset_trace_second_form hp8 hχ hc

/-- **The family means** (Corollary 3.3): `∑_{a ∈ H} Re 𝒞(a) = A²`, `∑_{a ∈ H} Im 𝒞(a) = -AB`. -/
theorem family_mean_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    (∑ a ∈ fiber χ 1, fam χ 2 a).re = sigma χ 1 ^ 2 ∧
      (∑ a ∈ fiber χ 1, fam χ 2 a).im = -(sigma χ 1 * sigma χ gi) :=
  family_means hp8 hχ

/-- **Conjugate dynamics** (Proposition 4.1): for `a ∈ H`, `Re 𝒞(a) = ∑_{v ∈ H} s(a⁻¹v) s(a⁻¹v²)`. -/
theorem conjugate_dynamics_squaring {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {a : ZMod p} (ha : a ∈ fiber χ 1) :
    (fam χ 2 a).re = ∑ v ∈ fiber χ 1, parSign (a⁻¹ * v) * parSign (a⁻¹ * v ^ 2) :=
  conjugate_dynamics hp8 hχ ha

/-- **Second moments over the family** (Proposition 4.2):
`∑_{a ∈ H} (Re 𝒞(a))² = ∑_{d ∈ H} M(d) M(d²)` and `∑_{a ∈ H} (Im 𝒞(a))² = ∑_{d ∈ H} M_{F_i}(d) M(d²)`,
with `F_i` the fibre over `i` (`2H` when `χ(2) = i`). -/
theorem second_moments {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) ∧
      ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) :=
  ⟨second_moment_re hp8 hχ, second_moment_im hp8 hχ⟩

/-- **The gcd decomposition** (proof of Proposition 6.3): every `(n, n') ∈ [1, N]²` is `(ar, br)` for
one coprime `(a, b)` and one `r ≤ ⌊N / max(a, b)⌋`. -/
theorem gcd_decomposition {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) :=
  sum_pairs_gcd N F

/-- `𝒞 = ∑_{n ≤ (p-1)/2} χ(n) ε_n` with `ε_n = (-1)^{⌊n²/p⌋}`. -/
theorem band_sum_interval (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) :=
  bandSum_eq_Icc hp2 χ

/-- **The pair structure** (Proposition 6.3): `𝒞 S̄`, `𝒞 S`, `|𝒞|²` and `𝒞²` as sums over coprime
pairs `(a, b)` of inner sums over `r ≤ ⌊N / max(a, b)⌋`. -/
theorem pair_structure_identities {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) (hp8 : p % 8 = 5) :
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
            ((eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt)) :=
  pair_structure hχ hp8

/-- **Parseval** (Proposition 7.1): `∑_{ψ mod p} |∑_{n ≤ N} ψ(n) ε_n|² = (p - 1) N`, `N = (p-1)/2`. -/
theorem parseval_identity :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (eps p n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) :=
  parseval

/-- Parseval for any weight `w` with `w(n)² = 1`. -/
theorem parseval_any_weight (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) :=
  parseval_general w hw

end Statements

end MellinDuality
