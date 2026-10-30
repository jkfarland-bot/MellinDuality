module

public import Mathlib

public section

/-!
# Mellin duality: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `MellinDuality/`. The numbering follows the paper (Farland, *What the band-parity companion is:
Mellin duality, Weil sums, and the Gauss-sum axis*, Paper II).

Throughout `p` is a prime, `x.val` the least nonnegative residue of `x : ZMod p`, `gi = i`,
`s(x) = (-1)^⟨x⟩`, and `𝒞_χ^{(e)}(a) = ∑_{0 < n < p/2} χ(n) (-1)^{n + ⟨a n^e⟩}`.
-/

namespace MellinDuality

open Finset

/-! ### Definitions -/

/-- The Gaussian unit `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

section Defs

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The parity sign `s(x) = (-1)^⟨x⟩` of the least nonnegative residue. -/
def parSign (x : ZMod p) : ℤ := (-1) ^ x.val

/-- The half system `{n : 0 ≤ n < p/2}` (the term `n = 0` vanishes against every character). -/
def half (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := univ.filter fun n => 2 * n.val < p

variable {R : Type*} [CommRing R]

/-- **The multiplier family** `𝒞_χ^{(e)}(a) = ∑_{0 < n < p/2} χ(n) (-1)^{n + ⟨a n^e⟩}`. -/
def fam (χ : MulChar (ZMod p) R) (e : ℕ) (a : ZMod p) : R :=
  ∑ n ∈ half p, χ n * (((-1 : ℤ) ^ (n.val + (a * n ^ e).val) : ℤ) : R)

/-- **The multiplier constant** `𝒢(ψ) = ∑_{m=1}^{p-1} ψ(m) (-1)^m`. -/
def G (ψ : MulChar (ZMod p) R) : R := ∑ x : ZMod p, ψ x * (parSign x : R)

/-- `T(ψ) = ∑_{m=1}^{p-1} ψ(m) m = p B_{1,ψ}`. -/
def T (ψ : MulChar (ZMod p) R) : R := ∑ x : ZMod p, ψ x * (x.val : R)

/-- The first Bernoulli number `B_{1,ψ} = (1/p) ∑_{m=1}^{p-1} ψ(m) m` of a complex character. -/
noncomputable def bern (ψ : MulChar (ZMod p) ℂ) : ℂ := T ψ / p

/-- The band sign `(-1)^{⌊⟨x⟩^e/p⌋}`. -/
def bandSignE (e : ℕ) (x : ZMod p) : ℤ := (-1) ^ (x.val ^ e / p)

/-- `𝒞_e = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋}`; `𝒞_2 = 𝒞` is the band-parity companion. -/
def bandSumPow (χ : MulChar (ZMod p) R) (e : ℕ) : R :=
  ∑ n ∈ half p, χ n * (bandSignE e n : R)

/-- The odd characters modulo `p` with values in `ℂ`. -/
noncomputable def oddChars (p : ℕ) [Fact p.Prime] : Finset (DirichletCharacter ℂ p) :=
  univ.filter fun ψ => ψ (-1) = -1

/-- The fibre `{x : χ(x) = z}`; for the quartic character pinned by `χ(2) = i` at
`p ≡ 5 (mod 8)` the fibres of `1, i, -1, -i` are the cosets `H, 2H, -H, -2H` of the group `H` of
nonzero fourth powers. -/
def fiber (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter fun x => χ x = z

/-- `σ(z) = ∑_{χ(x) = z} s(x)`; `A = σ(1)` is the sum of `s` over `H`, and `B = σ(i)` the sum over
the fibre of `i` (which is `2H` when `χ(2) = i`). -/
def sigma (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ :=
  ∑ x ∈ fiber χ z, parSign x

/-- `γ = A + i B` with `A = σ(1)`, `B = σ(i)`, so that `𝒢(χ) = 2γ`. -/
def gamma (χ : MulChar (ZMod p) GaussianInt) : GaussianInt := ⟨sigma χ 1, sigma χ gi⟩

/-- The multiplier correlation `M_X(d) = ∑_{u ∈ X} s(u) s(d u)`. -/
def multCorr (X : Finset (ZMod p)) (d : ZMod p) : ℤ := ∑ u ∈ X, parSign u * parSign (d * u)

/-- `ε_n = (-1)^{⌊n²/p⌋}` for a natural number `n`. -/
def eps (p n : ℕ) : ℤ := (-1) ^ (n ^ 2 / p)

/-- The quadratic character `(·/p)` with values in `R`. -/
noncomputable def quadR (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] : MulChar (ZMod p) R :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R)

/-- `S = ∑_{0 < n ≤ (p - 1)/2} χ(n)`. -/
def halfSum (χ : MulChar (ZMod p) R) : R := ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p)

/-- The coprime pairs `(a, b)` in `[1, N]²`. -/
def coprimePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N).filter fun ab => Nat.Coprime ab.1 ab.2

/-- The range `1 ≤ r ≤ ⌊N / max(a, b)⌋`. -/
def pairRange (N : ℕ) (ab : ℕ × ℕ) : Finset ℕ := Icc 1 (N / max ab.1 ab.2)

end Defs

/-! ### Statements -/

section Statements

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The half sums** (Paper II, §2). For an odd character `φ`, `𝒢(φ) = 2 ∑_{0<n<p/2} φ(n)(-1)^n` and
`𝒢(φ) = 2 φ(2) ∑_{0<m<p/2} φ(m)`. -/
theorem multiplier_constant_half {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) :
    G φ = 2 * ∑ n ∈ half p, φ n * (parSign n : R) ∧ G φ = 2 * φ 2 * ∑ n ∈ half p, φ n := by
  sorry

/-- `𝒢(φ) = 0` for an even character `φ` (Paper II, §2). -/
theorem multiplier_constant_even {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) :
    G φ = 0 := by
  sorry

/-- **The half-sum identity** (classical input; Paper II, (1)): for odd `ψ`,
`p 𝒢(ψ) = 2 (1 - 2ψ(2)) T(ψ)` with `T(ψ) = ∑ ψ(m) m = p B_{1,ψ}`. -/
theorem half_sum_identity {R : Type*} [CommRing R] (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R) (hψ : ψ (-1) = -1) :
    (p : R) * G ψ = 2 * (1 - 2 * ψ 2) * T ψ := by
  sorry

/-- `𝒢(φ) = 2 (1 - 2φ(2)) B_{1,φ}` for an odd complex character (Paper II, (1)). -/
theorem multiplier_constant_bern (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p) (hφ : φ (-1) = -1) :
    G φ = 2 * (1 - 2 * φ 2) * bern φ := by
  sorry

/-- **Mellin duality** (Theorem 3.1, with the exponent `2m` of Corollary 3.2). For an odd prime `p`, an
odd character `χ` and any character `ψ` with values in a commutative ring,
`2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem mellin_duality {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    (m : ℕ) : 2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  sorry

/-- **Mellin duality, inverted** (Theorem 3.1). For an odd complex character `χ` and a unit `a`,
`𝒞_χ^{(2m)}(a) = (1/(2(p-1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem mellin_duality_inverse (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  sorry

/-- **Mellin duality in Bernoulli form** (Theorem 3.1): `𝒞_χ(a) = (2/(p-1)) ∑_{ψ odd} ψ(a)
(1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`. -/
theorem mellin_duality_bernoulli (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by
  sorry

/-- **The quartic case** (Theorem 3.1, last display): if `χ` is odd with `χ(2) = i`,
`𝒞 = (2/(p-1)) ∑_{ψ odd} (1 - 2ψ̄(2)) (1 - 2iψ(2)²) B_{1,ψ̄} B_{1,χψ²}`. -/
theorem mellin_duality_quartic (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by
  sorry

/-- **The parity dictionary** (Paper II, §2; Paper I, Lemma 2.5): `𝒞_χ^{(e)}(1) = ∑_{0<n<p/2} χ(n)(-1)^{⌊n^e/p⌋}`
for `e ≥ 1`. -/
theorem parity_dictionary {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) {e : ℕ} (he : 1 ≤ e) :
    fam χ e 1 = bandSumPow χ e := by
  sorry

/-- **The exponent family** (Corollary 3.2): for `m ≥ 1`,
`𝒞_{2m} = (1/(2(p-1))) ∑_{ψ odd} 𝒢(ψ̄) 𝒢(χ ψ^{2m})`. -/
theorem exponent_family_dual (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  sorry

/-- **The collapse** (Corollary 3.2): if `(p - 1) ∣ 2m`, then `2 𝒞_{2m} = -𝒢(χ)`. -/
theorem exponent_collapse_first {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (hm : 1 ≤ m) (hdiv : p - 1 ∣ 2 * m) : 2 * bandSumPow χ (2 * m) = -G χ := by
  sorry

/-- **The collapse** (Corollary 3.2): if `(p - 1) ∣ 4m` and `(p - 1) ∤ 2m`, then
`2 𝒞_{2m} = -𝒢(χ (·/p))`. -/
theorem exponent_collapse_second {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) := by
  sorry

/-- **The cosets** (Paper II, §2). At `p ≡ 5 (mod 8)` a quartic `χ` is odd, its fibre over `1` is
the group `H` of nonzero fourth powers, and if `χ(2) = i` its fibre over `i` is `2H`. -/
theorem cosets_as_fibers {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    χ (-1) = -1 ∧ fiber χ 1 = univ.filter (fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x) ∧
      (χ 2 = gi → fiber χ gi = (fiber χ 1).image (2 * ·)) := by
  sorry

/-- **Lemma 2.1.** `Re 𝒞(a) = ∑_{u ∈ H} s(u) s(au²)` and `Im 𝒞(a) = ∑_{u ∈ F_i} s(u) s(au²)`, where
`F_i` is the fibre of `χ` over `i` (which is `2H` when `χ(2) = i`). -/
theorem coset_decomposition {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) := by
  sorry

/-- `𝒢(χ) = 2γ` with `γ = A + iB`, and `p γ = (1 - 2i) T(χ)` when `χ(2) = i`, i.e. `γ = (1 - 2i)β`. -/
theorem gamma_identities {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    G χ = 2 * gamma χ ∧ (χ 2 = gi → (p : GaussianInt) * gamma χ = (1 - 2 * gi) * T χ) := by
  sorry

/-- **The terminal values** (Corollary 3.2, quartic case): if `(p - 1) ∣ 4m` then `𝒞_{2m} = -γ`
when `(p - 1) ∣ 2m` and `𝒞_{2m} = -γ̄` otherwise. -/
theorem exponent_terminal_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) := by
  sorry

/-- **The coset trace** (Corollary 3.3): for `c ∈ {1, i, -1, -i}`,
`∑_{χ(a) = c} 𝒞(a) = Re(c̄ γ) γ̄`. -/
theorem coset_trace_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) := by
  sorry

/-- **The coset trace, second form** (Corollary 3.3): `2 ∑_{χ(a) = c} 𝒞(a) = c̄ |γ|² + c γ̄²`. -/
theorem coset_trace_second {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 := by
  sorry

/-- **The family means** (Corollary 3.3): `∑_{a ∈ H} Re 𝒞(a) = A²`, `∑_{a ∈ H} Im 𝒞(a) = -AB`. -/
theorem family_mean_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    (∑ a ∈ fiber χ 1, fam χ 2 a).re = sigma χ 1 ^ 2 ∧
      (∑ a ∈ fiber χ 1, fam χ 2 a).im = -(sigma χ 1 * sigma χ gi) := by
  sorry

/-- **Conjugate dynamics** (Proposition 4.1): for `a ∈ H`, `Re 𝒞(a) = ∑_{v ∈ H} s(a⁻¹v) s(a⁻¹v²)`. -/
theorem conjugate_dynamics_squaring {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {a : ZMod p} (ha : a ∈ fiber χ 1) :
    (fam χ 2 a).re = ∑ v ∈ fiber χ 1, parSign (a⁻¹ * v) * parSign (a⁻¹ * v ^ 2) := by
  sorry

/-- **Second moments over the family** (Proposition 4.2):
`∑_{a ∈ H} (Re 𝒞(a))² = ∑_{d ∈ H} M(d) M(d²)` and `∑_{a ∈ H} (Im 𝒞(a))² = ∑_{d ∈ H} M_{F_i}(d) M(d²)`,
with `F_i` the fibre over `i` (`2H` when `χ(2) = i`). -/
theorem second_moments {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) ∧
      ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) := by
  sorry

/-- **The gcd decomposition** (proof of Proposition 6.3): every `(n, n') ∈ [1, N]²` is `(ar, br)` for
one coprime `(a, b)` and one `r ≤ ⌊N / max(a, b)⌋`. -/
theorem gcd_decomposition {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) := by
  sorry

/-- `𝒞 = ∑_{n ≤ (p-1)/2} χ(n) ε_n` with `ε_n = (-1)^{⌊n²/p⌋}`. -/
theorem band_sum_interval (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) := by
  sorry

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
            ((eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt)) := by
  sorry

/-- **Parseval** (Proposition 7.1): `∑_{ψ mod p} |∑_{n ≤ N} ψ(n) ε_n|² = (p - 1) N`, `N = (p-1)/2`. -/
theorem parseval_identity :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (eps p n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by
  sorry

/-- Parseval for any weight `w` with `w(n)² = 1`. -/
theorem parseval_any_weight (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by
  sorry

/-- Every member of the multiplier family is a half-interval sum with a `±1` weight:
`𝒞_χ^{(2)}(a) = ∑_{n ≤ (p-1)/2} χ(n) (-1)^{n + ⟨a n²⟩}`. -/
theorem multiplier_family_interval (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (a : ZMod p) :
    fam χ 2 a = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) *
      (((-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val) : ℤ) : R) := by
  sorry

/-- Parseval over the odd characters, for any weight with `w(n)² = 1`:
`∑_{χ odd} |∑_{n ≤ N} χ(n) w(n)|² = ((p - 1)/2) N`, `N = (p - 1)/2`. -/
theorem parseval_odd_characters (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ ∈ oddChars p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) / 2 * ((p - 1) / 2 : ℕ) := by
  sorry

/-- **The Bernoulli mean square** (companion paper, Theorem 7.3). For an odd prime `p` and
`a ≠ 0`, `∑_{χ odd} |∑_{ψ odd} ψ(a) (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}|² = ((p-1)/2)⁴`. -/
theorem bernoulli_mean_square_identity (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ∑ χ ∈ oddChars p, ‖∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
        (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2)‖ ^ 2 =
      (((p : ℝ) - 1) / 2) ^ 4 := by
  sorry

end Statements

end MellinDuality
