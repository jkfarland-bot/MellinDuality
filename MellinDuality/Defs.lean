module

public import Mathlib
public import MellinDuality.Basic

@[expose] public section

/-!
# Mellin duality: definitions

Throughout `p` is a prime, `x.val` is the least nonnegative residue of `x : ZMod p`, and
`s(x) = (-1)^⟨x⟩`. For a multiplicative character `χ` modulo `p` with values in a commutative
ring `R`, the paper (Farland, *What the band-parity companion is*, Paper II) studies the
multiplier family

  `𝒞_χ^{(e)}(a) = ∑_{0 < n < p/2} χ(n) (-1)^{n + ⟨a n^e⟩}`

(`e = 2` is Mellin duality, `e = 2m` the exponent family) and the multiplier constant

  `𝒢(ψ) = ∑_{m=1}^{p-1} ψ(m) (-1)^m`.
-/

namespace MellinDuality

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

end MellinDuality
