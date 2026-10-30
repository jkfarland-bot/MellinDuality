# MellinDuality

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23795143.svg)](https://doi.org/10.5281/zenodo.23795143)

Software archive: version v1.0 is [doi:10.5281/zenodo.23795144](https://doi.org/10.5281/zenodo.23795144);
all versions are [doi:10.5281/zenodo.23795143](https://doi.org/10.5281/zenodo.23795143).

Lean 4 / Mathlib formalization of the proved, finite part of J. S. Farland, *What the band-parity
companion is: Mellin duality, Weil sums, and the Gauss-sum axis* (Paper II of the author's series).
It continues [BandParity](https://github.com/jkfarland-bot/bandparity) and
[BandParityTower](https://github.com/jkfarland-bot/Bandparitytower), which formalized Paper I.

The companion paper is J. S. Farland, *Mellin duality for the band-parity companion, formalized in
Lean* (preprint, Zenodo, 2026; v1.0
[doi:10.5281/zenodo.23796263](https://doi.org/10.5281/zenodo.23796263), all versions
[doi:10.5281/zenodo.23796262](https://doi.org/10.5281/zenodo.23796262)).

For an odd prime `p`, characters `χ`, `ψ` modulo `p`, `s(x) = (-1)^⟨x⟩` and `m ≥ 0` put

  `𝒞_χ^{(2m)}(a) = ∑_{0<n<p/2} χ(n) (-1)^{n + ⟨a n^{2m}⟩}`,  `𝒢(ψ) = ∑_{m=1}^{p-1} ψ(m) (-1)^m`.

At `a = 1` and for the quartic character, `𝒞 = ∑_{0<n<p/2} χ₄(n) (-1)^{⌊n²/p⌋}` is the band-parity
companion of a quartic L-value. This repository proves:

- **The multiplier constant** (Paper II, (1)). `𝒢(φ) = 0` for even `φ`; for odd `φ`,
  `𝒢(φ) = 2 ∑_{0<n<p/2} φ(n)(-1)^n = 2φ(2) ∑_{0<n<p/2} φ(n)`, and the classical half-sum identity
  `p 𝒢(φ) = 2(1 - 2φ(2)) T(φ)`, i.e. `𝒢(φ) = 2(1 - 2φ(2)) B_{1,φ}`.
- **Mellin duality** (Theorem 3.1, Corollary 3.2). For odd `χ`, any `ψ` and every `m`,
  `2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χψ^{2m})`, over any commutative ring; for complex characters
  and `a ≠ 0`, `𝒞_χ^{(2m)}(a) = (1/(2(p-1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χψ^{2m})`, and in Bernoulli form
  `𝒞_χ(a) = (2/(p-1)) ∑_{ψ odd} ψ(a)(1 - 2ψ̄(2))(1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`.
- **The exponent family** (Corollary 3.2). The dual formula for `𝒞_{2m}`, the collapse
  `2𝒞_{2m} = -𝒢(χ)` when `(p-1) ∣ 2m` and `2𝒞_{2m} = -𝒢(χ (·/p))` when `(p-1) ∣ 4m`, `(p-1) ∤ 2m`,
  and, for the quartic character, the terminal values `-γ` and `-γ̄`.
- **The quartic family** at `p ≡ 5 (mod 8)`, with `H` the fourth powers, `A = ∑_H s`, `B = ∑_{2H} s`,
  `γ = A + iB = (1 - 2i)β`: the coset lemma (Lemma 2.1), the coset trace
  `∑_{a ∈ gH} 𝒞(a) = Re(χ̄₄(g)γ) γ̄` in both forms and the family means `A²`, `-AB`
  (Corollary 3.3), conjugate dynamics (Proposition 4.1) and the two second-moment identities
  (Proposition 4.2).
- **The pair structure** (Proposition 6.3): `𝒞S̄`, `𝒞S`, `|𝒞|²`, `𝒞²` as exact sums over coprime pairs,
  and **Parseval** (Proposition 7.1): `∑_ψ |∑_{n≤N} ψ(n) ε_n|² = (p-1)N`.
- **The Bernoulli mean square** (companion paper v2, Theorem 7.3; new in v1.1). For every odd prime
  `p` and `a ≢ 0`, with `X_χ(a) = ∑_{ψ odd} ψ(a)(1 - 2ψ̄(2))(1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`,
  `∑_{χ odd} |X_χ(a)|² = ((p-1)/2)⁴`. The proof combines the inversion `X_χ(a) = ((p-1)/2) 𝒞_χ(a)`
  with Parseval over the odd characters (Proposition 7.2), using that `𝒞_χ(a)` is a sum over
  `n ≤ (p-1)/2` with a `±1` weight (Lemma 7.1). This result is not in Paper II: it was proposed by
  Claude during the formalization and adopted by the author.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. The export of `Solution` is accepted by the Lean kernel, nanoda and con-ron.

## Scope, hypotheses and limitations

- Mellin duality, the multiplier constant, the parity dictionary and the collapse are stated for
  `MulChar (ZMod p) R` in any commutative ring, with `ψ̄ = ψ⁻¹`. The inversion uses orthogonality and
  is stated for `DirichletCharacter ℂ p`, where `ψ⁻¹` is the complex conjugate. Sums over units are
  taken over all of `ZMod p`, since characters vanish at `0`.
- The exponent family is proved for every odd character modulo every odd prime; the paper states it
  for the quartic character at `p ≡ 5 (mod 8)`.
- The cosets `H, 2H, -H, -2H` are the fibres of `χ₄` over `1, i, -1, -i` (`fiber χ z`);
  `cosets_as_fibers` proves this, using `χ₄(2) = i` for `2H`. The coset lemma, the coset trace and
  the second moments need only that `χ₄` has order 4; for `χ₄(2) = -i` the fibre over `i` is `-2H`.
- `B_{1,ψ}` is `T ψ / p` with `T ψ = ∑ ψ(m) m`.
- Not formalized: the Weil-sum expansion (Theorem 5.1), which needs the functional equation and the
  convergence of `L(1,ψ)`; the self-duality lemma (Lemma 5.2); the diagonal model (Prediction 5.3);
  the band-sum bounds (Lemma 6.2) and Proposition 6.4, which need Weil's bound; Conjecture 6.1,
  Question 5.8 and the observations.

## Sources and novelty

The half-sum identity is classical and is formalized as an input. Mellin duality is a two-line
substitution; what is new is the multiplier family and the bilinear formula
`∑_ψ ψ(a) B_{1,ψ̄} B_{1,χψ²}`, which the author found nowhere in the literature searched. The nearest work is Louboutin's mean values of products of
L-functions (arXiv:2405.17981), where no character appears squared and no sum is twisted by `ψ(a)`.
The coset trace is the band-parity analogue of Louboutin's evaluation of sums of Dedekind sums over a
subgroup (Bull. Pol. Acad. Sci. Math. 64 (2016); arXiv:2406.02802). The gcd decomposition and
Parseval are standard. The Bernoulli mean square combines the duality with Parseval over the odd characters; it is
not in Paper II, and we found it in none of the literature searched.

## Authorship, AI assistance and licence

The mathematics, the statements and the paper are by Joseph S. Farland. The Lean code was drafted
and repaired by Claude (Anthropic) against the paper's statements and proofs. The code is released
under the Apache License 2.0 (`LICENSE`); the paper is CC BY 4.0.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface to audit. It restates the definitions exactly as the
  development has them and states the 29 results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `MellinDuality/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the Palomar starter template.
- `check/statements.py` recomputes every formalized statement numerically.

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Paper II | Challenge declaration |
|---|---|
| (1), §2 | `multiplier_constant_half`, `multiplier_constant_even`, `half_sum_identity`, `multiplier_constant_bern` |
| §2 (Paper I, Lemma 2.5) | `parity_dictionary` |
| §2, cosets | `cosets_as_fibers`, `gamma_identities` |
| Lemma 2.1 | `coset_decomposition` |
| Theorem 3.1 | `mellin_duality`, `mellin_duality_inverse`, `mellin_duality_bernoulli`, `mellin_duality_quartic` |
| Corollary 3.2 | `exponent_family_dual`, `exponent_collapse_first`, `exponent_collapse_second`, `exponent_terminal_values` |
| Corollary 3.3 | `coset_trace_values`, `coset_trace_second`, `family_mean_values` |
| Proposition 4.1 | `conjugate_dynamics_squaring` |
| Proposition 4.2 | `second_moments` |
| Proposition 6.3 | `gcd_decomposition`, `band_sum_interval`, `pair_structure_identities` |
| Proposition 7.1 | `parseval_identity`, `parseval_any_weight` |
| companion paper v2, Lemma 7.1 | `multiplier_family_interval` |
| companion paper v2, Proposition 7.2 | `parseval_odd_characters` |
| companion paper v2, Theorem 7.3 | `bernoulli_mean_square_identity` |

## Files

| File | Contents |
|---|---|
| `Basic` | quartic characters with values in `ℤ[i]`, copied from the earlier repositories |
| `Defs` | the definitions |
| `Half` | half systems, the multiplier constant, the half-sum identity |
| `Mellin` | the parity dictionary, Mellin duality and its inversion, the exponent family |
| `Quartic` | cosets as fibres, the coset lemma and trace, conjugate dynamics, second moments |
| `Parseval` | Proposition 7.1 |
| `Pairs` | the gcd decomposition and Proposition 6.3 |
| `MeanSquare` | the family on an interval, Parseval over the odd characters, the Bernoulli mean square |
