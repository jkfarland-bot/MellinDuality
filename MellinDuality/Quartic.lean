module

public import MellinDuality.Mellin

@[expose] public section

/-!
# The quartic case: coset sums, the coset trace and second moments

Let `p ≡ 5 (mod 8)` and let `χ` be a quartic character with values in `ℤ[i]`. Its fibres over
`1, i, -1, -i` are the cosets of the group `H` of nonzero fourth powers (`fiber_one_eq`,
`fiber_gi_eq`, the latter when `χ(2) = i`). With `A = ∑_H s`, `B = ∑_{2H} s`, `γ = A + iB`:

* `fam_eq_fibers`, `coset_lemma` (Lemma 2.1 of Paper II):
  `Re 𝒞(a) = ∑_{u ∈ H} s(u) s(a u²)`, `Im 𝒞(a) = ∑_{u ∈ 2H} s(u) s(a u²)`;
* `G_eq_two_gamma`: `𝒢(χ) = 2γ`; `gamma_bernoulli`: `p γ = (1 - 2i) T(χ)`, i.e. `γ = (1 - 2i)β`;
* `coset_trace`, `coset_trace_second_form`, `family_means` (Corollary 3.3);
* `quartic_terminal` (the terminal values of the exponent family, Corollary 3.2);
* `conjugate_dynamics` (Proposition 4.1) and `second_moment_re`, `second_moment_im`
  (Proposition 4.2).
-/

namespace MellinDuality

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma re_sum {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.re_add, ih]

lemma im_sum {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.im_add, ih]

omit hp in
lemma hp2_of (hp8 : p % 8 = 5) : p ≠ 2 := by omega

/-- `∑_{u ∈ X} s(u) s(a u²)`. -/
def sqCorr (X : Finset (ZMod p)) (a : ZMod p) : ℤ := ∑ u ∈ X, parSign u * parSign (a * u ^ 2)

section Fibers

variable {χ : MulChar (ZMod p) GaussianInt}

lemma mem_fiber {x : ZMod p} {z : GaussianInt} : x ∈ fiber χ z ↔ χ x = z := by simp [fiber]

lemma ne_zero_of_mem_fiber {x : ZMod p} {z : GaussianInt} (hz : z ≠ 0) (hx : x ∈ fiber χ z) :
    x ≠ 0 := by
  rintro rfl; rw [mem_fiber, MulChar.map_zero] at hx; exact hz hx.symm

/-- Multiplying by `w ≠ 0` maps the fibre of `c` onto the fibre of `c χ(w)`. -/
lemma sum_fiber_mul {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (c : GaussianInt)
    {w : ZMod p} (hw : w ≠ 0) (hwu : χ w * χ w⁻¹ = 1) :
    ∑ a ∈ fiber χ c, f (a * w) = ∑ b ∈ fiber χ (c * χ w), f b := by
  refine sum_nbij' (· * w) (· * w⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha; rw [mem_fiber] at *; rw [map_mul, ha]
  · intro b hb
    rw [mem_fiber] at *
    rw [map_mul, hb, mul_assoc, hwu, mul_one]
  · intro a _; simp [mul_assoc, mul_inv_cancel₀ hw]
  · intro b _; simp [mul_assoc, inv_mul_cancel₀ hw]
  · intro a _; rfl

lemma char_mul_char_inv {x : ZMod p} (hx : x ≠ 0) : χ x * χ x⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]

variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ

lemma quartic_odd : χ (-1) = -1 := quartic_apply_neg_one χ hχ hp8

omit hp8 in
lemma char_ne_zero {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by
  rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide

lemma sum_fiber_neg {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (z : GaussianInt) :
    ∑ x ∈ fiber χ (-z), f x = ∑ x ∈ fiber χ z, f (-x) := by
  have hodd := quartic_odd hp8 hχ
  refine sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; rw [mem_fiber] at *; rw [apply_neg_of_odd χ hodd, hx, neg_neg]
  · intro x hx; rw [mem_fiber] at *; rw [apply_neg_of_odd χ hodd, hx]
  · intro x _; simp
  · intro x _; simp
  · intro x _; simp

omit hp8 in
/-- A sum over `ZMod p` of a function vanishing at `0` splits over the four fibres. -/
lemma sum_univ_fibers {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ x, f x = ∑ x ∈ fiber χ 1, f x + ∑ x ∈ fiber χ gi, f x + ∑ x ∈ fiber χ (-1), f x +
      ∑ x ∈ fiber χ (-gi), f x := by
  have hmaps : ∀ x ∈ (univ : Finset (ZMod p)),
      χ x ∈ ({0, 1, gi, -1, -gi} : Finset GaussianInt) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · rcases quartic_values χ hχ hx with h | h | h | h <;> simp [h]
  rw [← sum_fiberwise_of_maps_to hmaps, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have hz : ∑ x ∈ univ.filter (fun x => χ x = 0), f x = 0 := by
    refine sum_eq_zero fun x hx => ?_
    have hx0 : x = 0 := by
      by_contra h; exact char_ne_zero hχ h (mem_filter.1 hx).2
    rw [hx0, h0]
  rw [hz, zero_add]
  simp only [fiber, add_assoc]

/-- `σ(-z) = -σ(z)` for `z ≠ 0`. -/
lemma sigma_neg {z : GaussianInt} (hz : z ≠ 0) : sigma χ (-z) = -sigma χ z := by
  unfold sigma
  rw [sum_fiber_neg hp8 hχ, ← sum_neg_distrib]
  exact sum_congr rfl fun x hx => parSign_neg (hp2_of hp8) (ne_zero_of_mem_fiber hz hx)

/-- **Lemma 2.1 of Paper II** in one line: `𝒞(a) = ∑_{u ∈ H} s(u)s(au²) + i ∑_{u ∈ 2H} s(u)s(au²)`. -/
theorem fam_eq_fibers (a : ZMod p) :
    fam χ 2 a = ⟨sqCorr (fiber χ 1) a, sqCorr (fiber χ gi) a⟩ := by
  have hodd := quartic_odd hp8 hχ
  have hp2 := hp2_of hp8
  set g : ZMod p → GaussianInt := fun x =>
    χ x * (parSign x : GaussianInt) * (parSign (a * x ^ 2) : GaussianInt) with hg
  have hg0 : g 0 = 0 := by simp [g, MulChar.map_zero]
  have hgneg : ∀ x, g (-x) = g x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp only [g, apply_neg_of_odd χ hodd, parSign_neg hp2 hx, neg_sq]; push_cast; ring
  have h1 : (2 : GaussianInt) * fam χ 2 a = ∑ x, g x := by
    rw [sum_univ_eq_sum_half hp2 g hg0, fam_eq, mul_sum]
    exact sum_congr rfl fun n _ => by rw [hgneg]; simp only [g]; ring
  have h2 : ∑ x, g x = 2 * (∑ u ∈ fiber χ 1, g u + ∑ u ∈ fiber χ gi, g u) := by
    rw [sum_univ_fibers hχ g hg0, sum_fiber_neg hp8 hχ g 1, sum_fiber_neg hp8 hχ g gi]
    simp_rw [hgneg]; ring
  have h3 : ∑ u ∈ fiber χ 1, g u = ((sqCorr (fiber χ 1) a : ℤ) : GaussianInt) := by
    unfold sqCorr; push_cast
    exact sum_congr rfl fun u hu => by simp only [g, mem_fiber.1 hu]; ring
  have h4 : ∑ u ∈ fiber χ gi, g u = gi * ((sqCorr (fiber χ gi) a : ℤ) : GaussianInt) := by
    unfold sqCorr; push_cast; rw [mul_sum]
    exact sum_congr rfl fun u hu => by simp only [g, mem_fiber.1 hu]; ring
  have key := h1.trans h2
  rw [h3, h4] at key
  have := mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0) key
  rw [this]
  ext <;> simp [gi]

/-- **Lemma 2.1 of Paper II.** `Re 𝒞(a) = ∑_{u ∈ H} s(u) s(a u²)` and
`Im 𝒞(a) = ∑_{u ∈ 2H} s(u) s(a u²)`. -/
theorem coset_lemma (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) := by
  rw [fam_eq_fibers hp8 hχ]; exact ⟨rfl, rfl⟩

/-- `𝒢(χ) = 2γ` with `γ = A + iB`. -/
theorem G_eq_two_gamma : G χ = 2 * gamma χ := by
  have hfib : ∀ z : GaussianInt, ∑ x ∈ fiber χ z, χ x * (parSign x : GaussianInt) =
      z * (sigma χ z : GaussianInt) := by
    intro z; unfold sigma; push_cast; rw [mul_sum]
    exact sum_congr rfl fun x hx => by rw [mem_fiber.1 hx]
  unfold G
  rw [sum_univ_fibers hχ _ (by simp [MulChar.map_zero]), hfib, hfib, hfib, hfib,
    sigma_neg hp8 hχ one_ne_zero, sigma_neg hp8 hχ (by decide : gi ≠ 0)]
  unfold gamma
  ext <;> simp [gi] <;> ring

/-- `p γ = (1 - 2i) T(χ)` when `χ(2) = i`: `γ = (1 - 2i) β` with `β = B_{1,χ}`. -/
theorem gamma_bernoulli (hpin : χ 2 = gi) : (p : GaussianInt) * gamma χ = (1 - 2 * gi) * T χ := by
  have h := bernoulli_form (hp2_of hp8) χ (quartic_odd hp8 hχ)
  rw [G_eq_two_gamma hp8 hχ, hpin] at h
  apply mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0)
  linear_combination h

/-- The four fibre sums of `s`: `σ(c) = Re(c̄ γ)` for `c ∈ {1, i, -1, -i}`. -/
lemma sigma_eq_re {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    sigma χ c = (star c * gamma χ).re := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp [gamma]
  · simp [gamma, gi]
  · rw [sigma_neg hp8 hχ one_ne_zero]; simp [gamma]
  · rw [sigma_neg hp8 hχ (by decide : gi ≠ 0)]; simp [gamma, gi]

/-- `∑_{a ∈ cH} 𝒞(a) = σ(c) γ̄`, with the coset as a fibre. -/
lemma sum_fiber_fam {c : GaussianInt} (hc0 : c ≠ 0) :
    ∑ a ∈ fiber χ c, fam χ 2 a = (sigma χ c : GaussianInt) * star (gamma χ) := by
  have hinner : ∀ u : ZMod p, u ≠ 0 →
      ∑ a ∈ fiber χ c, parSign (a * u ^ 2) = sigma χ (c * χ (u ^ 2)) := by
    intro u hu
    exact sum_fiber_mul (fun b => parSign b) c (pow_ne_zero 2 hu)
      (char_mul_char_inv (pow_ne_zero 2 hu))
  have hre : ∑ a ∈ fiber χ c, sqCorr (fiber χ 1) a = sigma χ c * sigma χ 1 := by
    unfold sqCorr; rw [sum_comm]
    unfold sigma; rw [mul_comm, sum_mul]
    refine sum_congr rfl fun u hu => ?_
    have hu0 := ne_zero_of_mem_fiber one_ne_zero hu
    rw [← mul_sum, hinner u hu0, map_pow, mem_fiber.1 hu, one_pow, mul_one]
    unfold sigma; ring
  have him : ∑ a ∈ fiber χ c, sqCorr (fiber χ gi) a = -(sigma χ c * sigma χ gi) := by
    unfold sqCorr; rw [sum_comm]
    conv_rhs => unfold sigma
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun u hu => ?_
    have hu0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hu
    rw [← mul_sum, hinner u hu0, map_pow, mem_fiber.1 hu, gi_sq, mul_neg_one,
      sigma_neg hp8 hχ hc0]
    simp only [sigma]; ring
  simp_rw [fam_eq_fibers hp8 hχ]
  ext
  · rw [re_sum]; simp [hre, gamma]
  · rw [im_sum]; simp [him, gamma]

/-- **The coset trace** (Corollary 3.3 of Paper II). For `c ∈ {1, i, -1, -i}`, the sum of the
family over the fibre `{a : χ(a) = c}` (the coset `gH` with `χ(g) = c`) is `Re(c̄ γ) γ̄`. -/
theorem coset_trace {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl | rfl | rfl <;> decide
  rw [sum_fiber_fam hp8 hχ hc0, sigma_eq_re hp8 hχ hc]

/-- **The coset trace, second form**: `2 ∑_{a ∈ cH} 𝒞(a) = c̄ |γ|² + c γ̄²`; with `γ = (1 - 2i)β`
this is `5|β|² c̄ + γ̄² c`. -/
theorem coset_trace_second_form {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 := by
  rw [coset_trace hp8 hχ hc]
  have hre : ∀ x : GaussianInt, 2 * ((x.re : ℤ) : GaussianInt) = x + star x := by
    intro x; ext <;> simp [two_mul]
  rw [← mul_assoc, hre, star_mul', star_star]
  ring

/-- **The family means** (Corollary 3.3): `∑_{a ∈ H} Re 𝒞(a) = A²` and
`∑_{a ∈ H} Im 𝒞(a) = -AB`. -/
theorem family_means :
    (∑ a ∈ fiber χ 1, fam χ 2 a).re = sigma χ 1 ^ 2 ∧
      (∑ a ∈ fiber χ 1, fam χ 2 a).im = -(sigma χ 1 * sigma χ gi) := by
  rw [sum_fiber_fam hp8 hχ one_ne_zero]
  constructor <;> simp [gamma, sq]

omit hp8 in
/-- `𝒢(χ (·/p)) = 𝒢(χ̄)`: for the quartic character, `χ (·/p) = χ̄`. -/
lemma G_mul_quad : G (χ * quadR p GaussianInt) = star (G χ) := by
  unfold G
  rw [star_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [star_mul', star_intCast]
  congr 1
  by_cases hx : x = 0
  · subst hx; simp [MulChar.map_zero]
  · have hq := quadraticChar_eq_sq hχ hx
    rw [MulChar.mul_apply]
    simp only [quadR, MulChar.ringHomComp_apply, eq_intCast]
    rw [hq]
    rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide

/-- **The terminal values of the exponent family** (Corollary 3.2 of Paper II, quartic case): if
`(p - 1) ∣ 4m` then `𝒞_{2m} = -γ` when `(p - 1) ∣ 2m` and `𝒞_{2m} = -γ̄` otherwise; with
`γ = (1 - 2i)β` these are `-(1 - 2i)β` and its conjugate. -/
theorem quartic_terminal {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) := by
  have hp2 := hp2_of hp8
  have hodd := quartic_odd hp8 hχ
  apply mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0)
  split_ifs with h2
  · rw [exponent_collapse_one hp2 χ hodd hm h2, G_eq_two_gamma hp8 hχ]; ring
  · rw [exponent_collapse_two hp2 χ hodd h4 h2, G_mul_quad hχ, G_eq_two_gamma hp8 hχ,
      star_mul', star_ofNat]
    ring

omit hp8 in
/-- `fiber χ 1` is the group `H` of nonzero fourth powers. -/
theorem fiber_one_eq : fiber χ 1 = univ.filter fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x := by
  ext x
  simp only [mem_fiber, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have hx : x ≠ 0 := by rintro rfl; rw [MulChar.map_zero] at h; exact zero_ne_one h
    exact ⟨hx, (char_eq_one_iff hχ hx).1 h⟩
  · rintro ⟨hx, hy⟩; exact (char_eq_one_iff hχ hx).2 hy

omit hχ in
/-- With `χ(2) = i`, `fiber χ i = 2H`. -/
theorem fiber_gi_eq (hpin : χ 2 = gi) : fiber χ gi = (fiber χ 1).image (2 * ·) := by
  have h2 := two_ne_zero_zmod (hp2_of hp8)
  ext x
  simp only [mem_image, mem_fiber]
  constructor
  · intro hx
    refine ⟨2⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]⟩
    have : χ 2 * χ (2⁻¹ * x) = gi := by rw [← map_mul, ← mul_assoc, mul_inv_cancel₀ h2, one_mul, hx]
    rw [hpin] at this
    exact mul_left_cancel₀ (by decide : gi ≠ 0) (this.trans (mul_one gi).symm)
  · rintro ⟨u, hu, rfl⟩; rw [map_mul, hpin, hu, mul_one]

/-- **Conjugate dynamics** (Proposition 4.1 of Paper II). For `a ∈ H`, with `c = a⁻¹`,
`Re 𝒞(a) = ∑_{v ∈ H} s(c v) s(c v²)`. -/
theorem conjugate_dynamics {a : ZMod p} (ha : a ∈ fiber χ 1) :
    (fam χ 2 a).re = ∑ v ∈ fiber χ 1, parSign (a⁻¹ * v) * parSign (a⁻¹ * v ^ 2) := by
  have ha0 := ne_zero_of_mem_fiber one_ne_zero ha
  have hinv : χ a⁻¹ = 1 := by
    have := char_mul_char_inv (χ := χ) ha0; rwa [mem_fiber.1 ha, one_mul] at this
  rw [(coset_lemma hp8 hχ a).1]
  have := sum_fiber_mul (χ := χ) (fun u => parSign u * parSign (a * u ^ 2)) 1
    (inv_ne_zero ha0) (by rw [inv_inv, mul_comm]; exact char_mul_char_inv ha0)
  rw [hinv, mul_one] at this
  rw [← this]
  refine sum_congr rfl fun v _ => ?_
  rw [mul_comm v a⁻¹]
  congr 2
  field_simp

/-- **Second moments over the family** (Proposition 4.2 of Paper II):
`∑_{a ∈ H} (Re 𝒞(a))² = ∑_{d ∈ H} M(d) M(d²)` with `M(d) = ∑_{u ∈ H} s(u) s(d u)`. -/
theorem second_moment_re :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
      ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) := by
  set F1 := fiber χ 1
  have hinner : ∀ u ∈ F1, ∀ v : ZMod p,
      ∑ a ∈ F1, parSign (a * u ^ 2) * parSign (a * v ^ 2) = multCorr F1 ((v * u⁻¹) ^ 2) := by
    intro u hu v
    have hu0 := ne_zero_of_mem_fiber one_ne_zero hu
    have h := sum_fiber_mul (χ := χ) (fun b => parSign b * parSign ((v * u⁻¹) ^ 2 * b)) 1
      (pow_ne_zero 2 hu0) (char_mul_char_inv (pow_ne_zero 2 hu0))
    rw [map_pow, mem_fiber.1 hu, one_pow, mul_one] at h
    rw [multCorr, ← h]
    refine sum_congr rfl fun a _ => ?_
    congr 2; field_simp
  have hshift : ∀ u ∈ F1, ∑ v ∈ F1, parSign v * multCorr F1 ((v * u⁻¹) ^ 2) =
      ∑ d ∈ F1, parSign (d * u) * multCorr F1 (d ^ 2) := by
    intro u hu
    have hu0 := ne_zero_of_mem_fiber one_ne_zero hu
    have h := sum_fiber_mul (χ := χ) (fun v => parSign v * multCorr F1 ((v * u⁻¹) ^ 2)) 1
      hu0 (char_mul_char_inv hu0)
    rw [mem_fiber.1 hu, mul_one] at h
    rw [← h]
    refine sum_congr rfl fun d _ => ?_
    congr 3; field_simp
  calc ∑ a ∈ F1, (fam χ 2 a).re ^ 2
      = ∑ a ∈ F1, ∑ u ∈ F1, ∑ v ∈ F1,
          parSign u * parSign v * (parSign (a * u ^ 2) * parSign (a * v ^ 2)) := by
        refine sum_congr rfl fun a _ => ?_
        rw [(coset_lemma hp8 hχ a).1, sq, sum_mul_sum]
        exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
    _ = ∑ u ∈ F1, ∑ v ∈ F1, parSign u * parSign v * multCorr F1 ((v * u⁻¹) ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun u hu => ?_
        rw [sum_comm]
        refine sum_congr rfl fun v _ => ?_
        rw [← mul_sum, hinner u hu v]
    _ = ∑ u ∈ F1, ∑ d ∈ F1, parSign u * parSign (d * u) * multCorr F1 (d ^ 2) := by
        refine sum_congr rfl fun u hu => ?_
        simp_rw [mul_assoc (parSign u)]
        rw [← mul_sum, ← mul_sum, hshift u hu]
    _ = ∑ d ∈ F1, multCorr F1 d * multCorr F1 (d ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_mul]; rfl

/-- **Second moments over the family** (Proposition 4.2 of Paper II):
`∑_{a ∈ H} (Im 𝒞(a))² = ∑_{d ∈ H} M_{2H}(d) M(d²)`. -/
theorem second_moment_im :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
      ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) := by
  set F1 := fiber χ 1
  set Fi := fiber χ gi
  have hp2 := hp2_of hp8
  have hinner : ∀ u ∈ Fi, ∀ v ∈ Fi,
      ∑ a ∈ F1, parSign (a * u ^ 2) * parSign (a * v ^ 2) = multCorr F1 ((v * u⁻¹) ^ 2) := by
    intro u hu v hv
    have hu0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hu
    have hv0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hv
    have he0 : (v * u⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hv0 (inv_ne_zero hu0))
    have h := sum_fiber_mul (χ := χ) (fun b => parSign b * parSign ((v * u⁻¹) ^ 2 * b)) 1
      (pow_ne_zero 2 hu0) (char_mul_char_inv (pow_ne_zero 2 hu0))
    rw [map_pow, mem_fiber.1 hu, gi_sq, one_mul] at h
    rw [multCorr, ← (show ∑ b ∈ fiber χ (-1), parSign b * parSign ((v * u⁻¹) ^ 2 * b) =
        ∑ b ∈ F1, parSign b * parSign ((v * u⁻¹) ^ 2 * b) from ?_), ← h]
    · refine sum_congr rfl fun a _ => ?_
      congr 2; field_simp
    · rw [sum_fiber_neg hp8 hχ]
      refine sum_congr rfl fun b hb => ?_
      have hb0 := ne_zero_of_mem_fiber one_ne_zero hb
      rw [mul_neg, parSign_neg hp2 hb0, parSign_neg hp2 (mul_ne_zero he0 hb0)]
      ring
  have hshift : ∀ u ∈ Fi, ∑ v ∈ Fi, parSign v * multCorr F1 ((v * u⁻¹) ^ 2) =
      ∑ d ∈ F1, parSign (d * u) * multCorr F1 (d ^ 2) := by
    intro u hu
    have hu0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hu
    have h := sum_fiber_mul (χ := χ) (fun v => parSign v * multCorr F1 ((v * u⁻¹) ^ 2)) 1
      hu0 (char_mul_char_inv hu0)
    rw [mem_fiber.1 hu, one_mul] at h
    rw [← h]
    refine sum_congr rfl fun d _ => ?_
    congr 3; field_simp
  calc ∑ a ∈ F1, (fam χ 2 a).im ^ 2
      = ∑ a ∈ F1, ∑ u ∈ Fi, ∑ v ∈ Fi,
          parSign u * parSign v * (parSign (a * u ^ 2) * parSign (a * v ^ 2)) := by
        refine sum_congr rfl fun a _ => ?_
        rw [(coset_lemma hp8 hχ a).2, sq, sum_mul_sum]
        exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
    _ = ∑ u ∈ Fi, ∑ v ∈ Fi, parSign u * parSign v * multCorr F1 ((v * u⁻¹) ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun u hu => ?_
        rw [sum_comm]
        refine sum_congr rfl fun v hv => ?_
        rw [← mul_sum, hinner u hu v hv]
    _ = ∑ u ∈ Fi, ∑ d ∈ F1, parSign u * parSign (d * u) * multCorr F1 (d ^ 2) := by
        refine sum_congr rfl fun u hu => ?_
        simp_rw [mul_assoc (parSign u)]
        rw [← mul_sum, ← mul_sum, hshift u hu]
    _ = ∑ d ∈ F1, multCorr Fi d * multCorr F1 (d ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_mul]; rfl

end Fibers

end MellinDuality
