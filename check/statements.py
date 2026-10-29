# Numerical check of the Lean statements of MellinDuality, exactly as formalized.
# Quartic statements use exact Gaussian integers (Python complex numbers with integer parts);
# statements over C use floating point with tolerance 1e-8.
import cmath, math
from math import gcd
from sympy import primerange, primitive_root, legendre_symbol

fails = {}
def F(name):
    fails[name] = fails.get(name, 0) + 1

def s(x, p):            # parSign
    return -1 if (x % p) % 2 else 1

def chars(p):
    g = primitive_root(p)
    ind = {pow(g, j, p): j for j in range(p - 1)}
    def mk(j):
        return lambda x: 0 if x % p == 0 else cmath.exp(2j * cmath.pi * j * ind[x % p] / (p - 1))
    return mk

def half(p):            # 0 < n < p/2 (the n = 0 term vanishes)
    return range(1, (p - 1) // 2 + 1)

def fam(chi, e, a, p):
    return sum(chi(n) * (-1) ** (n + (a * pow(n, e, p)) % p) for n in half(p))

def G(psi, p):
    return sum(psi(x) * s(x, p) for x in range(1, p))

def T(psi, p):
    return sum(psi(x) * x for x in range(1, p))

def bandSumPow(chi, e, p):
    return sum(chi(n) * (-1) ** ((n ** e) // p) for n in half(p))

def close(a, b):
    return abs(a - b) < 1e-8

for p in primerange(3, 140):
    mk = chars(p)
    oddj = [j for j in range(p - 1) if j % 2 == 1]
    quad = lambda x: int(legendre_symbol(x % p, p)) if x % p else 0
    for j in range(p - 1):
        phi = mk(j)
        if j % 2 == 1:
            if not close(G(phi, p), 2 * sum(phi(n) * s(n, p) for n in half(p))): F('half1')
            if not close(G(phi, p), 2 * phi(2) * sum(phi(n) for n in half(p))): F('half2')
            if not close(p * G(phi, p), 2 * (1 - 2 * phi(2)) * T(phi, p)): F('bernoulli')
        else:
            if not close(G(phi, p), 0): F('even')
    for jc in oddj[:3]:
        chi = mk(jc)
        for m in range(0, 4):
            for jp in range(p - 1):
                psi, psiinv = mk(jp), mk(-jp)
                lhs = 2 * sum(psiinv(a) * fam(chi, 2 * m, a, p) for a in range(p))
                rhs = G(psiinv, p) * G(mk(jc + 2 * m * jp), p)
                if not close(lhs, rhs): F('mellin_forward')
            for a in (1, 2, p - 1):
                inv = sum(mk(j)(a) * G(mk(-j), p) * G(mk(jc + 2 * m * j), p) for j in oddj) / (2 * (p - 1))
                if not close(inv, fam(chi, 2 * m, a, p)): F('mellin_inverse')
            if m >= 1:
                if not close(fam(chi, 2 * m, 1, p), bandSumPow(chi, 2 * m, p)): F('parity_dictionary')
                if (p - 1) % (2 * m) == 0 or True:
                    if (2 * m) % (p - 1) == 0:
                        if not close(2 * bandSumPow(chi, 2 * m, p), -G(chi, p)): F('collapse1')
                    elif (4 * m) % (p - 1) == 0:
                        cq = lambda x, chi=chi: chi(x) * quad(x)
                        if not close(2 * bandSumPow(chi, 2 * m, p), -G(cq, p)): F('collapse2')
        bern = lambda f: T(f, p) / p
        for a in (1, 3):
            if a % p == 0: continue
            rhs = 2 / (p - 1) * sum(mk(j)(a) * (1 - 2 * mk(-j)(2)) * (1 - 2 * chi(2) * mk(j)(2) ** 2)
                                    * bern(mk(-j)) * bern(mk(jc + 2 * j)) for j in oddj)
            if not close(fam(chi, 2, a, p), rhs): F('mellin_bernoulli')
    # Parseval
    N = (p - 1) // 2
    tot = sum(abs(sum(mk(j)(n) * (-1) ** ((n * n) // p) for n in range(1, N + 1))) ** 2 for j in range(p - 1))
    if abs(tot - (p - 1) * N) > 1e-6: F('parseval')

# The quartic statements, exactly, at p = 5 (mod 8)
I = 1j
for p in primerange(13, 700):
    if p % 8 != 5: continue
    g = primitive_root(p); Q = (p - 1) // 4
    w = pow(g, Q, p)
    pw = {pow(w, j, p): j for j in range(4)}
    chi0 = {x: [1, I, -1, -I][pw[pow(x, Q, p)]] for x in range(1, p)}
    # both quartic characters; the pinned clauses are tested only for chi(2) = i
    for chi in (chi0, {x: chi0[x].conjugate() for x in chi0}):
        pinned = chi[2] == I
        c = lambda x: 0 if x % p == 0 else chi[x % p]
        if c(p - 1) != -1: F('odd')
        fib = lambda z: [x for x in range(1, p) if chi[x] == z]
        H = sorted(fib(1))
        if H != sorted({pow(y, 4, p) for y in range(1, p)}): F('fiber_one')
        if pinned and sorted(fib(I)) != sorted((2 * u) % p for u in H): F('fiber_gi')
        sig = lambda z: sum(s(x, p) for x in fib(z))
        A, B = sig(1), sig(I); gam = complex(A, B)
        if G(c, p) != 2 * gam: F('G_two_gamma')
        if pinned and p * gam != (1 - 2 * I) * T(c, p): F('gamma_bernoulli')
        famq = lambda a: sum(c(n) * (-1) ** (n + (a * n * n) % p) for n in half(p))
        for a in range(1, p):
            Cq = famq(a)
            if Cq.real != sum(s(u, p) * s(a * u * u, p) for u in fib(1)): F('coset_re')
            if Cq.imag != sum(s(u, p) * s(a * u * u, p) for u in fib(I)): F('coset_im')
        for cc in (1, I, -1, -I):
            tr = sum(famq(a) for a in fib(cc))
            if tr != (cc.conjugate() * gam).real * gam.conjugate(): F('coset_trace')
            if 2 * tr != cc.conjugate() * gam * gam.conjugate() + cc * gam.conjugate() ** 2: F('coset_trace2')
        tr1 = sum(famq(a) for a in H)
        if tr1.real != A * A or tr1.imag != -A * B: F('family_means')
        for a in H[:5]:
            ai = pow(a, p - 2, p)
            if famq(a).real != sum(s(ai * v, p) * s(ai * v * v, p) for v in H): F('conj_dynamics')
        M = lambda X, d: sum(s(u, p) * s(d * u, p) for u in X)
        if sum(famq(a).real ** 2 for a in H) != sum(M(H, d) * M(H, d * d) for d in H): F('secmom_re')
        if sum(famq(a).imag ** 2 for a in H) != sum(M(fib(I), d) * M(H, d * d) for d in H): F('secmom_im')
        for m in range(1, 2 * (p - 1)):
            if (4 * m) % (p - 1): continue
            val = bandSumPow(c, 2 * m, p)
            want = -gam if (2 * m) % (p - 1) == 0 else -gam.conjugate()
            if val != want: F('terminal')
        if p < 200:
            N = (p - 1) // 2
            eps = lambda n: (-1) ** ((n * n) // p)
            C = bandSumPow(c, 2, p); S = sum(c(n) for n in range(1, N + 1))
            if C != sum(c(n) * eps(n) for n in range(1, N + 1)): F('band_interval')
            pairs = [(a, b) for a in range(1, N + 1) for b in range(1, N + 1) if gcd(a, b) == 1]
            K = lambda a, b: range(1, N // max(a, b) + 1)
            leg = lambda r: int(legendre_symbol(r % p, p))
            r1 = sum(c(a) * c(b).conjugate() * sum(eps(a * r) for r in K(a, b)) for a, b in pairs)
            r2 = sum(c(a * b) * sum(leg(r) * eps(a * r) for r in K(a, b)) for a, b in pairs)
            r3 = sum(c(a) * c(b).conjugate() * sum(eps(a * r) * eps(b * r) for r in K(a, b)) for a, b in pairs)
            r4 = sum(c(a * b) * sum(leg(r) * eps(a * r) * eps(b * r) for r in K(a, b)) for a, b in pairs)
            if C * S.conjugate() != r1: F('pair1')
            if C * S != r2: F('pair2')
            if C * C.conjugate() != r3: F('pair3')
            if C * C != r4: F('pair4')

print("failures:", fails if fails else "none")
