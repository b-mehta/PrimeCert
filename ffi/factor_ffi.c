/*
 * FFI for Lean factor: GMP-optimized Pollard-Brent rho.
 * Declares GMP types/functions directly to avoid needing gmp.h dev headers.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

/* Minimal GMP declarations (enough for what we need) */
typedef struct {
    int _mp_alloc;
    int _mp_size;
    unsigned long *_mp_d;
} __mpz_struct;
typedef __mpz_struct mpz_t[1];

extern void __gmpz_init(mpz_t);
extern void __gmpz_init_set(mpz_t, const mpz_t);
extern void __gmpz_init_set_ui(mpz_t, unsigned long);
extern void __gmpz_clear(mpz_t);
extern void __gmpz_set(mpz_t, const mpz_t);
extern void __gmpz_set_ui(mpz_t, unsigned long);
extern unsigned long __gmpz_get_ui(const mpz_t);
extern int __gmpz_fits_ulong_p(const mpz_t);
extern int __gmpz_cmp(const mpz_t, const mpz_t);
extern int __gmpz_cmp_ui(const mpz_t, unsigned long);
extern int __gmpz_sgn(const mpz_t);
extern void __gmpz_add(mpz_t, const mpz_t, const mpz_t);
extern void __gmpz_sub(mpz_t, const mpz_t, const mpz_t);
extern void __gmpz_mul(mpz_t, const mpz_t, const mpz_t);
extern void __gmpz_mod(mpz_t, const mpz_t, const mpz_t);
extern void __gmpz_gcd(mpz_t, const mpz_t, const mpz_t);
extern void __gmpz_abs(mpz_t, const mpz_t);
extern int __gmpz_even_p_macro(const mpz_t);
extern int __gmpz_probab_prime_p(const mpz_t, int);
extern void __gmpz_mul_ui(mpz_t, const mpz_t, unsigned long);
extern void __gmpz_sub_ui(mpz_t, const mpz_t, unsigned long);
extern void __gmpz_add_ui(mpz_t, const mpz_t, unsigned long);
extern int __gmpz_invert(mpz_t, const mpz_t, const mpz_t);
extern size_t __gmpz_sizeinbase(const mpz_t, int);
extern void __gmpz_sqrt(mpz_t, const mpz_t);
extern void __gmpz_mul_si(mpz_t, const mpz_t, long);
extern long __gmpz_get_si(const mpz_t);
extern void __gmpz_set_si(mpz_t, long);
extern void __gmpz_fdiv_q_ui(mpz_t, const mpz_t, unsigned long);
extern unsigned long __gmpz_fdiv_r_ui(mpz_t, const mpz_t, unsigned long);
extern unsigned long __gmpz_tdiv_r_ui(mpz_t, const mpz_t, unsigned long);
extern void __gmpz_addmul_ui(mpz_t, const mpz_t, unsigned long);
extern void __gmpz_submul_ui(mpz_t, const mpz_t, unsigned long);
extern int __gmpz_perfect_square_p(const mpz_t);
extern void __gmpz_divexact_ui(mpz_t, const mpz_t, unsigned long);
extern int __gmpz_divisible_ui_p(const mpz_t, unsigned long);
extern unsigned long __gmpz_mod_ui(mpz_t, const mpz_t, unsigned long);
#define mpz_sizeinbase __gmpz_sizeinbase
#define mpz_sqrt __gmpz_sqrt
#define mpz_mul_si __gmpz_mul_si
#define mpz_get_si __gmpz_get_si
#define mpz_set_si __gmpz_set_si
#define mpz_fdiv_q_ui __gmpz_fdiv_q_ui
#define mpz_tdiv_r_ui __gmpz_tdiv_r_ui
#define mpz_addmul_ui __gmpz_addmul_ui
#define mpz_submul_ui __gmpz_submul_ui
#define mpz_perfect_square_p __gmpz_perfect_square_p
#define mpz_divexact_ui __gmpz_divexact_ui
#define mpz_divisible_ui_p __gmpz_divisible_ui_p
/* mpz_mod_ui: defined after macros below */
#define mpz_mod_ui(rop, op, d) mpz_mod_ui_impl(op, d)

#define mpz_init __gmpz_init
#define mpz_init_set __gmpz_init_set
#define mpz_init_set_ui __gmpz_init_set_ui
#define mpz_clear __gmpz_clear
#define mpz_set __gmpz_set
#define mpz_set_ui __gmpz_set_ui
#define mpz_get_ui __gmpz_get_ui
#define mpz_fits_ulong_p __gmpz_fits_ulong_p
#define mpz_cmp __gmpz_cmp
#define mpz_cmp_ui __gmpz_cmp_ui
#define mpz_add __gmpz_add
#define mpz_sub __gmpz_sub
#define mpz_mul __gmpz_mul
#define mpz_mod __gmpz_mod
#define mpz_gcd __gmpz_gcd
#define mpz_abs __gmpz_abs
#define mpz_probab_prime_p __gmpz_probab_prime_p
#define mpz_mul_ui __gmpz_mul_ui
#define mpz_sub_ui __gmpz_sub_ui
#define mpz_add_ui __gmpz_add_ui
#define mpz_invert __gmpz_invert
/* mpz_even_p is a macro in gmp.h; implement directly */
static inline int mpz_even_p(const mpz_t n) { return n[0]._mp_size == 0 || (n[0]._mp_d[0] & 1) == 0; }
static inline int mpz_sgn(const mpz_t n) { return n[0]._mp_size < 0 ? -1 : (n[0]._mp_size > 0 ? 1 : 0); }

static unsigned long mpz_mod_ui_impl(const mpz_t n, unsigned long d) {
    mpz_t tmp, dd;
    mpz_init(tmp); mpz_init_set_ui(dd, d);
    mpz_mod(tmp, n, dd);
    unsigned long r = mpz_get_ui(tmp);
    mpz_clear(tmp); mpz_clear(dd);
    return r;
}

/* Lean Nat <-> mpz conversion using official runtime API */
extern lean_object * lean_alloc_mpz(mpz_t);
extern void lean_extract_mpz_value(lean_object *, mpz_t);

static void lean_nat_to_mpz(mpz_t out, lean_object *n) {
    if (lean_is_scalar(n))
        mpz_set_ui(out, lean_unbox(n));
    else
        lean_extract_mpz_value(n, out);
}

static lean_obj_res mpz_to_lean_nat(const mpz_t v) {
    if (mpz_fits_ulong_p(v) && mpz_cmp_ui(v, LEAN_MAX_SMALL_NAT) <= 0)
        return lean_box(mpz_get_ui(v));
    mpz_t tmp;
    mpz_init_set(tmp, v);
    return lean_alloc_mpz(tmp); /* takes ownership of tmp */
}

/* PRNG — use simple counter-based sigma for ECM (good coverage) */
static uint64_t rng_s = 42;
static uint64_t rng(void) {
    /* LCG with good constants (Knuth) */
    rng_s = rng_s * 6364136223846793005ULL + 1442695040888963407ULL;
    return rng_s;
}

/* Pollard-Brent rho */
static int rho_mpz(mpz_t result, const mpz_t n) {
    if (mpz_even_p(n)) { mpz_set_ui(result, 2); return 1; }
    mpz_t y, c, x, ys, q, g, diff;
    mpz_init(y); mpz_init(c); mpz_init(x); mpz_init(ys);
    mpz_init(q); mpz_init(g); mpz_init(diff);
    int found = 0;
    int max_att = mpz_sizeinbase(n, 2) <= 100 ? 30 : 3;
    for (int att = 0; att < max_att && !found; att++) {
        mpz_set_ui(c, rng()); mpz_mod(c, c, n);
        if (!mpz_sgn(c)) mpz_set_ui(c, 1);
        mpz_set_ui(y, rng()); mpz_mod(y, y, n);
        mpz_set_ui(q, 1); mpz_set_ui(g, 1);
        unsigned long r = 1;
        while (!mpz_cmp_ui(g, 1)) {
            mpz_set(x, y);
            for (unsigned long i = 0; i < r; i++) {
                mpz_mul(y, y, y); mpz_add(y, y, c); mpz_mod(y, y, n);
            }
            unsigned long k = 0;
            while (k < r && !mpz_cmp_ui(g, 1)) {
                mpz_set(ys, y);
                unsigned long b = r - k; if (b > 128) b = 128;
                for (unsigned long i = 0; i < b; i++) {
                    mpz_mul(y, y, y); mpz_add(y, y, c); mpz_mod(y, y, n);
                    mpz_sub(diff, x, y); mpz_abs(diff, diff);
                    mpz_mul(q, q, diff); mpz_mod(q, q, n);
                }
                mpz_gcd(g, q, n); k += b;
            }
            r *= 2;
            if (r > 2000000) break;  /* cap ~6M iterations per attempt */
        }
        if (!mpz_cmp(g, n)) {
            mpz_set_ui(g, 1);
            while (!mpz_cmp_ui(g, 1)) {
                mpz_mul(ys, ys, ys); mpz_add(ys, ys, c); mpz_mod(ys, ys, n);
                mpz_sub(diff, x, ys); mpz_abs(diff, diff);
                mpz_gcd(g, diff, n);
            }
        }
        if (mpz_cmp_ui(g, 1) > 0 && mpz_cmp(g, n) != 0) { mpz_set(result, g); found = 1; }
    }
    mpz_clear(y); mpz_clear(c); mpz_clear(x); mpz_clear(ys);
    mpz_clear(q); mpz_clear(g); mpz_clear(diff);
    return found;
}

/* ECM (Elliptic Curve Method) using Montgomery curves */
/* Montgomery point: (X : Z) in projective coordinates */
typedef struct { mpz_t X, Z; } ecm_pt;

static void ecm_pt_init(ecm_pt *P) { mpz_init(P->X); mpz_init(P->Z); }
static void ecm_pt_clear(ecm_pt *P) { mpz_clear(P->X); mpz_clear(P->Z); }

/* Point doubling on Montgomery curve: By^2 = x^3 + Ax^2 + x */
static void ecm_double(ecm_pt *R, const ecm_pt *P, const mpz_t a24, const mpz_t n) {
    mpz_t u, v, t;
    mpz_init(u); mpz_init(v); mpz_init(t);
    mpz_add(u, P->X, P->Z); mpz_mul(u, u, u); mpz_mod(u, u, n);
    mpz_sub(v, P->X, P->Z); mpz_mul(v, v, v); mpz_mod(v, v, n);
    mpz_mul(R->X, u, v); mpz_mod(R->X, R->X, n);
    mpz_sub(t, u, v);
    mpz_mul(R->Z, a24, t); mpz_mod(R->Z, R->Z, n);
    mpz_add(R->Z, R->Z, v);
    mpz_mul(R->Z, R->Z, t); mpz_mod(R->Z, R->Z, n);
    mpz_clear(u); mpz_clear(v); mpz_clear(t);
}

/* Differential addition: R = P + Q given P - Q */
static void ecm_add(ecm_pt *R, const ecm_pt *P, const ecm_pt *Q, const ecm_pt *D, const mpz_t n) {
    mpz_t u, v, t1, t2;
    mpz_init(u); mpz_init(v); mpz_init(t1); mpz_init(t2);
    mpz_sub(u, P->X, P->Z); mpz_add(v, Q->X, Q->Z);
    mpz_mul(u, u, v); mpz_mod(u, u, n);
    mpz_add(v, P->X, P->Z); mpz_sub(t1, Q->X, Q->Z);
    mpz_mul(v, v, t1); mpz_mod(v, v, n);
    mpz_add(t1, u, v); mpz_mul(t1, t1, t1); mpz_mod(t1, t1, n);
    mpz_sub(t2, u, v); mpz_mul(t2, t2, t2); mpz_mod(t2, t2, n);
    mpz_mul(R->X, D->Z, t1); mpz_mod(R->X, R->X, n);
    mpz_mul(R->Z, D->X, t2); mpz_mod(R->Z, R->Z, n);
    mpz_clear(u); mpz_clear(v); mpz_clear(t1); mpz_clear(t2);
}

/* Montgomery ladder: compute k*P */
static void ecm_mul(ecm_pt *R, const ecm_pt *P, unsigned long k, const mpz_t a24, const mpz_t n) {
    if (k == 0) { mpz_set_ui(R->X, 0); mpz_set_ui(R->Z, 0); return; }
    ecm_pt Q, T;
    ecm_pt_init(&Q); ecm_pt_init(&T);
    mpz_set(R->X, P->X); mpz_set(R->Z, P->Z);
    ecm_double(&Q, P, a24, n);
    unsigned long bit = 1UL << 62;
    while (!(k & bit)) bit >>= 1;
    bit >>= 1;
    while (bit) {
        if (k & bit) {
            ecm_add(&T, &Q, R, P, n);
            mpz_set(R->X, T.X); mpz_set(R->Z, T.Z);
            ecm_double(&T, &Q, a24, n);
            mpz_set(Q.X, T.X); mpz_set(Q.Z, T.Z);
        } else {
            ecm_add(&T, R, &Q, P, n);
            mpz_set(Q.X, T.X); mpz_set(Q.Z, T.Z);
            ecm_double(&T, R, a24, n);
            mpz_set(R->X, T.X); mpz_set(R->Z, T.Z);
        }
        bit >>= 1;
    }
    ecm_pt_clear(&Q); ecm_pt_clear(&T);
}

/* Small primes for ECM stage 1 */
static int small_primes[] = {
    2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
    101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,
    211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,
    307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,
    401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,
    509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,
    641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,
    773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,
    907,911,919,929,937,941,947,953,967,971,977,983,991,997, 0
};

/* ECM: try one curve. Returns factor or sets result to 1 on failure. */
static int ecm_one_curve(mpz_t result, const mpz_t n, unsigned long B1, uint64_t sigma) {
    /* Suyama parameterization */
    mpz_t u, v, a, a24, t;
    mpz_init(u); mpz_init(v); mpz_init(a); mpz_init(a24); mpz_init(t);
    mpz_set_ui(u, sigma); mpz_mul_ui(u, u, sigma); mpz_sub_ui(u, u, 5); mpz_mod(u, u, n);
    mpz_set_ui(v, sigma); mpz_mul_ui(v, v, 4); mpz_mod(v, v, n);

    ecm_pt P;
    ecm_pt_init(&P);
    /* P.X = u^3, P.Z = v^3 */
    mpz_mul(P.X, u, u); mpz_mul(P.X, P.X, u); mpz_mod(P.X, P.X, n);
    mpz_mul(P.Z, v, v); mpz_mul(P.Z, P.Z, v); mpz_mod(P.Z, P.Z, n);

    /* a24 = (v-u)^3 * (3u+v) / (16*u^3*v) ... simplified: */
    mpz_sub(t, v, u); /* t = v - u */
    mpz_mul(a24, t, t); mpz_mul(a24, a24, t); mpz_mod(a24, a24, n); /* (v-u)^3 */
    mpz_mul_ui(t, u, 3); mpz_add(t, t, v); /* 3u + v */
    mpz_mul(a24, a24, t); mpz_mod(a24, a24, n);
    /* Divide by 16*u^3*v: compute inverse */
    mpz_mul(t, P.X, v); mpz_mul_ui(t, t, 16); mpz_mod(t, t, n);
    /* Check gcd before inversion */
    mpz_gcd(result, t, n);
    if (mpz_cmp_ui(result, 1) != 0 && mpz_cmp(result, n) != 0) {
        ecm_pt_clear(&P);
        mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
        return 1; /* lucky factor */
    }
    if (!mpz_cmp(result, n)) {
        ecm_pt_clear(&P);
        mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
        return 0; /* degenerate curve */
    }
    /* Modular inverse of t mod n */
    mpz_invert(t, t, n);
    mpz_mul(a24, a24, t); mpz_mod(a24, a24, n);
    /* a24 = (a+2)/4 */

    /* Stage 1: multiply P by all prime powers up to B1 */
    for (int i = 0; small_primes[i] && (unsigned long)small_primes[i] <= B1; i++) {
        unsigned long p = small_primes[i];
        unsigned long pp = p;
        while (pp <= B1 / p) pp *= p;
        ecm_mul(&P, &P, pp, a24, n);
    }
    /* Also handle primes beyond our table up to B1 */
    for (unsigned long p = 1009; p <= B1; p += 2) {
        /* Quick primality check */
        int is_p = 1;
        for (int d = 3; (unsigned long)d * d <= p; d += 2)
            if (p % d == 0) { is_p = 0; break; }
        if (!is_p) continue;
        unsigned long pp = p;
        while (pp <= B1 / p) pp *= p;
        ecm_mul(&P, &P, pp, a24, n);
    }

    mpz_gcd(result, P.Z, n);
    if (mpz_cmp_ui(result, 1) != 0 && mpz_cmp(result, n) != 0) {
        ecm_pt_clear(&P);
        mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
        return 1;
    }

    /* Stage 2: check for one large prime factor in group order in (B1, B2).
     * Iterate odd q from B1 to B2, computing q*P via differential addition
     * with step size 2, accumulating gcd. */
    unsigned long B2 = B1 * 10;
    ecm_pt P2, Q, Qprev, Tmp;
    ecm_pt_init(&P2); ecm_pt_init(&Q); ecm_pt_init(&Qprev); ecm_pt_init(&Tmp);
    ecm_double(&P2, &P, a24, n);
    unsigned long startQ = (B1 % 2 == 0) ? B1 + 1 : B1;
    ecm_mul(&Q, &P, startQ, a24, n);
    ecm_mul(&Qprev, &P, startQ - 2, a24, n);
    mpz_t acc;
    mpz_init_set_ui(acc, 1);
    for (unsigned long q = startQ; q <= B2; q += 2) {
        /* Quick primality check for q */
        int isp = 1;
        if (q > 3) for (unsigned long dd = 3; dd * dd <= q; dd += 2)
            if (q % dd == 0) { isp = 0; break; }
        if (isp) {
            mpz_mul(acc, acc, Q.Z); mpz_mod(acc, acc, n);
        }
        /* Advance: Q_{q+2} = Q_q + 2P with diff Q_{q-2} */
        ecm_add(&Tmp, &Q, &P2, &Qprev, n);
        mpz_set(Qprev.X, Q.X); mpz_set(Qprev.Z, Q.Z);
        mpz_set(Q.X, Tmp.X); mpz_set(Q.Z, Tmp.Z);
        /* Periodic GCD check */
        if ((q & 0x3FF) == 1) {
            mpz_gcd(result, acc, n);
            if (mpz_cmp_ui(result, 1) != 0 && mpz_cmp(result, n) != 0) {
                ecm_pt_clear(&P2); ecm_pt_clear(&Q); ecm_pt_clear(&Qprev); ecm_pt_clear(&Tmp);
                mpz_clear(acc); ecm_pt_clear(&P);
                mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
                return 1;
            }
            mpz_set_ui(acc, 1);
        }
    }
    mpz_gcd(result, acc, n);
    int found = mpz_cmp_ui(result, 1) != 0 && mpz_cmp(result, n) != 0;
    ecm_pt_clear(&P2); ecm_pt_clear(&Q); ecm_pt_clear(&Qprev); ecm_pt_clear(&Tmp);
    mpz_clear(acc); ecm_pt_clear(&P);
    mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
    return found;
}

/* Try ECM with multiple curves */
static int ecm_factor(mpz_t result, const mpz_t n, unsigned long B1, int curves) {
    for (int i = 0; i < curves; i++) {
        uint64_t sigma = rng() % 1000000 + 6;
        if (ecm_one_curve(result, n, B1, sigma)) return 1;
    }
    return 0;
}

/* ================================================================
 * Quadratic Sieve (single polynomial)
 * For balanced semiprimes in the 30-60 digit range.
 * ================================================================ */

#include <string.h>
#include <math.h>

/* Tonelli-Shanks: find r such that r^2 ≡ n (mod p). Assumes n is a QR mod p. */
static unsigned long tonelli_shanks(unsigned long n_mod, unsigned long p) {
    if (p == 2) return n_mod & 1;
    if (n_mod == 0) return 0;
    /* Find Q, S such that p-1 = Q * 2^S */
    unsigned long Q = p - 1, S = 0;
    while (!(Q & 1)) { Q >>= 1; S++; }
    if (S == 1) { /* p ≡ 3 (mod 4) */
        /* r = n^((p+1)/4) mod p */
        unsigned long r = 1, base = n_mod % p, exp = (p + 1) / 4;
        while (exp) { if (exp & 1) r = (unsigned __int128)r * base % p; base = (unsigned __int128)base * base % p; exp >>= 1; }
        return r;
    }
    /* Find a non-residue z */
    unsigned long z = 2;
    while (1) {
        unsigned long t = 1, b = z, e = (p - 1) / 2;
        while (e) { if (e & 1) t = (unsigned __int128)t * b % p; b = (unsigned __int128)b * b % p; e >>= 1; }
        if (t == p - 1) break;
        z++;
    }
    unsigned long M = S;
    /* c = z^Q mod p */
    unsigned long c = 1, base = z, exp = Q;
    while (exp) { if (exp & 1) c = (unsigned __int128)c * base % p; base = (unsigned __int128)base * base % p; exp >>= 1; }
    /* t = n^Q mod p */
    unsigned long t = 1; base = n_mod; exp = Q;
    while (exp) { if (exp & 1) t = (unsigned __int128)t * base % p; base = (unsigned __int128)base * base % p; exp >>= 1; }
    /* R = n^((Q+1)/2) mod p */
    unsigned long R = 1; base = n_mod; exp = (Q + 1) / 2;
    while (exp) { if (exp & 1) R = (unsigned __int128)R * base % p; base = (unsigned __int128)base * base % p; exp >>= 1; }
    while (1) {
        if (t == 1) return R;
        unsigned long i = 0, tmp = t;
        while (tmp != 1) { tmp = (unsigned __int128)tmp * tmp % p; i++; }
        unsigned long b2 = c;
        for (unsigned long j = 0; j < M - i - 1; j++) b2 = (unsigned __int128)b2 * b2 % p;
        M = i;
        c = (unsigned __int128)b2 * b2 % p;
        t = (unsigned __int128)t * c % p;
        R = (unsigned __int128)R * b2 % p;
    }
}

/* Legendre symbol (a/p) using Euler criterion */
static int legendre(unsigned long a, unsigned long p) {
    if (a == 0) return 0;
    unsigned long r = 1, base = a % p, exp = (p - 1) / 2;
    while (exp) { if (exp & 1) r = (unsigned __int128)r * base % p; base = (unsigned __int128)base * base % p; exp >>= 1; }
    return r == 1 ? 1 : -1;
}

#define QS_MAX_FB 8000      /* max factor base size */
#define QS_MAX_SMOOTH 9000  /* max smooth relations */

/* Bit matrix for GF(2) Gaussian elimination */
typedef struct {
    uint64_t *rows;  /* each row is ceil(ncols/64) uint64_t words */
    int nrows, ncols, words_per_row;
} bitmatrix;

static bitmatrix *bm_alloc(int nrows, int ncols) {
    bitmatrix *m = malloc(sizeof(bitmatrix));
    m->nrows = nrows; m->ncols = ncols;
    m->words_per_row = (ncols + 63) / 64;
    m->rows = calloc((size_t)nrows * m->words_per_row, sizeof(uint64_t));
    return m;
}
static void bm_free(bitmatrix *m) { free(m->rows); free(m); }
static void bm_set(bitmatrix *m, int r, int c) {
    m->rows[(size_t)r * m->words_per_row + c / 64] |= (1ULL << (c % 64));
}
static int bm_get(bitmatrix *m, int r, int c) {
    return (m->rows[(size_t)r * m->words_per_row + c / 64] >> (c % 64)) & 1;
}
static void bm_xor_row(bitmatrix *m, int dst, int src) {
    uint64_t *d = m->rows + (size_t)dst * m->words_per_row;
    uint64_t *s = m->rows + (size_t)src * m->words_per_row;
    for (int i = 0; i < m->words_per_row; i++) d[i] ^= s[i];
}

static int qs_factor(mpz_t result, const mpz_t n) {
    /* Check perfect square */
    if (mpz_perfect_square_p(n)) {
        mpz_sqrt(result, n);
        return 1;
    }

    /* Compute smoothness bound B ≈ exp(0.5 * sqrt(ln(n) * ln(ln(n)))) */
    double ln_n = mpz_sizeinbase(n, 2) * 0.693147;
    double ln_ln_n = log(ln_n);
    double B_d = exp(0.5 * sqrt(ln_n * ln_ln_n));
    unsigned long B = (unsigned long)B_d;
    if (B < 100) B = 100;
    if (B > 1000000) B = 1000000;

    /* Build factor base: primes p ≤ B where (n mod p) is a QR */
    unsigned long *fb = malloc(QS_MAX_FB * sizeof(unsigned long));
    unsigned long *fb_sqrt = malloc(QS_MAX_FB * sizeof(unsigned long)); /* sqrt(n) mod p */
    int fb_size = 0;
    /* fb[0] = placeholder for sign (-1), fb[1] = 2, rest = odd primes */
    fb[fb_size++] = 0; fb_sqrt[0] = 0; /* sign factor */
    fb[fb_size++] = 2; fb_sqrt[1] = 1;

    for (unsigned long p = 3; p <= B && fb_size < QS_MAX_FB; p += 2) {
        /* Quick primality check */
        int isp = 1;
        for (unsigned long d = 3; d * d <= p; d += 2)
            if (p % d == 0) { isp = 0; break; }
        if (!isp) continue;
        unsigned long n_mod_p = mpz_mod_ui(NULL, n, p);
        if (legendre(n_mod_p, p) == 1) {
            fb[fb_size] = p;
            fb_sqrt[fb_size] = tonelli_shanks(n_mod_p, p);
            fb_size++;
        }
    }

    int needed = fb_size + 50; /* extra relations → more null vectors → better chance */

    /* Sieve: Q(x) = (x + floor(sqrt(n)))^2 - n for x in [-M, M] */
    mpz_t sqrt_n, x_val, q_val, tmp;
    mpz_init(sqrt_n); mpz_init(x_val); mpz_init(q_val); mpz_init(tmp);
    mpz_sqrt(sqrt_n, n);

    /* M needs to be large enough to find fb_size+1 smooth relations.
     * Heuristic: M ≈ fb_size * exp(u) where u = ln(Q(M))/ln(B) */
    long M = (long)B * 1000;
    if (M < 1000000) M = 1000000;
    if (M > 50000000) M = 50000000;

    /* Sieve array: log approximations */
    double *sieve = calloc(2 * M + 1, sizeof(double));
    double threshold;
    {
        /* threshold ≈ log2(Q(M)) - some slack */
        mpz_set_si(x_val, M);
        mpz_add(x_val, x_val, sqrt_n);
        mpz_mul(q_val, x_val, x_val);
        mpz_sub(q_val, q_val, n);
        threshold = mpz_sizeinbase(q_val, 2) * 0.693147 - 30.0;
    }

    /* Sieve with each factor base prime.
     * For prime p with sqrt(n) ≡ r (mod p), Q(x) = (x+sqrt_n)^2 - n ≡ 0 (mod p)
     * when x+sqrt_n ≡ ±r (mod p), i.e., x ≡ ±r - sqrt_n (mod p). */
    for (int i = 1; i < fb_size; i++) {
        unsigned long p = fb[i];
        unsigned long r = fb_sqrt[i];
        double logp = log((double)p);
        unsigned long sn_mod_p = mpz_mod_ui_impl(sqrt_n, p);

        /* Two starting residues mod p */
        long s1 = ((long)r - (long)sn_mod_p % (long)p + (long)p) % (long)p;
        long s2 = ((long)p - (long)r - (long)sn_mod_p % (long)p + 2*(long)p) % (long)p;

        /* Find first x >= -M with x ≡ s (mod p) */
        for (int si = 0; si < 2; si++) {
            long s = si == 0 ? s1 : s2;
            long x = -M + ((s - (-M % (long)p) + (long)p) % (long)p);
            if (x < -M) x += p;
            for (; x <= M; x += p)
                sieve[x + M] += logp;
        }
    }

    /* Collect smooth relations by trial division */
    /* (debug removed) */

    /* Collect smooth relations by trial division */
    int nsmooth = 0;
    /* Store: for each smooth relation, the exponent vector and the x value */
    int (*exponents)[QS_MAX_FB] = malloc(QS_MAX_SMOOTH * sizeof(*exponents));
    long *x_values = malloc(QS_MAX_SMOOTH * sizeof(long));

    for (long x = -M; x <= M && nsmooth < needed; x++) {
        if (sieve[x + M] < threshold) continue;

        /* Compute Q(x) = (x + sqrt_n)^2 - n */
        mpz_set_si(x_val, x);
        mpz_add(x_val, x_val, sqrt_n);
        mpz_mul(q_val, x_val, x_val);
        mpz_sub(q_val, q_val, n);

        /* Trial divide by factor base */
        int smooth = 1;
        memset(exponents[nsmooth], 0, fb_size * sizeof(int));

        /* Handle sign */
        if (mpz_cmp_ui(q_val, 0) < 0) {
            mpz_abs(q_val, q_val);
            exponents[nsmooth][0] = 1; /* sign bit in position 0 */
        }

        mpz_set(tmp, q_val);
        for (int i = 1; i < fb_size; i++) {
            unsigned long p = fb[i];
            while (mpz_divisible_ui_p(tmp, p)) {
                mpz_divexact_ui(tmp, tmp, p);
                exponents[nsmooth][i]++;
            }
        }
        /* Also divide by 2 */
        while (mpz_divisible_ui_p(tmp, 2)) {
            mpz_divexact_ui(tmp, tmp, 2);
            /* factor 2 is at index 0 but we used it for sign... skip for now */
        }

        if (mpz_cmp_ui(tmp, 1) == 0) {
            x_values[nsmooth] = x;
            nsmooth++;
        }
    }

    free(sieve);

    
    if (nsmooth < fb_size + 1) {
        /* Not enough smooth relations */
        free(fb); free(fb_sqrt); free(exponents); free(x_values);
        mpz_clear(sqrt_n); mpz_clear(x_val); mpz_clear(q_val); mpz_clear(tmp);
        return 0;
    }

    /* GF(2) Gaussian elimination to find a dependency */
    bitmatrix *mat = bm_alloc(nsmooth, fb_size);
    bitmatrix *hist = bm_alloc(nsmooth, nsmooth); /* track which rows were combined */

    for (int i = 0; i < nsmooth; i++) {
        for (int j = 0; j < fb_size; j++)
            if (exponents[i][j] & 1) bm_set(mat, i, j);
        bm_set(hist, i, i); /* identity */
    }

    

    /* Row reduce */
    int *pivot_row = malloc(fb_size * sizeof(int));
    for (int i = 0; i < fb_size; i++) pivot_row[i] = -1;

    for (int col = 0; col < fb_size; col++) {
        int prow = -1;
        for (int row = 0; row < nsmooth; row++) {
            if (!bm_get(mat, row, col)) continue;
            int ok = 1;
            for (int c2 = 0; c2 < col; c2++)
                if (bm_get(mat, row, c2)) { ok = 0; break; }
            if (ok) { prow = row; break; }
        }
        if (prow == -1) continue;
        pivot_row[col] = prow;
        for (int row = 0; row < nsmooth; row++) {
            if (row != prow && bm_get(mat, row, col)) {
                bm_xor_row(mat, row, prow);
                bm_xor_row(hist, row, prow);
            }
        }
    }

    /* Find a zero row in mat → dependency */
    int found = 0;
    for (int row = 0; row < nsmooth && !found; row++) {
        int is_zero = 1;
        for (int j = 0; j < mat->words_per_row; j++)
            if (mat->rows[(size_t)row * mat->words_per_row + j]) { is_zero = 0; break; }
        if (!is_zero) continue;

        /* Compute x = product of (x_i + sqrt_n), y = sqrt of product of Q(x_i) */
        mpz_t X, Y, qi;
        mpz_init_set_ui(X, 1);
        mpz_init_set_ui(Y, 1);
        mpz_init(qi);

        /* Accumulate exponents */
        int *total_exp = calloc(fb_size, sizeof(int));

        for (int i = 0; i < nsmooth; i++) {
            if (!bm_get(hist, row, i)) continue;
            /* X *= (x_i + sqrt_n) mod n */
            mpz_set_si(tmp, x_values[i]);
            mpz_add(tmp, tmp, sqrt_n);
            mpz_mul(X, X, tmp);
            mpz_mod(X, X, n);
            /* Accumulate exponents */
            for (int j = 0; j < fb_size; j++)
                total_exp[j] += exponents[i][j];
        }

        /* Y = product of fb[j]^(total_exp[j]/2) mod n — use powmod */
        for (int j = 1; j < fb_size; j++) {
            if (total_exp[j] == 0) continue;
            unsigned long p = fb[j];
            unsigned long half = total_exp[j] / 2;
            /* Compute p^half mod n via binary exponentiation */
            mpz_t base_p, pow_p;
            mpz_init_set_ui(base_p, p);
            mpz_init(pow_p);
            mpz_set_ui(pow_p, 1);
            mpz_t b; mpz_init_set_ui(b, p);
            unsigned long e = half;
            while (e) {
                if (e & 1) { mpz_mul(pow_p, pow_p, b); mpz_mod(pow_p, pow_p, n); }
                mpz_mul(b, b, b); mpz_mod(b, b, n);
                e >>= 1;
            }
            mpz_mul(Y, Y, pow_p); mpz_mod(Y, Y, n);
            mpz_clear(base_p); mpz_clear(pow_p); mpz_clear(b);
        }

        /* Factor = gcd(X - Y, n) */
        mpz_sub(tmp, X, Y);
        mpz_abs(tmp, tmp);
        mpz_gcd(result, tmp, n);

        
        if (mpz_cmp_ui(result, 1) > 0 && mpz_cmp(result, n) != 0) {
            
            found = 1;
        }

        free(total_exp);
        mpz_clear(X); mpz_clear(Y); mpz_clear(qi);
    }

    bm_free(mat); bm_free(hist);
    free(pivot_row); free(fb); free(fb_sqrt); free(exponents); free(x_values);
    mpz_clear(sqrt_n); mpz_clear(x_val); mpz_clear(q_val); mpz_clear(tmp);
    return found;
}

/* Combined factoring: rho first (fast for small factors), then ECM */
static int combined_factor(mpz_t result, const mpz_t n) {
    if (rho_mpz(result, n)) return 1;
    /* Try QS for balanced semiprimes (30-70 digits) */
    if (mpz_sizeinbase(n, 10) >= 25 && mpz_sizeinbase(n, 10) <= 70) {
        if (qs_factor(result, n)) return 1;
    }
    /* Escalating ECM */
    static const struct { unsigned long B1; int curves; } ecm_params[] = {
        {2000, 25}, {10000, 200}, {50000, 300}, {250000, 500}, {1000000, 1000}, {0, 0}
    };
    for (int i = 0; ecm_params[i].B1; i++)
        if (ecm_factor(result, n, ecm_params[i].B1, ecm_params[i].curves)) return 1;
    return 0;
}

LEAN_EXPORT lean_obj_res lean_factor_rho(b_lean_obj_arg n_lean) {
    mpz_t n, result;
    mpz_init(n); mpz_init(result);
    lean_nat_to_mpz(n, n_lean);
    int ok = combined_factor(result, n);
    lean_obj_res ret;
    if (ok) {
        lean_obj_res val = mpz_to_lean_nat(result);
        ret = lean_alloc_ctor(1, 1, 0); /* Option.some */
        lean_ctor_set(ret, 0, val);
    } else {
        ret = lean_box(0); /* Option.none */
    }
    mpz_clear(n); mpz_clear(result);
    return ret;
}

LEAN_EXPORT uint8_t lean_is_prime_gmp(b_lean_obj_arg n_lean) {
    mpz_t n;
    mpz_init(n);
    lean_nat_to_mpz(n, n_lean);
    int r = mpz_probab_prime_p(n, 25);
    mpz_clear(n);
    return r > 0 ? 1 : 0;
}
