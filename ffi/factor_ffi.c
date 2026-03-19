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
extern void __gmpz_submul(mpz_t, const mpz_t, const mpz_t);
extern int __gmpz_perfect_square_p(const mpz_t);
extern void __gmpz_divexact_ui(mpz_t, const mpz_t, unsigned long);
extern int __gmpz_divisible_ui_p(const mpz_t, unsigned long);
extern unsigned long __gmpz_mod_ui(mpz_t, const mpz_t, unsigned long);
extern void __gmpz_neg(mpz_t, const mpz_t);
extern void __gmpz_fdiv_q(mpz_t, const mpz_t, const mpz_t);
extern void __gmpz_mul_2exp(mpz_t, const mpz_t, unsigned long);
#define mpz_neg __gmpz_neg
#define mpz_fdiv_q __gmpz_fdiv_q
#define mpz_mul_2exp __gmpz_mul_2exp
#define mpz_sizeinbase __gmpz_sizeinbase
#define mpz_sqrt __gmpz_sqrt
#define mpz_mul_si __gmpz_mul_si
#define mpz_get_si __gmpz_get_si
#define mpz_set_si __gmpz_set_si
#define mpz_fdiv_q_ui __gmpz_fdiv_q_ui
#define mpz_tdiv_r_ui __gmpz_tdiv_r_ui
#define mpz_addmul_ui __gmpz_addmul_ui
#define mpz_submul_ui __gmpz_submul_ui
#define mpz_submul __gmpz_submul
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
    /* Save a copy of P since R may alias P */
    ecm_pt P0, Q, T;
    ecm_pt_init(&P0); ecm_pt_init(&Q); ecm_pt_init(&T);
    mpz_set(P0.X, P->X); mpz_set(P0.Z, P->Z);
    mpz_set(R->X, P->X); mpz_set(R->Z, P->Z);
    ecm_double(&Q, &P0, a24, n);
    unsigned long bit = 1UL << 62;
    while (!(k & bit)) bit >>= 1;
    bit >>= 1;
    while (bit) {
        if (k & bit) {
            ecm_add(&T, &Q, R, &P0, n);
            mpz_set(R->X, T.X); mpz_set(R->Z, T.Z);
            ecm_double(&T, &Q, a24, n);
            mpz_set(Q.X, T.X); mpz_set(Q.Z, T.Z);
        } else {
            ecm_add(&T, R, &Q, &P0, n);
            mpz_set(Q.X, T.X); mpz_set(Q.Z, T.Z);
            ecm_double(&T, R, a24, n);
            mpz_set(R->X, T.X); mpz_set(R->Z, T.Z);
        }
        bit >>= 1;
    }
    ecm_pt_clear(&P0); ecm_pt_clear(&Q); ecm_pt_clear(&T);
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

    /* Stage 2: Baby-step Giant-step.
     * Choose step D (even). Precompute baby[i] = (2i+1)*P for i=0..D/2-1.
     * For each giant step j, compute G = j*D*P, accumulate ∏(G.X - baby[i].X).
     * Check gcd periodically. This is O(D + (B2-B1)/D) point ops instead of O(B2-B1). */
    unsigned long B2 = B1 * 50;
    /* D ≈ √(B2-B1), rounded to multiple of 30 for wheel factorization */
    unsigned long range = B2 - B1;
    unsigned long D = 30;
    while (D * D < range) D += 30;
    if (D > 2310) D = 2310;  /* cap at primorial(11) */

    /* Baby steps: compute d*P for odd d = 1, 3, 5, ..., D-1 */
    int nbaby = D / 2;
    mpz_t *baby_x = malloc(nbaby * sizeof(mpz_t));
    for (int i = 0; i < nbaby; i++) mpz_init(baby_x[i]);
    {
        ecm_pt Bp, Bp_prev, P2b, Tmpb;
        ecm_pt_init(&Bp); ecm_pt_init(&Bp_prev); ecm_pt_init(&P2b); ecm_pt_init(&Tmpb);
        ecm_double(&P2b, &P, a24, n);
        /* Bp = 1*P */
        mpz_set(Bp.X, P.X); mpz_set(Bp.Z, P.Z);
        /* Compute X/Z for normalization: store X*Z^(-1) mod n would be ideal,
         * but for simplicity just store X and Z separately and compare X*Z' = X'*Z */
        mpz_set(baby_x[0], Bp.X);  /* baby[0] = P.X (we'll compare X*Z - X'*Z) */
        /* Actually, for the comparison we need X/Z. But modular inverse per baby is expensive.
         * Instead: accumulate ∏(G.X * baby[i].Z - G.Z * baby[i].X) */
        /* Let's store both X and Z for each baby step */
        mpz_t *baby_z = malloc(nbaby * sizeof(mpz_t));
        for (int i = 0; i < nbaby; i++) mpz_init(baby_z[i]);
        mpz_set(baby_x[0], P.X); mpz_set(baby_z[0], P.Z);
        /* Bp_prev = -1*P (same as P, differential add needs P-2P = -P which has same X,Z) */
        /* For differential chain: compute 3P = 2P + P (diff P), 5P = 3P + 2P (diff P), etc. */
        ecm_pt Bcur, Bprev;
        ecm_pt_init(&Bcur); ecm_pt_init(&Bprev);
        mpz_set(Bprev.X, P.X); mpz_set(Bprev.Z, P.Z); /* 1*P */
        ecm_add(&Bcur, &P2b, &P, &P, n); /* 3*P = 2P + P (diff P) */
        mpz_set(baby_x[1], Bcur.X); mpz_set(baby_z[1], Bcur.Z);
        for (int i = 2; i < nbaby; i++) {
            ecm_add(&Tmpb, &Bcur, &P2b, &Bprev, n); /* (2i+1)*P = (2i-1)*P + 2P (diff (2i-3)*P) */
            mpz_set(Bprev.X, Bcur.X); mpz_set(Bprev.Z, Bcur.Z);
            mpz_set(Bcur.X, Tmpb.X); mpz_set(Bcur.Z, Tmpb.Z);
            mpz_set(baby_x[i], Bcur.X); mpz_set(baby_z[i], Bcur.Z);
        }
        ecm_pt_clear(&Bp); ecm_pt_clear(&Bp_prev); ecm_pt_clear(&P2b); ecm_pt_clear(&Tmpb);
        ecm_pt_clear(&Bcur); ecm_pt_clear(&Bprev);

        /* Giant steps: G_j = j*D*P for j = ceil(B1/D), ceil(B1/D)+1, ..., ceil(B2/D) */
        ecm_pt G, G_prev, DP, Gtmp;
        ecm_pt_init(&G); ecm_pt_init(&G_prev); ecm_pt_init(&DP); ecm_pt_init(&Gtmp);
        ecm_mul(&DP, &P, D, a24, n);  /* D*P */
        unsigned long j_start = (B1 / D) + 1;
        unsigned long j_end = (B2 / D) + 1;
        ecm_mul(&G, &P, j_start * D, a24, n);
        ecm_mul(&G_prev, &P, (j_start - 1) * D, a24, n);

        mpz_t acc, diff_xz;
        mpz_init_set_ui(acc, 1);
        mpz_init(diff_xz);

        for (unsigned long j = j_start; j <= j_end; j++) {
            /* For each baby step i, check if j*D ± (2i+1) hits a prime.
             * Accumulate ∏(G.X * baby_z[i] - G.Z * baby_x[i]) */
            for (int i = 0; i < nbaby; i++) {
                /* diff = G.X * baby_z[i] - G.Z * baby_x[i] */
                mpz_mul(diff_xz, G.X, baby_z[i]);
                mpz_submul(diff_xz, G.Z, baby_x[i]);
                mpz_mod(diff_xz, diff_xz, n);
                mpz_mul(acc, acc, diff_xz);
                mpz_mod(acc, acc, n);
            }
            /* Advance giant step: G_{j+1} = G_j + D*P (diff G_{j-1}) */
            ecm_add(&Gtmp, &G, &DP, &G_prev, n);
            mpz_set(G_prev.X, G.X); mpz_set(G_prev.Z, G.Z);
            mpz_set(G.X, Gtmp.X); mpz_set(G.Z, Gtmp.Z);
            /* Periodic GCD */
            if ((j & 0xF) == 0) {
                mpz_gcd(result, acc, n);
                if (mpz_cmp_ui(result, 1) != 0 && mpz_cmp(result, n) != 0) {
                    /* Found! Clean up and return. */
                    for (int i = 0; i < nbaby; i++) { mpz_clear(baby_x[i]); mpz_clear(baby_z[i]); }
                    free(baby_x); free(baby_z);
                    mpz_clear(acc); mpz_clear(diff_xz);
                    ecm_pt_clear(&G); ecm_pt_clear(&G_prev); ecm_pt_clear(&DP); ecm_pt_clear(&Gtmp);
                    ecm_pt_clear(&P);
                    mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
                    return 1;
                }
                mpz_set_ui(acc, 1);
            }
        }
        mpz_gcd(result, acc, n);
        int found2 = mpz_cmp_ui(result, 1) != 0 && mpz_cmp(result, n) != 0;
        for (int i = 0; i < nbaby; i++) { mpz_clear(baby_x[i]); mpz_clear(baby_z[i]); }
        free(baby_x); free(baby_z);
        mpz_clear(acc); mpz_clear(diff_xz);
        ecm_pt_clear(&G); ecm_pt_clear(&G_prev); ecm_pt_clear(&DP); ecm_pt_clear(&Gtmp);
        ecm_pt_clear(&P);
        mpz_clear(u); mpz_clear(v); mpz_clear(a); mpz_clear(a24); mpz_clear(t);
        return found2;
    }
}

/* Try ECM with multiple curves */
static unsigned long ecm_sigma_counter = 6;
static int ecm_factor(mpz_t result, const mpz_t n, unsigned long B1, int curves) {
    for (int i = 0; i < curves; i++) {
        if (ecm_one_curve(result, n, B1, ecm_sigma_counter++)) return 1;
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
    long M = (long)B * 5000;
    if (M < 2000000) M = 2000000;
    if (M > 100000000) M = 100000000;

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

/* ================================================================
 * Self-Initializing Quadratic Sieve (SIQS)
 * For balanced semiprimes in the 42-60 digit range.
 * Uses multiple polynomials Q(x) = (a*x + b)^2 - n.
 * ================================================================ */

/* Modular inverse mod prime (via Fermat's little theorem) */
static unsigned long mod_inv(unsigned long a, unsigned long p) {
    unsigned long r = 1, base = a % p, exp = p - 2;
    while (exp) {
        if (exp & 1) r = (unsigned __int128)r * base % p;
        base = (unsigned __int128)base * base % p;
        exp >>= 1;
    }
    return r;
}

static int siqs_factor(mpz_t result, const mpz_t n) {
    if (mpz_perfect_square_p(n)) { mpz_sqrt(result, n); return 1; }

    size_t ndig = mpz_sizeinbase(n, 10);
    double ln_n = mpz_sizeinbase(n, 2) * 0.693147;

    /* Tuned parameters per digit range (from msieve/yafu experience).
     * fb_target = desired factor base size, M = sieve half-width. */
    int fb_target;
    long M;
    if      (ndig <= 30) { fb_target = 200;  M = 16384; }
    else if (ndig <= 34) { fb_target = 400;  M = 32768; }
    else if (ndig <= 38) { fb_target = 600;  M = 32768; }
    else if (ndig <= 42) { fb_target = 900;  M = 65536; }
    else if (ndig <= 46) { fb_target = 1400; M = 65536; }
    else if (ndig <= 52) { fb_target = 2000; M = 65536; }
    else if (ndig <= 58) { fb_target = 3000; M = 65536; }
    else                 { fb_target = 4500; M = 65536; }

    /* Build factor base — collect primes where n is a QR */
    unsigned long *fb = malloc(QS_MAX_FB * sizeof(unsigned long));
    unsigned long *fb_sqrt = malloc(QS_MAX_FB * sizeof(unsigned long));
    int fb_size = 0;
    fb[fb_size++] = 0; fb_sqrt[0] = 0; /* sign factor */
    fb[fb_size++] = 2; fb_sqrt[1] = 1;

    for (unsigned long p = 3; fb_size < fb_target; p += 2) {
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

    int needed = fb_size + 20;

    /* Compute s from target_a = sqrt(2n)/M */
    mpz_t check_a;
    mpz_init(check_a);
    mpz_mul_2exp(check_a, n, 1);
    mpz_sqrt(check_a, check_a);
    mpz_fdiv_q_ui(check_a, check_a, (unsigned long)M);
    double log_target_a = mpz_sizeinbase(check_a, 2) * 0.693147;
    int mid = fb_size / 2;
    if (mid < 2) mid = 2;
    double avg_log_prime = log((double)fb[mid]);
    int s = (int)(log_target_a / avg_log_prime + 0.5);
    if (s < 3) s = 3;
    if (s > 10) s = 10;
    mpz_clear(check_a);
    mpz_t target_a, sqrt_2n, tmp_z;
    mpz_init(target_a); mpz_init(sqrt_2n); mpz_init(tmp_z);

    /* Allocate relation storage */
    int (*exponents)[QS_MAX_FB] = malloc(QS_MAX_SMOOTH * sizeof(*exponents));
    mpz_t *ax_plus_b = malloc(QS_MAX_SMOOTH * sizeof(mpz_t));
    for (int i = 0; i < QS_MAX_SMOOTH; i++) mpz_init(ax_plus_b[i]);
    int nsmooth = 0;

    /* Sieve array */
    long sieve_len = 2 * M + 1;
    unsigned char *sieve = malloc(sieve_len);

    /* Precompute scaled log of each factor base prime (fit in byte) */
    unsigned char *fb_logb = malloc(fb_size);
    for (int i = 0; i < fb_size; i++)
        fb_logb[i] = (i <= 1) ? 0 : (unsigned char)(log((double)fb[i]) / log(2.0) * 4 + 0.5);

    /* Large prime bound for single-large-prime variation */
    unsigned long lp_bound = (unsigned long)fb[fb_size - 1] * fb[fb_size - 1];
    /* Hash table for partial relation matching */
    #define LP_HASH_SIZE 65536
    #define LP_HASH_MASK (LP_HASH_SIZE - 1)
    typedef struct lp_entry { unsigned long lp; int exp_idx; struct lp_entry *next; } lp_entry_t;
    lp_entry_t **lp_hash = calloc(LP_HASH_SIZE, sizeof(lp_entry_t *));
    lp_entry_t *lp_pool = malloc(50000 * sizeof(lp_entry_t));
    int lp_pool_used = 0;
    int npartials = 0;

    /* Temp mpz for trial division */
    mpz_t q_val, a_mpz, b_mpz, x_val, tmp2;
    mpz_init(q_val); mpz_init(a_mpz); mpz_init(b_mpz);
    mpz_init(x_val); mpz_init(tmp2);

    /* Generate polynomials and sieve — Gray code for multiple b per a */
    int max_a_values = 10000;
    int a_count = 0;
    int poly_count = 0;
    int a_idx[12];
    int npolys_per_a = (1 << (s - 1)) - 1; /* 2^(s-1) - 1 polynomials per a */
    mpz_t Bj[12]; /* Bj[j] = sqrt(n) * (a/pj)^(-1) mod a, scaled */
    for (int i = 0; i < 12; i++) mpz_init(Bj[i]);

    /* Pre-allocate per-a arrays (reuse across iterations) */
    unsigned long *a_inv_p = malloc(fb_size * sizeof(unsigned long));
    unsigned long **Bj_mod_p = malloc(12 * sizeof(unsigned long *));
    for (int j = 0; j < 12; j++) Bj_mod_p[j] = malloc(fb_size * sizeof(unsigned long));
    unsigned long *soln1 = malloc(fb_size * sizeof(unsigned long));
    unsigned long *soln2 = malloc(fb_size * sizeof(unsigned long));
    int *in_a_flag = malloc(fb_size * sizeof(int));

    while (nsmooth < needed && a_count < max_a_values) {
        /* Choose s primes from factor base for a */
        int lo = fb_size / 4;
        if (lo < 3) lo = 3;
        int hi = 3 * fb_size / 4;
        if (hi <= lo + s) hi = lo + s + 5;
        if (hi > fb_size) hi = fb_size;

        for (int i = 0; i < s; i++) {
            int idx, retry;
            do {
                retry = 0;
                idx = lo + (int)(rng() % (unsigned long)(hi - lo));
                for (int j = 0; j < i; j++)
                    if (a_idx[j] == idx) { retry = 1; break; }
            } while (retry);
            a_idx[i] = idx;
        }

        mpz_set_ui(a_mpz, 1);
        for (int i = 0; i < s; i++)
            mpz_mul_ui(a_mpz, a_mpz, fb[a_idx[i]]);

        /* Compute Bj[j] for each factor pj of a:
         * Bj[j] = sqrt(n) mod pj * (a/pj)^(-1) mod pj * (a/pj) */
        for (int j = 0; j < s; j++) {
            unsigned long pj = fb[a_idx[j]];
            unsigned long rj = fb_sqrt[a_idx[j]];
            mpz_fdiv_q_ui(tmp_z, a_mpz, pj);
            unsigned long apj_mod = mpz_mod_ui(NULL, tmp_z, pj);
            unsigned long apj_inv = mod_inv(apj_mod, pj);
            unsigned long coeff = (unsigned __int128)rj * apj_inv % pj;
            mpz_mul_ui(Bj[j], tmp_z, coeff);
        }

        /* Initial b = B1 + B2 + ... + Bs (all positive signs) */
        mpz_set_ui(b_mpz, 0);
        for (int j = 0; j < s; j++)
            mpz_add(b_mpz, b_mpz, Bj[j]);
        mpz_mod(b_mpz, b_mpz, a_mpz);
        mpz_fdiv_q_ui(tmp_z, a_mpz, 2);
        if (mpz_cmp(b_mpz, tmp_z) > 0)
            mpz_sub(b_mpz, a_mpz, b_mpz);

        /* Verify b^2 ≡ n (mod a) */
        mpz_mul(tmp_z, b_mpz, b_mpz);
        mpz_sub(tmp_z, tmp_z, n);
        mpz_mod(tmp_z, tmp_z, a_mpz);
        if (mpz_sgn(tmp_z) != 0) { a_count++; continue; }

        /* Precompute a_inv and Bj mod p for each fb prime — ONCE per a value */
        memset(in_a_flag, 0, fb_size * sizeof(int));

        for (int i = 2; i < fb_size; i++) {
            unsigned long p = fb[i];
            for (int j = 0; j < s; j++)
                if (fb[a_idx[j]] == p) { in_a_flag[i] = 1; break; }
            if (in_a_flag[i]) { a_inv_p[i] = 0; continue; }
            unsigned long a_mod_p = mpz_mod_ui(NULL, a_mpz, p);
            a_inv_p[i] = mod_inv(a_mod_p, p);
            for (int j = 0; j < s; j++)
                Bj_mod_p[j][i] = mpz_mod_ui(NULL, Bj[j], p);
        }

        /* Gray code: iterate through 2^(s-1)-1 polynomials */
        for (int pidx = 0; pidx <= npolys_per_a && nsmooth < needed; pidx++) {
            if (pidx > 0) {
                int F = pidx, jj = 0;
                while ((F & 1) == 0) { F >>= 1; jj++; }
                int polyadd = (F & 2) != 0;
                /* Update b */
                if (polyadd) {
                    mpz_add(b_mpz, b_mpz, Bj[jj]);
                    mpz_add(b_mpz, b_mpz, Bj[jj]);
                } else {
                    mpz_sub(b_mpz, b_mpz, Bj[jj]);
                    mpz_sub(b_mpz, b_mpz, Bj[jj]);
                }
                /* Incrementally update sieve positions:
                 * soln_new = soln_old ± 2*Bj_mod_p[jj] * a_inv mod p */
                for (int i = 2; i < fb_size; i++) {
                    if (in_a_flag[i]) continue;
                    unsigned long p = fb[i];
                    unsigned long shift = (unsigned __int128)2 * Bj_mod_p[jj][i] % p * a_inv_p[i] % p;
                    if (polyadd) {
                        soln1[i] = (soln1[i] + p - shift) % p;
                        soln2[i] = (soln2[i] + p - shift) % p;
                    } else {
                        soln1[i] = (soln1[i] + shift) % p;
                        soln2[i] = (soln2[i] + shift) % p;
                    }
                }
            } else {
                /* First polynomial: compute sieve positions from scratch */
                for (int i = 2; i < fb_size; i++) {
                    if (in_a_flag[i]) { soln1[i] = soln2[i] = fb[i]; continue; }
                    unsigned long p = fb[i];
                    unsigned long r = fb_sqrt[i];
                    unsigned long b_mod_p = mpz_mod_ui(NULL, b_mpz, p);
                    soln1[i] = (unsigned __int128)(r + p - b_mod_p) % p * a_inv_p[i] % p;
                    soln2[i] = (unsigned __int128)(p - r + p - b_mod_p) % p * a_inv_p[i] % p;
                }
            }

        /* Sieve (byte array — fast memset and cache-friendly) */
        memset(sieve, 0, sieve_len);
        for (int i = 2; i < fb_size; i++) {
            if (in_a_flag[i]) continue;
            unsigned long p = fb[i];
            unsigned char logp = fb_logb[i];
            /* Sieve positions: x ≡ soln[i] (mod p), mapped to [0, 2M] */
            for (int si = 0; si < 2; si++) {
                unsigned long s_pos = (si == 0 ? soln1[i] : soln2[i]);
                /* First x in [-M, M] where x ≡ s_pos (mod p):
                 * offset = ((s_pos - (-M % p) + p) % p gives start in [0, 2M] */
                long neg_M_mod = (long)((-M) % (long)p);
                if (neg_M_mod < 0) neg_M_mod += p;
                long off = (long)s_pos - neg_M_mod;
                if (off < 0) off += p;
                for (long j = off; j < sieve_len; j += (long)p)
                    sieve[j] += logp;
            }
        }

        /* Threshold: we want sieve[x] ≈ log2(|Q(x)|) * 4 for smooth Q(x).
         * Q(x) = ((ax+b)^2 - n) / a. Near x=0, |Q(x)| ≈ |b^2-n|/a ≈ n/a (small).
         * Near x=M, |Q(x)| ≈ a*M^2. Average is somewhere between.
         * Threshold = log2(a*M^2) * 4 * T where T ≈ 0.6-0.7 to allow slack for
         * large prime factor or sieve misses. Lower T = more candidates = slower
         * trial division but more smooth finds. */
        double log_a = 0;
        for (int i = 0; i < s; i++) log_a += log((double)fb[a_idx[i]]);
        double log_Qmax = log_a + 2.0 * log((double)M);
        unsigned char poly_thresh = (unsigned char)(log_Qmax / log(2.0) * 4 * 0.70);

        /* Collect smooth relations */
        for (long x = -M; x <= M && nsmooth < needed; x++) {
            if (sieve[x + M] < poly_thresh) continue;  /* byte comparison — fast */

            /* Compute Q(x)*a = (a*x+b)^2 - n */
            mpz_set_si(x_val, x);
            mpz_mul(q_val, a_mpz, x_val);
            mpz_add(q_val, q_val, b_mpz); /* a*x + b */
            mpz_set(ax_plus_b[nsmooth], q_val); /* save for later */
            mpz_mul(q_val, q_val, q_val);
            mpz_sub(q_val, q_val, n); /* (a*x+b)^2 - n */
            /* Divide by a to get the sieved value */
            mpz_fdiv_q(q_val, q_val, a_mpz);

            /* Trial divide */
            memset(exponents[nsmooth], 0, fb_size * sizeof(int));
            if (mpz_sgn(q_val) < 0) {
                mpz_neg(q_val, q_val);
                exponents[nsmooth][0] = 1;
            }
            if (mpz_sgn(q_val) == 0) continue;

            mpz_set(tmp2, q_val);
            for (int i = 1; i < fb_size; i++) {
                unsigned long p = fb[i];
                /* Sieve-guided: skip primes that don't divide Q(x) */
                if (soln1[i] != p) { /* not a prime dividing a */
                    unsigned long xmp = ((x % (long)p) + (long)p) % p;
                    if (xmp != soln1[i] && xmp != soln2[i]) continue;
                }
                if (mpz_fits_ulong_p(tmp2)) {
                    unsigned long val = mpz_get_ui(tmp2);
                    while (val % p == 0) { val /= p; exponents[nsmooth][i]++; }
                    mpz_set_ui(tmp2, val);
                } else {
                    while (mpz_divisible_ui_p(tmp2, p)) {
                        mpz_divexact_ui(tmp2, tmp2, p);
                        exponents[nsmooth][i]++;
                    }
                }
                if (mpz_cmp_ui(tmp2, 1) == 0) break;
            }
            /* Also check primes dividing a (not in sieve) */
            for (int j = 0; j < s; j++) {
                int i = a_idx[j];
                unsigned long p = fb[i];
                if (mpz_fits_ulong_p(tmp2)) {
                    unsigned long val = mpz_get_ui(tmp2);
                    while (val % p == 0) { val /= p; exponents[nsmooth][i]++; }
                    mpz_set_ui(tmp2, val);
                } else {
                    while (mpz_divisible_ui_p(tmp2, p)) {
                        mpz_divexact_ui(tmp2, tmp2, p);
                        exponents[nsmooth][i]++;
                    }
                }
            }

            if (mpz_cmp_ui(tmp2, 1) == 0) {
                nsmooth++;
            } else if (mpz_fits_ulong_p(tmp2)) {
                /* Single large prime variation */
                unsigned long lp = mpz_get_ui(tmp2);
                if (lp > 1 && lp <= lp_bound) {
                    unsigned long h = (lp * 2654435761UL) & LP_HASH_MASK;
                    /* Search hash bucket for matching partial */
                    lp_entry_t *ent = lp_hash[h], *prev = NULL, *match = NULL;
                    while (ent) {
                        if (ent->lp == lp) { match = ent; break; }
                        prev = ent; ent = ent->next;
                    }
                    if (match && nsmooth < QS_MAX_SMOOTH - 1) {
                        /* Combine: product of ax+b, sum of exponents */
                        int pidx = match->exp_idx;
                        mpz_mul(ax_plus_b[nsmooth], ax_plus_b[nsmooth], ax_plus_b[pidx]);
                        mpz_mod(ax_plus_b[nsmooth], ax_plus_b[nsmooth], n);
                        for (int j = 0; j < fb_size; j++)
                            exponents[nsmooth][j] += exponents[pidx][j];
                        nsmooth++;
                        /* Remove from hash */
                        if (prev) prev->next = match->next;
                        else lp_hash[h] = match->next;
                        npartials--;
                    } else if (lp_pool_used < 50000) {
                        /* Store new partial */
                        int slot = needed + lp_pool_used;
                        if (slot < QS_MAX_SMOOTH) {
                            memcpy(exponents[slot], exponents[nsmooth], fb_size * sizeof(int));
                            mpz_set(ax_plus_b[slot], ax_plus_b[nsmooth]);
                            lp_entry_t *e = &lp_pool[lp_pool_used++];
                            e->lp = lp;
                            e->exp_idx = slot;
                            e->next = lp_hash[h];
                            lp_hash[h] = e;
                            npartials++;
                        }
                    }
                }
            }
        }
            poly_count++;
        } /* end Gray code inner loop */
        a_count++;
    } /* end a-value outer loop */

    free(soln1); free(soln2); free(a_inv_p); free(in_a_flag);
    for (int j = 0; j < 12; j++) free(Bj_mod_p[j]);
    free(Bj_mod_p);
    free(lp_hash); free(lp_pool);
    for (int i = 0; i < 12; i++) mpz_clear(Bj[i]);
    free(sieve); free(fb_logb);
    mpz_clear(target_a); mpz_clear(sqrt_2n); mpz_clear(tmp_z);
    mpz_clear(q_val); mpz_clear(a_mpz); mpz_clear(b_mpz);
    mpz_clear(x_val); mpz_clear(tmp2);

    if (nsmooth < fb_size + 1) {
        free(fb); free(fb_sqrt); free(exponents);
        for (int i = 0; i < QS_MAX_SMOOTH; i++) mpz_clear(ax_plus_b[i]);
        free(ax_plus_b);
        return 0;
    }

    /* GF(2) Gaussian elimination — reuse existing infrastructure */
    bitmatrix *mat = bm_alloc(nsmooth, fb_size);
    bitmatrix *hist = bm_alloc(nsmooth, nsmooth);

    for (int i = 0; i < nsmooth; i++) {
        for (int j = 0; j < fb_size; j++)
            if (exponents[i][j] & 1) bm_set(mat, i, j);
        bm_set(hist, i, i);
    }

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

    /* Find zero rows → dependencies */
    int found = 0;
    mpz_t X, Y, tmp;
    mpz_init(X); mpz_init(Y); mpz_init(tmp);

    for (int row = 0; row < nsmooth && !found; row++) {
        int is_zero = 1;
        for (int j = 0; j < mat->words_per_row; j++)
            if (mat->rows[(size_t)row * mat->words_per_row + j]) { is_zero = 0; break; }
        if (!is_zero) continue;

        /* X = product of (a_i*x_i + b_i) mod n */
        /* Y = sqrt(product of Q values) = product of fb[j]^(total_exp[j]/2) mod n */
        mpz_set_ui(X, 1);
        mpz_set_ui(Y, 1);
        int *total_exp = calloc(fb_size, sizeof(int));

        for (int i = 0; i < nsmooth; i++) {
            if (!bm_get(hist, row, i)) continue;
            mpz_mul(X, X, ax_plus_b[i]);
            mpz_mod(X, X, n);
            for (int j = 0; j < fb_size; j++)
                total_exp[j] += exponents[i][j];
        }

        /* Y = product of fb[j]^(total_exp[j]/2) mod n */
        for (int j = 1; j < fb_size; j++) {
            if (total_exp[j] == 0) continue;
            unsigned long half = total_exp[j] / 2;
            if (half == 0) continue;
            mpz_t bp;
            mpz_init_set_ui(bp, 1);
            mpz_t b2; mpz_init_set_ui(b2, fb[j]);
            unsigned long e = half;
            while (e) {
                if (e & 1) { mpz_mul(bp, bp, b2); mpz_mod(bp, bp, n); }
                mpz_mul(b2, b2, b2); mpz_mod(b2, b2, n);
                e >>= 1;
            }
            mpz_mul(Y, Y, bp); mpz_mod(Y, Y, n);
            mpz_clear(bp); mpz_clear(b2);
        }

        mpz_sub(tmp, X, Y);
        mpz_abs(tmp, tmp);
        mpz_gcd(result, tmp, n);

        if (mpz_cmp_ui(result, 1) > 0 && mpz_cmp(result, n) != 0)
            found = 1;

        free(total_exp);
    }

    mpz_clear(X); mpz_clear(Y); mpz_clear(tmp);
    bm_free(mat); bm_free(hist);
    free(pivot_row); free(fb); free(fb_sqrt); free(exponents);
    for (int i = 0; i < QS_MAX_SMOOTH; i++) mpz_clear(ax_plus_b[i]);
    free(ax_plus_b);
    return found;
}

static int combined_factor(mpz_t result, const mpz_t n) {
    ecm_sigma_counter = 6;
    size_t ndig = mpz_sizeinbase(n, 10);

    /* ECM stages: B1 and curve counts from GMP-ECM recommendations.
     * Each stage finds factors up to max_digits. */
    static const struct { unsigned long B1; int curves; int max_digits; } ecm_stages[] = {
        {2000,    25,  15},
        {11000,   90,  20},
        {50000,   300, 25},
        {250000,  700, 30},
        {1000000, 1800, 35},
        {3000000, 5100, 40},
        {11000000, 10600, 45},
        {43000000, 19300, 50},
        {0, 0, 0}
    };

    /* SIQS is available but not yet fast enough to beat ECM.
     * Disable for now — ECM handles all sizes. */
    int siqs_after = -1;

    int total_curves = 0;
    int half_digits = (int)(ndig + 1) / 2;
    for (int i = 0; ecm_stages[i].B1; i++) {
        /* Try SIQS once we've hit the curve threshold */
        if (siqs_after >= 0 && total_curves >= siqs_after) {
            if (siqs_factor(result, n)) return 1;
            siqs_after = -1; /* don't try again */
        }
        if (ecm_factor(result, n, ecm_stages[i].B1, ecm_stages[i].curves)) return 1;
        total_curves += ecm_stages[i].curves;
        if (ecm_stages[i].max_digits >= half_digits + 5) break;
    }
    /* Final SIQS attempt if not tried yet */
    if (siqs_after >= 0) {
        if (siqs_factor(result, n)) return 1;
    }
    return 0;
}

/* Test ECM directly, bypassing rho and QS */
LEAN_EXPORT lean_obj_res lean_ecm_test(b_lean_obj_arg n_lean) {
    mpz_t n, result;
    mpz_init(n); mpz_init(result);
    lean_nat_to_mpz(n, n_lean);
    int ok = 0;
    static const struct { unsigned long B1; int curves; } params[] = {
        {2000, 25}, {10000, 200}, {50000, 300}, {0, 0}
    };
    for (int i = 0; params[i].B1 && !ok; i++)
        ok = ecm_factor(result, n, params[i].B1, params[i].curves);
    lean_obj_res ret;
    if (ok) {
        ret = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(ret, 0, mpz_to_lean_nat(result));
    } else ret = lean_box(0);
    mpz_clear(n); mpz_clear(result);
    return ret;
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
