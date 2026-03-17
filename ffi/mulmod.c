/* Unboxed 64-bit modular multiplication for Lean FFI.
 * Uses __int128 for intermediate product — no GMP needed.
 */
#include <stdint.h>
#include <lean/lean.h>

/* mulMod64(a, b, m) = a * b % m, all UInt64 */
LEAN_EXPORT uint64_t lean_mulmod64(uint64_t a, uint64_t b, uint64_t m) {
    return (unsigned __int128)a * b % m;
}

/* addMod64(a, b, m) = (a + b) % m */
LEAN_EXPORT uint64_t lean_addmod64(uint64_t a, uint64_t b, uint64_t m) {
    uint64_t s = a + b;
    return s >= m || s < a ? s - m : s;
}

/* subMod64(a, b, m) = (a - b + m) % m */
LEAN_EXPORT uint64_t lean_submod64(uint64_t a, uint64_t b, uint64_t m) {
    return a >= b ? a - b : a + m - b;
}
