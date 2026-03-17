"""Test ECM implementation - reference for debugging Lean version."""
import math

def ecm_double(px, pz, a24, n):
    """Montgomery point doubling."""
    u = (px + pz) ** 2 % n
    v = (px - pz) ** 2 % n  # Note: px - pz can be negative!
    rx = u * v % n
    diff = u - v  # This can be negative too!
    rz = (a24 * diff % n + v) * diff % n
    return rx, rz

def ecm_add(px, pz, qx, qz, dx, dz, n):
    """Differential addition: R = P + Q given D = P - Q."""
    u = (px - pz) * (qx + qz) % n
    v = (px + pz) * (qx - qz) % n
    su = (u + v) ** 2 % n
    di = (u - v) ** 2 % n
    return dz * su % n, dx * di % n

def ecm_mul(px, pz, k, a24, n):
    """Montgomery ladder: k * P."""
    if k <= 1:
        return px, pz
    rx, rz = px, pz
    qx, qz = ecm_double(px, pz, a24, n)
    for bit in range(k.bit_length() - 2, -1, -1):
        if (k >> bit) & 1:
            rx, rz = ecm_add(qx, qz, rx, rz, px, pz, n)
            qx, qz = ecm_double(qx, qz, a24, n)
        else:
            qx, qz = ecm_add(rx, rz, qx, qz, px, pz, n)
            rx, rz = ecm_double(rx, rz, a24, n)
    return rx, rz

def ecm_one_curve(n, sigma, B1):
    """Try one ECM curve. Returns factor or None."""
    u = (sigma * sigma - 5) % n
    v = (sigma * 4) % n
    px = pow(u, 3, n)
    pz = pow(v, 3, n)

    # a24 = (v-u)^3 * (3u+v) / (16 * u^3 * v)
    diff = (v - u) % n
    num = pow(diff, 3, n) * ((3 * u + v) % n) % n
    den = 16 * px % n * v % n

    g = math.gcd(den, n)
    if g != 1:
        return g if g != n else None

    inv = pow(den, -1, n)
    a24 = num * inv % n

    # Stage 1
    p = 2
    while p <= B1:
        pp = p
        while pp * p <= B1:
            pp *= p
        px, pz = ecm_mul(px, pz, pp, a24, n)
        p += 1
        while p <= B1:
            # Quick primality check
            if all(p % d != 0 for d in range(2, int(p**0.5) + 1)):
                break
            p += 1

    g = math.gcd(pz, n)
    if 1 < g < n:
        return g
    return None

def ecm(n, B1, curves):
    import random
    random.seed(42)
    for i in range(curves):
        sigma = random.randrange(6, 1000006)
        result = ecm_one_curve(n, sigma, B1)
        if result:
            print(f"  Found factor {result} on curve {i} with sigma={sigma}")
            return result
    return None

# Test cases
tests = [
    (143, 100, 5),           # trivial: 11 * 13
    (10403, 100, 10),        # 101 * 103
    (1000003 * 1000033, 1000, 20),  # 12-digit
    (4061802743374398955091421338749, 50000, 100),  # 31-digit, 15-digit factors
]

for n, B1, curves in tests:
    print(f"\nn = {n} ({len(str(n))} digits)")
    result = ecm(n, B1, curves)
    if result:
        print(f"  Factor: {result}, cofactor: {n // result}")
    else:
        print(f"  FAILED with B1={B1}, {curves} curves")
