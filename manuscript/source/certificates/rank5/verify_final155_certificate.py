#!/usr/bin/env python3
"""Finite arithmetic certificate for the rank-five family.

Only Python standard-library imports. The denominator N need not be prime.
The finite-complexity prime theorem and local descent arguments remain
mathematical inputs; running this file certifies their finite arithmetic
premises, not the analytic theorem itself.
"""
import json
from math import gcd, isqrt, prod
from pathlib import Path


F, H, J = tuple(range(4)), tuple(range(4, 8)), tuple(range(8, 12))
CONSTANTS = (-1, 2, 3, 5)
EXPECTED_CI = (54, 1, 8, 1, 8, 1, 1, 2, 4, 1, 1, 6)


def is_prime(p):
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    return all(p % d for d in range(3, isqrt(p) + 1, 2))


def valuation(z, p):
    assert z != 0
    k = 0
    while z % p == 0:
        z //= p
        k += 1
    return k


def polynomial_product(forms):
    # Coefficient order is ascending in M, with N set equal to one.
    result = [1]
    for a, b in forms:
        new = [0] * (len(result) + 1)
        for i, c in enumerate(result):
            new[i] += b * c
            new[i + 1] += a * c
        result = new
    return result


def echelon(rows):
    basis = {}
    for row in rows:
        while row:
            bit = row.bit_length() - 1
            if bit in basis:
                row ^= basis[bit]
            else:
                basis[bit] = row
                break
    return basis


def nullspace(rows, width):
    basis = echelon(rows)
    result = []
    for free in range(width):
        if free in basis:
            continue
        vector = 1 << free
        for pivot in sorted(basis):
            if (basis[pivot] & vector).bit_count() % 2:
                vector ^= 1 << pivot
        result.append(vector)
    assert all((r & v).bit_count() % 2 == 0 for r in rows for v in result)
    return result


def legendre_bit(z, p):
    assert p > 2 and is_prime(p)
    value = pow(z % p, (p - 1) // 2, p)
    assert value in (1, p - 1), (z, p)
    return int(value != 1)


def local_code(d, p):
    v = valuation(d, p)
    unit = d // p**v
    if p == 2:
        return {1: 0, 3: 5, 5: 4, 7: 1}[unit % 8] ^ (2 if v % 2 else 0)
    return legendre_bit(unit, p) ^ (2 if v % 2 else 0)


def passing_quartic_classes(a, b, p, precision):
    """Necessary congruence tests for dV^4+aV^2S^2+(b/d)S^4=W^2.

    Scaling makes (V,S) primitive.  Its charts are S=1 and V=1 with p|S.
    Odd-valuation d with unit b is excluded by valuations before division.
    For other classes every coefficient is integral and both charts are
    tested exhaustively modulo p**precision.
    """
    representatives = ([1, -1, 2, -2, 5, -5, 10, -10] if p == 2
                       else [1, 2, p, 2*p])
    modulus = p**precision
    squares = {w*w % modulus for w in range(modulus)}
    result = []
    for d in representatives:
        vd = valuation(d, p)
        if vd > valuation(b, p):
            assert vd == 1 and valuation(b, p) == 0
            continue
        du = d // p**vd
        bd = (b // p**vd) * pow(du, -1, modulus) % modulus
        for v in range(modulus):
            vv = v*v % modulus
            if (d*vv*vv + a*vv + bd) % modulus in squares:
                result.append(local_code(d, p))
                break
        else:
            for s in range(0, modulus, p):
                ss = s*s % modulus
                if (d + a*ss + bd*ss*ss) % modulus in squares:
                    result.append(local_code(d, p))
                    break
    return result


def verify_factorization(record, prime_support):
    factors = {int(p): int(e) for p, e in record['factors'].items()}
    assert all(p in prime_support and e > 0 for p, e in factors.items())
    assert prod(p**e for p, e in factors.items()) == abs(int(record['value']))
    return factors


def small_factorization(z):
    """All scalar constants occurring here are supported on -1,2,3,5."""
    result = {-1: int(z < 0)}
    z = abs(z)
    for p in (2, 3, 5):
        k = 0
        while z % p == 0:
            z //= p
            k += 1
        result[p] = k
    assert z == 1
    return result


def char_product(chars, factorizations, negative=False):
    answer = chars[-1] if negative else 0
    for factors in factorizations:
        for p, exponent in factors.items():
            if exponent % 2:
                answer ^= chars[p]
    return answer


def main():
    from fractions import Fraction
    data = json.loads(Path(__file__).with_name('final155_certificate.json').read_text())
    forms = [(int(r['a']), int(r['b'])) for r in data['forms']]
    ci = data['cofactors']
    S = set(data['intrinsic_primes'])
    assert len(S) == 14 and all(is_prime(p) for p in S)
    assert tuple(ci) == EXPECTED_CI
    assert data['geometry'] == dict(D=[62, -226, -165], T=[1550, -5440, -8745], Q=[1240, -3187, -7755])
    assert len(forms) == 12 and all(gcd(a, b) == 1 for a, b in forms)
    intrinsic = {2, 3, 5}
    determinants = {}
    for record in data['determinant_factorizations']:
        i, j = record['i'], record['j']
        assert 0 <= i < j < 12 and (i, j) not in determinants
        ai, bi = forms[i]
        aj, bj = forms[j]
        assert int(record['value']) == ai*bj-aj*bi != 0
        factors = verify_factorization(record, S)
        determinants[i, j] = factors
        intrinsic.update(factors)
    assert len(determinants) == 66 and intrinsic == S
    def factored_on_S(z):
        answer = {-1: int(z < 0)}
        z = abs(z)
        assert z
        for p in S:
            exponent = 0
            while z % p == 0:
                z //= p
                exponent += 1
            if exponent:
                answer[p] = exponent
        assert z == 1
        return answer
    for a, b in forms[1:]:
        factored_on_S(b)

    pf, ph, pj = [polynomial_product(forms[start:start+4]) for start in (0, 4, 8)]
    assert all(625*f+3*h == 16*j for f, h, j in zip(pf, ph, pj))
    def model(m, n):
        ls = [a*m+b*n for a, b in forms]
        f, h, j = [prod(ls[start:start+4]) for start in (0, 4, 8)]
        a, b, c = 1500*f, -2700*f*h, 57600*f*j
        assert a*a-4*b == c
        return ls, (f, h, j), ((a, b), (-2*a, c))
    # Each cleared point identity is homogeneous degree12: 13 distinct
    # evaluations on N=1 give an exact polynomial identity certificate.
    for m in range(13):
        ls, (f, h, j), curves = model(m, 1)
        D = 62-226*m-165*m*m
        T = 1550-5440*m-8745*m*m
        Q = 1240-3187*m-7755*m*m
        K = ls[2]*ls[3]*ls[6]*ls[7]
        R = ls[1]*ls[2]*ls[8]*ls[10]
        V = m*ls[1]*ls[8]*ls[9]
        points = [
            [(-150*f, 3600*D*f),
             (Fraction(10, 49)*K, Fraction(80, 343)*K*(2*T-55*D))],
            [(24*j, 288*D*j),
             (120*V, Fraction(720, 7)*V*(3*T+65*D)),
             (Fraction(1600, 49)*R, Fraction(3200, 343)*R*Q)]]
        for (a, b), group in zip(curves, points):
            for x, y in group:
                assert y*y == x*x*x+a*x*x+b*x
        S1 = ls[2]*ls[3]*ls[10]*ls[11]
        V2 = ls[0]*ls[3]*ls[9]*ls[11]
        A0 = 3*T+65*D
        on_E = points[0]+[
            (36*D*D, 36*D*(j-100*f)),
            (Fraction(9, 49)*A0*A0, Fraction(90, 7)*A0*(V-4*S1)),
            (Fraction(1, 49)*Q*Q, Fraction(1, 343)*Q*(400*R-21609*V2))]
        a, b = curves[0]
        c = curves[1][1]
        for x, y in on_E:
            assert y*y == x*x*x+a*x*x+b*x
        for (x, y), (u, v) in zip(points[1], on_E[2:]):
            if x:
                assert Fraction(y*y, 4*x*x) == u
                assert Fraction(y*(x*x-c), 8*x*x) == v

    states = {int(p): int(r) for p, r in data['states'].items()}
    R = set(data['crt_primes'])
    assert R == {2, 3, 5, 7, 11, 17, 19, 31}
    ignored = S-R
    assert set(states) == R-{2, 3}
    congruences = [(64, 54), (81, 54), (5, 4)] + [(p, states[p]) for p in sorted(R-{2, 3, 5})]
    W = prod(q for q, _ in congruences)
    M = sum(r*(W//q)*pow(W//q, -1, q) for q, r in congruences) % W
    assert M == int(data['M_residue']) and W == int(data['modulus'])
    assert int(data['N_residue']) == -1 and M % 25920 == 54
    assert int(data['small_modulus']) == 25920
    assert data['congruences'] == [dict(modulus=q, M=r, N=-1) for q, r in congruences]
    for a, b in forms:
        assert all(a+b*t > 0 for t in (Fraction(19, 20), Fraction(11, 10)))
    # Signed congruence representative: L4 is negative here; its residue
    # must not be replaced by an absolute value. Future primes are positive.
    ls, (f, h, j), curves = model(M, -1)
    pi = [v//c for v, c in zip(ls, ci)]
    assert [2**valuation(v, 2)*3**valuation(v, 3) for v in ls] == ci
    assert all(gcd(v, W) == 1 for v in pi)
    assert pi[0] % 8 == 1 and pi[0] % 4 == 1
    normalized = data['prime_forms']
    assert len(normalized) == 12
    for i, ((a, b), rec) in enumerate(zip(forms, normalized)):
        assert int(rec['X']) == a*W//ci[i]
        assert int(rec['Y']) == b*W//ci[i]
        assert int(rec['constant']) == pi[i]
    assert all(W % p == 0 for p in R)
    assert all(W % p for p in ignored)
    for q in ignored:
        directions = {(1, b*pow(a, -1, q) % q) if a % q else (0, 1) for a, b in forms}
        assert len(directions) == int(data["exceptional_direction_counts"][str(q)])
        assert len(directions) < q+1
    for i, one in enumerate(normalized):
        for two in normalized[i+1:]:
            assert int(one['X'])*int(two['Y']) != int(two['X'])*int(one['Y'])

    # Check the finite premises of the fixed-local proof modulo 25920.
    # The coupled identity is essential in the 2-adic exceptional branch.
    assert valuation(f, 2) == valuation(h, 2) == 4 and valuation(j, 2) == 3
    alpha, beta, kappa = 375*(f//16), -675*(f//16)*(h//16), 225*(f//16)*(j//8)
    assert alpha % 8 == 3 and beta % 8 == kappa % 8 == 1
    assert alpha*alpha-beta == 8*kappa
    a, b = curves[0]
    A, B = curves[1]
    assert a//16 == 4*alpha and b//256 == 4*beta
    assert A//64 == -2*alpha and B//4096 == 8*kappa
    for u in (3, 11):
        for aa in (3, 11):
            for kk in (1, 9):
                br1 = u*u-aa*u+2*kk
                br2 = 2*u*u-aa*u+kk
                assert br1 % 4 == br2 % 4 == 2
                assert u*(br1//2) % 8 in (3, 7)
                assert u*(br2//2) % 8 in (3, 7)
    # Every modulo64 pair has one of16 lifts modulo256. The normalized
    # factor units modulo32, hence scaled a mod64 and b mod128, are fixed
    # by a lift; these residues preserve both primitive quartic charts.
    for r in range(4):
        for t in range(4):
            _, (_, _, _), lift_curves = model(54+64*r, -1+64*t)
            scaled = [(lift_curves[0][0]//16, lift_curves[0][1]//256),
                      (lift_curves[1][0]//64, lift_curves[1][1]//4096)]
            for index, (aa, bb) in enumerate(scaled):
                expected = [0, 2] if index == 0 else [0, 1, 2, 3]
                assert sorted(passing_quartic_classes(aa, bb, 2, 6)) == expected
    assert (valuation(f, 3), valuation(h, 3), valuation(j, 3)) == (3, 0, 1)
    assert valuation(a, 3) == 4 and valuation(b, 3) == valuation(a*a-4*b, 3) == 6
    assert (b//729) % 3 == 1
    assert all(valuation(c, 2) <= 3 and valuation(c, 3) <= 3 for c in ci)
    assert (f % 5, h % 5, j % 5) == (1, 2, 1)
    for aa, bb in curves:
        assert valuation(aa, 5) >= 3 and valuation(bb, 5) == 2 and (bb//25) % 5 == 4
    
    local_images = {2: ([0, 2], [0, 1, 2, 3]), 3: ([0], [0, 1, 2, 3]), 5: ([0, 2], [0, 2])}
    fixed = {'E': [], 'Ep': []}
    for p in (2, 3, 5):
        for k, side in enumerate(('E', 'Ep')):
            group = F+H if side == 'E' else F+J
            coordinates = [local_code(z, p) for z in list(CONSTANTS)+[pi[i] for i in group]]
            for ann in nullspace(local_images[p][k], 3 if p == 2 else 2):
                row = sum(((ann & coord).bit_count() % 2) << i for i, coord in enumerate(coordinates))
                if row:
                    fixed[side].append(row)
    fixed['Ep'].append(1)

    characters = []
    reference = {int(q): int(r) for q, r in data['reference_character_states'].items()}
    assert set(reference) == ignored
    for index, pvalue in enumerate(pi):
        chars = {-1: int(pvalue % 4 == 3), 2: int(pvalue % 8 in (3, 5))}
        for q in sorted(S-{2}):
            residue = pvalue if q in R else ((forms[index][0]*reference[q]-forms[index][1])*pow(ci[index], -1, q))
            chars[q] = legendre_bit(residue, q) ^ (((q-1)//2 % 2) & chars[-1])
        characters.append(chars)
    def symbol(z, index, chars=characters):
        return char_product(chars[index], [factored_on_S(z)])
    def cross_rows(chars):
        cross = [[0]*12 for _ in range(12)]
        for i, (ai, bi) in enumerate(forms):
            for j, (aj, bj) in enumerate(forms):
                if i == j:
                    continue
                if i == 0:
                    cross[i][j] = symbol(bj*ci[j], 0, chars)
                elif j == 0:
                    cross[i][j] = symbol(bi*ci[i], 0, chars)
                else:
                    cross[i][j] = symbol(ci[0]*ci[j]*(bi*aj-bj*ai)*bi, i, chars) ^ symbol(bi*ci[i], 0, chars)
        return cross
    cross = cross_rows(characters)
    # The auxiliary assignment is a realizable full-CRT reference. It is
    # not an extra congruence on the prime pattern used by the theorem.
    for i in range(12):
        for j in range(i+1, 12):
            assert cross[i][j] ^ cross[j][i] == characters[i][-1] & characters[j][-1]
    def moving_rows(side, eps, chars):
        cross = cross_rows(chars)
        group = F+H if side == 'E' else F+J
        q = (-2700 if side == 'E' else 57600)*prod(ci[i] for i in group)
        rows = fixed[side][:]
        for i in F:
            row = sum(symbol(d, i, chars) << k for k, d in enumerate(CONSTANTS))
            diagonal = symbol(q, i, chars)
            for j in group:
                if i != j:
                    bit = cross[i][j] ^ eps
                    diagonal ^= bit
                    row |= bit << (4+group.index(j))
            row |= diagonal << (4+group.index(i))
            rows.append(row)
        for i in (J if side == 'E' else H):
            row = sum(symbol(d, i, chars) << k for k, d in enumerate(CONSTANTS))
            for j in group:
                row |= (cross[i][j] ^ eps) << (4+group.index(j))
            rows.append(row)
        return rows
    # All rows depend linearly over F2 on the constant-prime characters.
    # Checking all72 basis derivatives proves invariance for all2^72
    # joint assignments, regardless of realizability or reciprocity.
    for q in ignored:
        for index in range(12):
            altered = [dict(c) for c in characters]
            altered[index][q] ^= 1
            for side in ('E', 'Ep'):
                for eps in (0, 1):
                    assert moving_rows(side, eps, altered) == moving_rows(side, eps, characters)

    section_classes = {
        'E': [(-2700, F+H), (-6, F), (10, (2, 3, 6, 7))],
        'Ep': [(57600, F+J), (6, J), (30, (0, 1, 8, 9)), (1, (1, 2, 8, 10))]}
    known = {}
    for side in ('E', 'Ep'):
        group = F+H if side == 'E' else F+J
        codes = []
        for scalar, indices in section_classes[side]:
            factors = small_factorization(scalar*prod(ci[i] for i in indices))
            code = sum((factors[p] % 2) << k for k, p in enumerate(CONSTANTS))
            code += sum(1 << (4+group.index(i)) for i in indices)
            codes.append(code)
        assert codes == data['known_vectors'][side]
        assert len(echelon(codes)) == (3 if side == 'E' else 4)
        known[side] = codes
    reduced = {}
    for eps in (0, 1):
        for side in ('E', 'Ep'):
            rows = moving_rows(side, eps, characters)
            assert rows == data['matrices'][side+str(eps)]
            dimension = 12-len(echelon(rows))
            assert dimension == (3 if side == 'E' else 4)
            assert all((r & v).bit_count() % 2 == 0 for r in rows for v in known[side])
            kernel = nullspace(rows, 12)
            assert len(echelon(kernel+known[side])) == len(kernel) == dimension
            rref = echelon(rows)
            for pivot in sorted(rref):
                for other in rref:
                    if other != pivot and rref[other] & (1 << pivot):
                        rref[other] ^= rref[pivot]
            reduced[side+str(eps)] = [rref[k] for k in sorted(rref, reverse=True)]
            print(f'{side}, epsilon={eps}: matrix rank {12-dimension}, kernel dimension {dimension}')
    assert reduced['E0'] == reduced['E1'] == [2051, 1027, 523, 267, 137, 73, 33, 17, 4]
    print('E reduced rows:', reduced['E0'])
    assert reduced['Ep0'] == reduced['Ep1'] == [2322, 1288, 794, 152, 66, 42, 4, 1]
    print('Ep reduced rows:', reduced['Ep0'])
    print('PASS: 14 certified primes; 66 complete determinant factorizations; all five section identities and five points on E;')
    print('CRT and primitive prime forms; uniform local25920 premises and all16 quartic lifts; 66 reference reciprocal pairs; 72 zero character derivatives; six exceptional direction counts; four matrices;')
    print('seven independent known codes span both kernels. Denominator N is not required prime.')
    print('Analytic infinitude and local valuation proofs are separate mathematical inputs.')


if __name__ == '__main__':
    main()
