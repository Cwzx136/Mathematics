#!/usr/bin/env python3
"""Verify the smoothed elliptic certificates using Python integer arithmetic.

Usage: python3 check_smoothing.py smooth8_weights.json smooth20_weights.json
There are no third-party dependencies. A positive certificate for a mixed root
coefficient net succeeds only after both subregions have passed.
"""
import json
import sys
from collections import Counter
from fractions import Fraction
from math import comb


def chebyshev(n, second):
    """Return constant-first integer coefficients of T_n or U_n."""
    p, q = [1], [0, 2 if second else 1]
    if n == 0:
        return p
    for _ in range(1, n):
        r = [0] + [2 * x for x in q]
        for j, x in enumerate(p):
            r[j] -= x
        p, q = q, r
    return q


def homogeneous(coefficients, degree):
    """Clear (a+b)^d in p((a-b)/(a+b)), returning coefficients by a exponent."""
    result = [0] * (degree + 1)
    for k, c in enumerate(coefficients):
        for i in range(k + 1):
            for j in range(degree - k + 1):
                result[i + j] += c * comb(k, i) * (-1) ** (k - i) * comb(degree - k, j)
    return result


def root_net(entries, degree):
    powers = {j: homogeneous(chebyshev(j, True), degree) for _, j, _ in entries}
    frequencies = {l: homogeneous(chebyshev(l, False), degree) for l, _, _ in entries}
    return [[sum(c * powers[j][a] * frequencies[l][b] for l, j, c in entries)
             for b in range(degree + 1)] for a in range(degree + 1)]


def split_row(row, right):
    d = len(row) - 1
    if right:
        return [2 ** k * sum(comb(i, k) * row[i] for i in range(k, d + 1))
                for k in range(d + 1)]
    return [2 ** (d - k) * sum(comb(d - i, d - k) * row[i] for i in range(k + 1))
            for k in range(d + 1)]


def certify(net, depth, cap, histogram):
    if all(c >= 0 for row in net for c in row):
        histogram[depth] += 1
        return
    if depth >= cap:
        raise ValueError("Mixed terminal net")
    transpose = depth % 2 == 0
    by_rows = list(zip(*net)) if transpose else net
    for right in (False, True):
        result = [split_row(row, right) for row in by_rows]
        certify(list(zip(*result)) if transpose else result, depth + 1, cap, histogram)


def d_j(j):
    if j == 1:
        return Fraction(1, 3)
    k = j + 1
    return Fraction(k, 4) * (1 - Fraction(2, 3 * k**5 - 2 * k**4 - k**2))


def verify(path):
    with open(path, encoding="utf-8") as stream:
        data = json.load(stream)
    entries = data["entries"]
    denominator = data["den"]
    if len({(l, j) for l, j, _ in entries}) != len(entries):
        raise ValueError("Duplicate entries")
    weights = {(l, j): Fraction(c, denominator) for l, j, c in entries}
    if weights[1, 1] != 1 or any(c < 0 and l*j != 0 for l, j, c in entries):
        raise ValueError("Incorrect coefficient constraints")
    d = max(max(l, j) for l, j, _ in entries)
    histogram = Counter()
    certify(root_net(entries, d), 0, data["depth"], histogram)
    if histogram != Counter({int(k): n for k, n in data['leaves'].items()}):
        raise ValueError("Incorrect histogram")
    slope = sum(c * d_j(j) for (l, j), c in weights.items() if l*j)
    gain = Fraction(13, 8) * (Fraction(95181399549361514143, 344366740312739020800)
                              - Fraction(315, 796) * weights[0, 0])
    if gain <= 0:
        raise ValueError("Nonpositive gain")
    results = [slope, gain, slope / gain]
    if results != [Fraction(data[x]) for x in ("slope", "gain", "ratio")]:
        raise ValueError("Incorrect objective")
    rounded = {8: 617635, 20: 616918}
    if not slope / gain < Fraction(rounded[d], 100000):
        raise ValueError("Upper bound failed")
    print(f"{path}: degree {d}, {sum(histogram.values())} leaves, maximum depth {max(histogram)}")
    print(f"G = {slope}, J = {gain}")
    print(f"G/J = {slope/gain} < {rounded[d]}/100000")


if __name__ == "__main__":
    if len(sys.argv) == 1:
        raise SystemExit(__doc__)
    for filename in sys.argv[1:]:
        verify(filename)
