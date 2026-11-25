#!/usr/bin/env python3
"""Reconstruct the compressed Lean input tables from A5 and GL(3,2).

Usage: python3 audit_brauer_groups.py [path/to/A5BrauerCertificate.lean]
Dependencies: Python standard library. No GAP or downloaded group data.
"""
from collections import defaultdict, deque
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
import re
import sys


def alternating_five():
    return [p for p in permutations(range(5))
            if sum(p[i] > p[j] for i in range(5) for j in range(i + 1, 5)) % 2 == 0]


def general_linear_three_two():
    matrices = []
    for a, b, c in product(range(1, 8), repeat=3):
        images = tuple((a if x & 1 else 0) ^ (b if x & 2 else 0) ^ (c if x & 4 else 0)
                       for x in range(8))
        if len(set(images)) == 8:
            matrices.append(images)
    return matrices


class Group:
    def __init__(self, elements):
        elements = sorted(elements)
        assert elements[0] == tuple(range(len(elements[0])))
        index = {g: i for i, g in enumerate(elements)}
        self.n = len(elements)
        self.mul = [[index[tuple(p[x] for x in q)] for q in elements] for p in elements]
        self.inv = [row.index(0) for row in self.mul]
        self.conj = [[self.mul[self.mul[g][x]][self.inv[g]] for x in range(self.n)]
                     for g in range(self.n)]
        self.classes = sorted(set(frozenset(row[x] for row in self.conj)
                                  for x in range(self.n)), key=lambda cl: min(cl))
        self.order = []
        for g in range(self.n):
            y, order = g, 1
            while y != 0:
                y, order = self.mul[y][g], order + 1
            self.order.append(order)

    def closure(self, generators):
        orbit = [0]
        seen = {0}
        for x in orbit:
            for g in generators:
                y = self.mul[x][g]
                if y not in seen:
                    seen.add(y)
                    orbit.append(y)
        return frozenset(seen)

    def subgroups(self):
        # Add one generator in every right coset not already contained in H.
        one = frozenset({0})
        known = {one: ()}
        queue = deque([one])
        while queue:
            sub = queue.popleft()
            covered = set(sub)
            for g in range(self.n):
                if g in covered:
                    continue
                covered.update(self.mul[h][g] for h in sub)
                generators = known[sub] + (g,)
                larger = self.closure(generators)
                if larger not in known:
                    known[larger] = generators
                    queue.append(larger)
        return known

    def cyclic_quotient(self, sub, generators, kernel):
        if not all(self.conj[g][x] in kernel for g in generators for x in kernel):
            return None
        degree = len(sub) // len(kernel)
        for g in sub:
            powers = [0]
            y = g
            while y not in kernel:
                powers.append(y)
                y = self.mul[y][g]
            if len(powers) == degree:
                return {self.mul[p][v]: k for k, p in enumerate(powers) for v in kernel}
        return None


# Low-to-high coefficients of the monic cyclotomic polynomials encountered.
CYCLOTOMIC = {1: [-1, 1], 2: [1, 1], 3: [1, 1, 1], 4: [1, 0, 1],
              5: [1, 1, 1, 1, 1], 7: [1, 1, 1, 1, 1, 1, 1]}


def root_sum(elements, exponents, modulus):
    """Integer value of a sum of roots of unity; assert that it is rational."""
    counts = [0] * modulus
    for x in elements:
        counts[exponents[x]] += 1
    phi = CYCLOTOMIC[modulus]
    while len(counts) >= len(phi):
        leading = counts[-1]
        offset = len(counts) - len(phi)
        for i, coeff in enumerate(phi):
            counts[offset + i] -= leading * coeff
        assert counts.pop() == 0
    assert all(c == 0 for c in counts[1:]), counts
    return counts[0]


def lean_table(source, namespace):
    body = source.split('namespace ' + namespace + '\n', 1)[1].split('end ' + namespace, 1)[0]
    rows = re.findall(r'\|\s*\.(\w+)\s*=>\s*⟨([^⟩]+)⟩', body.split('def index', 1)[0])
    return {name: tuple(int(c.strip()) for c in values.split(',')) for name, values in rows}


def audit(elements, orders, lean_rows, numerator, denominator):
    group = Group(elements)
    subgroups = group.subgroups()
    found = set()
    selected = defaultdict(set)
    char_count = 0
    for sub, generators in subgroups.items():
        if len(sub) == group.n:
            continue
        for kernel in subgroups:
            if not kernel <= sub:
                continue
            exponents = group.cyclic_quotient(sub, generators, kernel)
            if exponents is None:
                continue
            modulus = len(sub) // len(kernel)
            # Every faithful character of H/K is a Galois conjugate. A rational
            # character sum is shared by all of these conjugates.
            char_count += len(CYCLOTOMIC[modulus]) - 1
            row = (len(sub), *(root_sum((g for g in sub if group.order[g] == order),
                                       exponents, modulus) for order in orders))
            found.add(row)
            if row in (lean_rows[numerator], lean_rows[denominator]):
                # Bare conjugacy classes, including both split classes separately.
                induced = tuple(Fraction(group.n * root_sum(cl & sub, exponents, modulus),
                                         len(cl) * len(sub)) for cl in group.classes)
                selected[row].add(induced)
    expected = set(lean_rows.values())
    assert found == expected, (found - expected, expected - found)
    plus, minus = selected[lean_rows[numerator]], selected[lean_rows[denominator]]
    assert len(plus) == len(minus) == 1
    plus, minus = next(iter(plus)), next(iter(minus))
    assert all(a - b == 1 for a, b in zip(plus, minus))
    print(f'order {group.n}: {len(subgroups) - 1} proper subgroups, '
          f'{char_count} subgroup/linear-character pairs, {len(found)} distinct rows ({len(lean_rows)} Lean types), '
          f'{len(group.classes)} original conjugacy classes; exact signed identity verified')


def main():
    table = (Path(sys.argv[1]) if len(sys.argv) > 1
             else Path(__file__).with_name('A5BrauerCertificate.lean')).read_text()
    audit(alternating_five(), [2, 3, 5], lean_table(table, 'A5BrauerCertificate'), 'd10', 'a4twist')
    audit(general_linear_three_two(), [2, 3, 4, 7],
          lean_table(table, 'PSL27BrauerCertificate'), 'borel', 's4sign')


if __name__ == '__main__':
    main()
