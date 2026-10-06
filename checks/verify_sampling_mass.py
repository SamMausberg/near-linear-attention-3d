#!/usr/bin/env python3
"""Independent exact finite diagnostics for the sampled-hull proof.

This enumerates every Bernoulli subset of several tiny 3D instances, both
without anchors and with the first four keys forced into every sample, and
compares two calculations of expected facet conflict mass. It also checks
the bounded-incidence polygon triangulation. It is not a fast implementation
of the attention algorithm, and finite checks do not replace the proof.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import random


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1],
            a[2]*b[0]-a[0]*b[2],
            a[0]*b[1]-a[1]*b[0])


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def determinant4(a, b, c, d):
    return dot(cross(sub(b, a), sub(c, a)), sub(d, a))


def check_general_position(points):
    return all(determinant4(*(points[j] for j in ids)) != 0
               for ids in combinations(range(len(points)), 4))


def random_generic(rng, count):
    points = []
    while len(points) < count:
        candidate = tuple(rng.randrange(-30, 31) for _ in range(3))
        if candidate in points:
            continue
        if all(determinant4(a, b, c, candidate) != 0
               for a, b, c in combinations(points, 3)):
            points.append(candidate)
    assert check_general_position(points)
    return points


def oriented_candidates(points):
    records = []
    for ids in combinations(range(len(points)), 3):
        a, b, c = (points[j] for j in ids)
        dmask = sum(1 << j for j in ids)
        normal = cross(sub(b, a), sub(c, a))
        signs = [dot(normal, sub(p, a)) for p in points]
        assert all(signs[j] != 0 for j in range(len(points)) if j not in ids)
        for orientation in (-1, 1):
            cmask = sum(1 << j for j, value in enumerate(signs)
                        if orientation*value > 0)
            records.append((dmask, cmask, cmask.bit_count()))
    return records


def enumerate_distribution(points, anchor_mask=0):
    """Sum facet counts and conflicts by the number of unforced sampled keys."""
    n = len(points)
    anchor_count = anchor_mask.bit_count()
    random_count = n-anchor_count
    records = oriented_candidates(points)
    facets_by_size = [0]*(random_count+1)
    conflicts_by_size = [0]*(random_count+1)
    subsets_by_size = [0]*(random_count+1)
    max_mass = 0
    max_facet_conflict = 0
    for mask in range(1 << n):
        if (mask & anchor_mask) != anchor_mask:
            continue
        size = mask.bit_count()
        random_size = size-anchor_count
        facets = [(cmask, count) for dmask, cmask, count in records
                  if (mask & dmask) == dmask and not (mask & cmask)]
        assert len(facets) <= 2*size
        if size >= 4:
            assert len(facets) <= 2*size-4
        if size == 3:
            assert len(facets) == 2
        if size < 3:
            assert len(facets) == 0
        mass = sum(count for _, count in facets)
        facets_by_size[random_size] += len(facets)
        conflicts_by_size[random_size] += mass
        subsets_by_size[random_size] += 1
        max_mass = max(max_mass, mass)
        if size >= 4:
            max_facet_conflict = max(max_facet_conflict,
                                     max((count for _, count in facets), default=0))
    return {
        'records': records,
        'facets_by_size': facets_by_size,
        'conflicts_by_size': conflicts_by_size,
        'subsets_by_size': subsets_by_size,
        'max_mass': max_mass,
        'max_facet_conflict': max_facet_conflict,
        'anchor_mask': anchor_mask,
        'random_count': random_count,
    }


def expectation(coeffs, probability):
    n = len(coeffs)-1
    return sum((F(count)*probability**size*(1-probability)**(n-size)
                for size, count in enumerate(coeffs)), F(0))


def zigzag(m):
    left, right = 0, m-1
    left_turn = True
    triangles = []
    while right-left >= 2:
        if left_turn:
            triangles.append((right, left, left+1))
            left += 1
        else:
            triangles.append((left, right-1, right))
            right -= 1
        left_turn = not left_turn
    return triangles


def main():
    rng = random.Random(2026100603)
    instances = [
        ('moment_curve_4', [(t, t*t, t*t*t) for t in range(4)]),
        ('moment_curve_7', [(t, t*t, t*t*t) for t in range(-3, 4)]),
        ('moment_curve_10', [(t, t*t, t*t*t) for t in range(-5, 5)]),
        ('random_generic_8', random_generic(rng, 8)),
        ('random_generic_9', random_generic(rng, 9)),
        ('random_generic_10', random_generic(rng, 10)),
    ]
    probabilities = [F(1,16), F(1,8), F(1,4), F(1,3), F(1,2), F(2,3), F(3,4), F(7,8)]
    report = {
        'scope': 'Exact finite sampling and triangulation diagnostics; no fast implementation or proof-assistant certificate.',
        'arithmetic': 'Python integer and Fraction arithmetic',
        'seed': 2026100603,
        'instances': [],
        'subset_count': 0,
        'forced_anchor_subset_count': 0,
        'expectation_comparisons': 0,
        'candidate_probability_comparisons': 0,
        'forced_anchor_expectation_comparisons': 0,
        'forced_anchor_candidate_probability_comparisons': 0,
        'forced_anchor_linear_bounds_when_n_rho_at_least_4': 0,
        'pointwise_comparison_checks': 0,
        'zigzag_polygon_sizes': 0,
    }
    for name, points in instances:
        assert check_general_position(points)
        n = len(points)
        data = enumerate_distribution(points)
        report['subset_count'] += 1 << n
        anchor_mask = (1 << 4)-1
        forced_data = enumerate_distribution(points, anchor_mask)
        report['forced_anchor_subset_count'] += 1 << (n-4)
        expectations = []
        forced_expectations = []
        for rho in probabilities:
            assert expectation(data['subsets_by_size'], rho) == 1
            enumerated_mass = expectation(data['conflicts_by_size'], rho)
            candidates_mass = sum((F(c)*rho**3*(1-rho)**c
                                   for _, _, c in data['records']), F(0))
            assert candidates_mass == enumerated_mass
            report['candidate_probability_comparisons'] += 1
            half_facets = expectation(data['facets_by_size'], rho/2)
            assert enumerated_mass <= 16/rho * half_facets <= 16*n
            report['expectation_comparisons'] += 1
            expectations.append({'rho': str(rho), 'expected_conflict_mass': str(enumerated_mass),
                                 'expected_half_sample_facets': str(half_facets),
                                 'expected_conflict_mass_over_n': str(enumerated_mass/n)})
            assert expectation(forced_data['subsets_by_size'], rho) == 1
            forced_mass = expectation(forced_data['conflicts_by_size'], rho)
            forced_candidates_mass = sum((F(c)*rho**((dmask & ~anchor_mask).bit_count())*(1-rho)**c
                                           for dmask, cmask, c in forced_data['records']
                                           if not (cmask & anchor_mask)), F(0))
            assert forced_candidates_mass == forced_mass
            report['forced_anchor_candidate_probability_comparisons'] += 1
            forced_half_facets = expectation(forced_data['facets_by_size'], rho/2)
            assert forced_half_facets <= 4+(n-4)*rho
            assert forced_mass <= 16/rho * forced_half_facets <= 16*(n-4)+64/rho
            report['forced_anchor_expectation_comparisons'] += 1
            linear_bound_applies = n*rho >= 4
            if linear_bound_applies:
                assert 16/rho*forced_half_facets <= 32*n
                report['forced_anchor_linear_bounds_when_n_rho_at_least_4'] += 1
            forced_expectations.append({
                'rho': str(rho),
                'expected_conflict_mass': str(forced_mass),
                'expected_half_sample_facets': str(forced_half_facets),
                'expected_conflict_mass_over_n': str(forced_mass/n),
                'linear_bound_32_n_applies': linear_bound_applies,
            })
        report['instances'].append({'name': name, 'points': points, 'key_count': n,
                                    'max_sample_conflict_mass': data['max_mass'],
                                    'max_one_facet_conflict_full_dimension': data['max_facet_conflict'],
                                    'expectations': expectations,
                                    'forced_anchor_indices': list(range(4)),
                                    'forced_max_sample_conflict_mass': forced_data['max_mass'],
                                    'forced_expectations': forced_expectations})
    for rho in [F(1, 2**j) for j in range(1, 11)] + probabilities:
        for c in range(257):
            for b in range(4):
                left = F(c)*rho**b*(1-rho)**c
                right = 16/rho*(rho/2)**b*(1-rho/2)**c
                assert left <= right
                report['pointwise_comparison_checks'] += 1
    for m in range(3, 1001):
        triangles = zigzag(m)
        assert len(triangles) == m-2
        occurrences = [0]*m
        for tri in triangles:
            assert len(set(tri)) == 3
            for j in tri:
                occurrences[j] += 1
        assert min(occurrences) >= 1
        assert max(occurrences) <= 3
        report['zigzag_polygon_sizes'] += 1
    report['status'] = 'PASS'
    path = Path(__file__).with_name('sampling_mass_results.json')
    path.write_text(json.dumps(report, indent=2)+'\n')
    summary = {k: value for k, value in report.items() if k != 'instances'}
    summary['maximum_observed_expected_mass_over_n'] = str(max(
        F(case['expected_conflict_mass_over_n'])
        for inst in report['instances'] for case in inst['expectations']))
    summary['maximum_observed_forced_expected_mass_over_n'] = str(max(
        F(case['expected_conflict_mass_over_n'])
        for inst in report['instances'] for case in inst['forced_expectations']))
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
