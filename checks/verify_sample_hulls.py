#!/usr/bin/env python3
"""Independent finite exact checks for sampled-hull attention selection.

This program uses exhaustive hull construction and Fraction arithmetic. It is
not an implementation or a timing test of the asymptotic fast algorithm.
It checks its geometric partitions, dyadic boxes, pair ownership, and final
integer moment reconstruction on small inputs, including the polar-cone
triangulation needed to control conflict-list duplication.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, gcd
from pathlib import Path
import json
import random
import time


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1],
            a[2]*b[0]-a[0]*b[2],
            a[0]*b[1]-a[1]*b[0])


def det(a, b, c):
    return dot(a, cross(b, c))


def lcm(a, b):
    return a//gcd(a, b)*b


def solve_columns(columns, q):
    a, b, c = columns
    d = det(a, b, c)
    if not d:
        return None
    return (det(q, b, c)/d, det(a, q, c)/d, det(a, b, q)/d)


def hull_facets(points, ids, centre):
    """Return exact normalized supporting facets and their original IDs."""
    centred = {j: sub(points[j], centre) for j in ids}
    found = {}
    for ia, ib, ic in combinations(ids, 3):
        a, b, c = (centred[j] for j in (ia, ib, ic))
        normal = cross(sub(b, a), sub(c, a))
        h = dot(normal, a)
        if h == 0:
            continue
        f = tuple(x/h for x in normal)
        if any(dot(f, centred[j]) > 1 for j in ids):
            continue
        on = tuple(j for j in ids if dot(f, centred[j]) == 1)
        found[f] = on
    return [(f, found[f]) for f in sorted(found)]


def cross2(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def polygon_order(projected):
    """Andrew hull in an injective coordinate projection of a polar face."""
    rec = sorted((p[0], p[1], i) for i, p in projected.items())
    lower = []
    for p in rec:
        while len(lower) >= 2 and cross2(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(rec):
        while len(upper) >= 2 and cross2(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    order = [p[2] for p in lower[:-1]+upper[:-1]]
    assert set(order) == set(projected), 'A polar-face vertex was lost'
    return order


def zigzag(order):
    order = list(order)
    triangles = []
    left = True
    while len(order) > 3:
        if left:
            triangles.append((order[-1], order[0], order[1]))
            del order[0]
        else:
            triangles.append((order[-2], order[-1], order[0]))
            del order[-1]
        left = not left
    triangles.append(tuple(order))
    multiplicity = Counter(x for triangle in triangles for x in triangle)
    assert max(multiplicity.values()) <= 3
    return triangles


def frames(points, facets, centre):
    vertices = sorted({j for _, on in facets for j in on})
    assert all(len(on) == 3 for _, on in facets)
    assert len(facets) == 2*len(vertices)-4
    out = []
    counts = Counter()
    for v in vertices:
        incident = [i for i, (_, on) in enumerate(facets) if v in on]
        dv = sub(points[v], centre)
        drop = max(range(3), key=lambda a: abs(dv[a]))
        axes = [a for a in range(3) if a != drop]
        projected = {i: tuple(facets[i][0][a] for a in axes) for i in incident}
        order = polygon_order(projected)
        for tri in zigzag(order):
            normals = tuple(facets[i][0] for i in tri)
            assert det(*normals) != 0
            assert all(dot(f, dv) == 1 for f in normals)
            out.append((v, tri, normals))
            counts.update(tri)
    assert max(counts.values()) <= 9
    return out, counts


def dyadic_floor(x):
    if x == 0:
        return None
    assert x > 0
    e = x.numerator.bit_length()-x.denominator.bit_length()
    b = F(2**e) if e >= 0 else F(1, 2**(-e))
    if b > x:
        e -= 1
        b /= 2
    assert b <= x < 2*b
    return e


def dyadic(e):
    return F(0) if e is None else F(2**e) if e >= 0 else F(1, 2**(-e))


def multi_indices(g):
    return [a for a in product(range(g+1), repeat=3) if sum(a) <= g]


def monomial(x, a):
    ans = 1
    for t, e in zip(x, a):
        ans *= t**e
    return ans


def run_instance(points, queries, values, T, seed, stats, *, checked=True,
                 common_denominator=None):
    rng = random.Random(seed)
    n, nq = len(points), len(queries)
    denominator = 1
    value_denominator = 1
    for p in points:
        for x in p:
            denominator = lcm(denominator, x.denominator)
    for v in values:
        value_denominator = lcm(value_denominator, v.denominator)
    if common_denominator is not None:
        assert common_denominator > 0
        assert common_denominator & (common_denominator-1) == 0
        assert all((x*common_denominator).denominator == 1
                   for p in points+queries for x in p)
        assert all((v*common_denominator).denominator == 1 for v in values)
        denominator = value_denominator = common_denominator
    integers = [tuple(int(x*denominator) for x in p) for p in points]
    value_int = [int(v*value_denominator) for v in values]
    degree = 3
    alphas = multi_indices(degree)
    weights = [tuple(monomial(p, a) for a in alphas) +
               tuple(value_int[j]*monomial(p, a) for a in alphas)
               for j, p in enumerate(integers)]
    stats['maximum_moment_weight_bits'] = max(
        stats['maximum_moment_weight_bits'],
        max(abs(w).bit_length() for row in weights for w in row))
    records = [[] for _ in queries]
    ownership = [Counter() for _ in queries]

    def summed(ids):
        return tuple(sum(weights[j][a] for j in ids) for a in range(len(weights[0])))

    def record(i, h, group, chosen):
        assert set(chosen) <= set(group)
        assert chosen and any(dot(queries[i], points[j]) == h for j in chosen)
        ownership[i].update(group)
        records[i].append((h, tuple(chosen), summed(chosen)))

    def direct(kids, qids, reason):
        stats[reason] += 1
        for i in qids:
            h = max(dot(queries[i], points[j]) for j in kids)
            chosen = [j for j in kids if h-dot(queries[i], points[j]) <= T]
            record(i, h, kids, chosen)

    def recurse(kids, qids, depth):
        if not kids or not qids:
            return
        stats['nodes'] += 1
        stats['maximum_depth'] = max(stats['maximum_depth'], depth)
        if checked:
            stats['checked_maximum_depth'] = max(stats['checked_maximum_depth'], depth)
        if len(kids) <= 6:
            direct(kids, qids, 'base_nodes')
            return
        fixed = kids[:4]
        if det(*(sub(points[j], points[fixed[0]]) for j in fixed[1:])) == 0:
            direct(kids, qids, 'degenerate_fallbacks')
            return
        centre = tuple(sum(points[j][a] for j in fixed)/4 for a in range(3))
        # Dyadic Bernoulli sampling, plus a mandatory tetrahedron.
        sample = fixed+[j for j in kids[4:] if rng.getrandbits(1)]
        facets = hull_facets(points, sample, centre)
        if any(len(on) != 3 for _, on in facets):
            direct(kids, qids, 'degenerate_fallbacks')
            return
        fs, counts = frames(points, facets, centre)
        stats['maximum_facet_coordinate_height_bits'] = max(
            stats['maximum_facet_coordinate_height_bits'],
            max(max(abs(x.numerator).bit_length(), x.denominator.bit_length())
                for f, _ in facets for x in f))
        stats['sample_hulls'] += 1
        stats['facet_records'] += len(facets)
        stats['normal_frames'] += len(fs)
        stats['maximum_frame_copies_of_facet'] = max(
            stats['maximum_frame_copies_of_facet'], max(counts.values()))
        stats['maximum_normal_cone_polygon_size'] = max(
            stats['maximum_normal_cone_polygon_size'],
            max(sum(v in on for _, on in facets)
                for v in {j for _, on in facets for j in on}))
        conflict = [{j for j in kids if dot(f, sub(points[j], centre)) > 1}
                    for f, _ in facets]
        if checked and max(map(len, conflict)) > F(len(kids), 4):
            direct(kids, qids, 'conflict_fallbacks')
            return
        assigned = defaultdict(list)
        for i in qids:
            q = queries[i]
            for z, (v, _, normals) in enumerate(fs):
                lam = solve_columns(normals, q)
                if lam is not None and all(x >= 0 for x in lam):
                    stats['maximum_frame_coefficient_height_bits'] = max(
                        stats['maximum_frame_coefficient_height_bits'],
                        max(max(abs(x.numerator).bit_length(), x.denominator.bit_length())
                            for x in lam))
                    assert dot(q, points[v]) == max(dot(q, points[j]) for j in sample)
                    assigned[z].append((i, lam))
                    if sum(x == 0 for x in lam):
                        stats['queries_on_cone_boundaries'] += 1
                    break
            else:
                raise AssertionError('Normal fan did not cover a query')
        all_bad_mass = sum(len(set().union(*(conflict[f] for f in tri))) for _, tri, _ in fs)
        assert all_bad_mass <= 9*sum(map(len, conflict))
        stats['conflict_duplication_checks'] += 1
        for z, query_lambdas in assigned.items():
            v, tri, normals = fs[z]
            bad = sorted(set().union(*(conflict[f] for f in tri)))
            if bad:
                stats['nonempty_bad_children'] += 1
                if checked:
                    stats['checked_nonempty_bad_children'] += 1
            good = [j for j in kids if j not in set(bad)]
            assert set(good).isdisjoint(bad) and set(good)|set(bad) == set(kids)
            assert set(sample) <= set(good)
            if checked:
                assert len(bad) <= 3*F(len(kids), 4)
            zs = {j: tuple(1-dot(f, sub(points[j], centre)) for f in normals) for j in good}
            assert all(min(zj) >= 0 for zj in zs.values())
            buckets = defaultdict(list)
            for i, lam in query_lambdas:
                bins = tuple(dyadic_floor(x) for x in lam)
                buckets[bins].append((i, lam))
            for bins, bucket in buckets.items():
                bs = tuple(dyadic(e) for e in bins)
                chosen = [j for j in good if all(bs[a]*zs[j][a] <= T for a in range(3))]
                for i, lam in bucket:
                    h = dot(queries[i], points[v])
                    for j in good:
                        deficit = h-dot(queries[i], points[j])
                        assert deficit == dot(lam, zs[j]) >= 0
                        if deficit <= T:
                            assert j in chosen
                        if j in chosen:
                            assert deficit <= 6*T
                        stats['frame_deficit_checks'] += 1
                    record(i, h, good, chosen)
                stats['dyadic_bucket_sums'] += 1
            recurse(bad, [i for i, _ in query_lambdas], depth+1)

    recurse(list(range(n)), list(range(nq)), 0)
    for i, q in enumerate(queries):
        assert ownership[i] == Counter({j: 1 for j in range(n)})
        H = max(h for h, _, _ in records[i])
        assert H == max(dot(q, p) for p in points)
        selected = []
        moments = [0]*len(weights[0])
        for h, chosen, w in records[i]:
            if H-h <= T:
                selected.extend(chosen)
                moments = [x+y for x, y in zip(moments, w)]
        assert len(selected) == len(set(selected))
        for j, p in enumerate(points):
            deficit = H-dot(q, p)
            if deficit <= T:
                assert j in selected
            if j in selected:
                assert deficit <= 7*T
            stats['global_sandwich_checks'] += 1
        assert tuple(moments) == summed(selected)
        stats['query_partition_checks'] += 1
        stats['selected_moment_coordinates_checked'] += len(moments)

        # Integer reconstruction is checked against a separately evaluated
        # rational Taylor sum on the selected original keys.
        query_denominator = 1
        for x in q:
            query_denominator = lcm(query_denominator, x.denominator)
        if common_denominator is not None:
            query_denominator = common_denominator
        qint = tuple(int(x*query_denominator) for x in q)
        scale = denominator*query_denominator
        hint = H*scale
        assert hint.denominator == 1
        hint = int(hint)
        fp = [1]
        for s in range(1, degree+1):
            fp.append(s*scale*fp[-1]+(-hint)**s)
        coefficients = []
        for alpha in alphas:
            remaining = degree-sum(alpha)
            den = factorial(remaining)
            for a in alpha:
                den *= factorial(a)
            coefficients.append(factorial(degree)//den*monomial(qint, alpha)*fp[remaining])
        stats['maximum_reconstruction_coefficient_bits'] = max(
            stats['maximum_reconstruction_coefficient_bits'],
            max(abs(c).bit_length() for c in coefficients))
        m = len(alphas)
        for off, value in ((0, lambda j: 1), (m, lambda j: value_int[j])):
            reconstructed = sum(c*moments[off+a] for a, c in enumerate(coefficients))
            reference = sum((value(j)*sum(((dot(q, points[j])-H)**s/factorial(s)
                                          for s in range(degree+1)), F(0))
                             for j in selected), F(0))
            assert reconstructed == factorial(degree)*scale**degree*reference
            stats['maximum_reconstructed_integer_bits'] = max(
                stats['maximum_reconstructed_integer_bits'], abs(reconstructed).bit_length())
            stats['integer_reconstruction_checks'] += 1


def general_position(points):
    return all(det(sub(points[b], points[a]), sub(points[c], points[a]),
                   sub(points[d], points[a])) != 0
               for a, b, c, d in combinations(range(len(points)), 4))


def random_general_position(rng, count, bound, initial=()):
    out = [tuple(F(x) for x in p) for p in initial]
    while len(out) < count:
        q = tuple(F(rng.randint(-bound, bound)) for _ in range(3))
        if q in out:
            continue
        if all(det(sub(b, a), sub(c, a), sub(q, a)) != 0
               for a, b, c in combinations(out, 3)):
            out.append(q)
    return out


def query_list(points, rng):
    queries = [(F(0), F(0), F(0))]
    queries += [tuple(F(s if a == j else 0) for a in range(3))
                for j in range(3) for s in (-1, 1)]
    queries += [tuple(F(rng.randint(-7, 7), rng.choice((1, 2, 3))) for _ in range(3))
                for _ in range(10)]
    if len(points) >= 4 and det(*(sub(points[j], points[0]) for j in (1, 2, 3))) != 0:
        centre = tuple(sum(points[j][a] for j in range(4))/4 for a in range(3))
        facets = hull_facets(points, list(range(len(points))), centre)
        queries += [f for f, _ in facets[:8]]
    queries += queries[-2:]  # Duplicate query records retain identity.
    return queries


def finite_preprocess(points, queries, values, seed, *, variant='random_grid'):
    """Check the final deterministic preprocessing and an earlier random variant.

    Only deterministic_moment_curve is used by the final theorem. The retained
    random_grid cases are particular outcomes from an earlier proof draft;
    this diagnostic does not estimate a general-position probability.
    """
    n = len(points)
    assert len(queries) == len(values) == n
    ell = (n+1).bit_length()
    B = n**10
    target = 16384*n**24
    R = 1 << (target-1).bit_length()
    assert variant in ('random_grid', 'deterministic_moment_curve')
    theta_exponent = (100 if variant == 'random_grid' else 128)*ell
    theta = F(1, 1 << theta_exponent)
    M = 1 << (200*ell)
    D = R*(1 << ((300 if variant == 'random_grid' else 128)*ell))
    assert R >= target and R//2 < target
    assert all(abs(x) <= B for p in points+queries for x in p)
    assert all(abs(v) <= 1 for v in values)

    def rounded(x):
        a = x*R
        b = a.numerator//a.denominator
        if a-b > F(1, 2):
            b += 1
        ans = F(b, R)  # Exact halfway cases choose the smaller grid point.
        assert abs(ans-x) <= F(1, 2*R)
        return ans

    rounded_points = [tuple(rounded(x) for x in p) for p in points]
    rounded_queries = [tuple(rounded(x) for x in p) for p in queries]
    rounded_values = [rounded(v) for v in values]
    rng = random.Random(seed)
    if variant == 'random_grid':
        perturbing_points = [tuple(F(-1)+F(2*rng.randrange(M), M) for _ in range(3))
                             for _ in points]
    else:
        perturbing_points = [tuple(F(j, 1 << ell)**a for a in (1, 2, 3))
                             for j in range(1, n+1)]
        assert R >= 1 << (3*ell)
        assert all((x*R).denominator == 1 and 0 < x < 1
                   for p in perturbing_points for x in p)
        assert 72*B*B+36*B+6 <= 114*B*B
        w = theta/(1-theta)
        assert w <= 2*theta and 0 < w < 1
        assert R <= 1 << (14+24*ell)
        assert R**3*114*B*B*w < dyadic(50-36*ell) < 1
    perturbed = [tuple((1-theta)*x+theta*y for x, y in zip(p, q))
                 for p, q in zip(rounded_points, perturbing_points)]
    assert all(abs(x) <= B for p in perturbed+rounded_queries for x in p)
    assert all(abs(v) <= 1 for v in rounded_values)
    assert all((x*D).denominator == 1 for p in perturbed+rounded_queries for x in p)
    assert all((v*D).denominator == 1 for v in rounded_values)
    assert all(abs(x-y) <= 2*B*theta
               for p, q in zip(perturbed, rounded_points) for x, y in zip(p, q))
    assert all(abs(dot(q, k)-dot(q, k0)) <= 6*B*B*theta
               for q in rounded_queries for k, k0 in zip(perturbed, rounded_points))
    deterministic_output_error_bound = F(18*B+1, R)+12*B*B*theta
    assert deterministic_output_error_bound < F(1, 32*n**10)
    if variant == 'random_grid':
        assert F(3*n**4, M) <= F(1, (n+2)**190)

    determinants = [abs(det(sub(perturbed[b], perturbed[a]),
                            sub(perturbed[c], perturbed[a]),
                            sub(perturbed[d], perturbed[a])))
                    for a, b, c, d in combinations(range(n), 4)]
    assert n < 4 or (determinants and min(determinants) > 0)
    polynomial_checks = 0
    if variant == 'deterministic_moment_curve':
        for a, b, c, d in combinations(range(n), 4):
            original = [sub(rounded_points[j], rounded_points[a]) for j in (b, c, d)]
            curve = [sub(perturbing_points[j], perturbing_points[a]) for j in (b, c, d)]
            coef = [F(0) for _ in range(4)]
            for mask in range(8):
                rows = [curve[i] if mask & (1 << i) else original[i] for i in range(3)]
                coef[mask.bit_count()] += det(*rows)
            vandermonde = F(1)
            for i, j in combinations((a, b, c, d), 2):
                vandermonde *= F(j-i, 1 << ell)
            assert coef[3] == vandermonde > 0
            assert all((x*R**3).denominator == 1 for x in coef)
            assert abs(coef[1]) <= 72*B*B
            assert abs(coef[2]) <= 36*B
            assert abs(coef[3]) <= 6
            first = next(i for i, x in enumerate(coef) if x)
            assert abs(coef[first]) >= F(1, R**3)
            tail = sum((coef[i]*w**(i-first) for i in range(first+1, 4)), F(0))
            assert abs(tail) <= 114*B*B*w < abs(coef[first])
            direct_det = det(*(sub(perturbed[j], perturbed[a]) for j in (b, c, d)))
            assert direct_det == (1-theta)**3*sum((coef[i]*w**i for i in range(4)), F(0))
            polynomial_checks += 1
    pair_distances = [max(abs(x-y) for x, y in zip(p, q))
                      for p, q in combinations(perturbed, 2)]
    assert min(pair_distances) > 0
    all_original_keys_identical = len(set(points)) == 1
    if all_original_keys_identical:
        assert max(pair_distances) <= 2*theta
    metadata = {
        'variant': variant, 'keys_and_queries': n, 'ell': ell, 'entry_bound_n_to_10': B,
        'R_power_of_two_exponent': R.bit_length()-1,
        'theta_power_of_two_exponent': -theta_exponent,
        'M_power_of_two_exponent': 200*ell if variant == 'random_grid' else None,
        'moment_curve_parameter_denominator_exponent': ell if variant != 'random_grid' else None,
        'D_power_of_two_exponent': D.bit_length()-1,
        'all_original_keys_identical': all_original_keys_identical,
        'original_general_position': general_position(points),
        'perturbed_general_position': True,
        'quadruple_determinants_checked': len(determinants),
        'quadruple_condition_vacuous': n < 4,
        'smallest_abs_affine_determinant_binary_floor':
            dyadic_floor(min(determinants)) if determinants else None,
        'smallest_pair_L_infinity_distance_binary_floor': dyadic_floor(min(pair_distances)),
        'largest_pair_L_infinity_distance_binary_floor': dyadic_floor(max(pair_distances)),
        'output_perturbation_bound_checked_exactly': True,
        'union_bound_n_count_checked_exactly': variant == 'random_grid',
        'determinant_polynomial_identity_checks': polynomial_checks,
        'deterministic_tail_bound_checked_exactly': variant != 'random_grid',
    }
    return perturbed, rounded_queries, rounded_values, D, metadata


def main():
    start_time = time.perf_counter()
    seed = 20261006
    rng = random.Random(seed)
    stats = Counter()
    cases = []
    generic = random_general_position(rng, 28, 30)
    assert general_position(generic)
    cases.append(('generic', generic))
    cases.append(('slender', [tuple(p[a]*s for a, s in enumerate((F(1), F(1, 10**4), F(1, 10**8))))
                              for p in generic]))
    tetra = [(-100, -100, -100), (100, 0, 0), (0, 100, 0), (0, 0, 100)]
    interior = random_general_position(rng, 26, 10, tetra)
    rng.shuffle(interior)
    cases.append(('many_interior_keys', interior))
    moment = [(F(t), F(t*t), F(t*t*t)) for t in range(-12, 13)]
    cases.append(('moment_curve', moment))
    cube = [tuple(F(x) for x in p) for p in product((-1, 1), repeat=3)]
    cases.append(('degenerate_cube', cube))
    cases.append(('duplicates_and_signed_values', cube+cube[:3]+[(F(0),)*3]))
    cases.append(('rank_two', [(F(i), F(i*i), F(0)) for i in range(-4, 5)]))
    cases.append(('small_leaf', [(F(0), F(0), F(0)), (F(1), F(0), F(0))]))
    instance_summary = []
    for ci, (name, points) in enumerate(cases):
        queries = query_list(points, rng)
        values = [F(rng.randint(-4, 4), 4) for _ in points]
        for T in (F(1, 2), F(3), F(40)):
            for trial in range(3):
                run_instance(points, queries, values, T, seed+ci*100+trial, stats, checked=True)
                stats['instances'] += 1
        # Also exercise the exact partition logic of a valid but insufficient
        # sample. The production proof would direct-fallback if this sample
        # exceeds its conflict threshold; this run tests no complexity claim.
        if name in ('generic', 'slender', 'moment_curve'):
            run_instance(points, queries, values, F(3), seed+ci*100+99, stats, checked=False)
            stats['instances'] += 1
            stats['unchecked_shrink_diagnostic_instances'] += 1
        instance_summary.append({'name': name, 'keys': len(points), 'queries': len(queries)})

    preprocessing_summary = []
    preprocessing_specs = [
        (variant, ci, name, n)
        for variant in ('random_grid', 'deterministic_moment_curve')
        for ci, (name, n) in enumerate((('duplicate_large_coordinates', 8),
                                        ('rank_two_original', 10)))
    ]
    preprocessing_specs.append(('deterministic_moment_curve', 2, 'two_key_endpoint_case', 2))
    for variant, ci, name, n in preprocessing_specs:
        B = n**10
        if ci == 0:
            points = [(F(B), F(-B, 3), F(B, 7))]*n
        elif ci == 1:
            points = [(F(i, 3), F(i*i, 7), F(0)) for i in range(-5, 5)]
        else:
            points = [(F(B), F(-B), F(0)), (F(-B), F(B), F(0))]
        query_patterns = [
            (0, 0, 0), (B, -B, B), (-B, B, -B),
            (B, B, -B), (-B, -B, B), (0, 0, B),
            (0, 0, -B), (F(B, 3), F(-B, 7), B),
            (-B, F(B, 3), 0), (B, 0, F(-B, 7)),
        ]
        queries = [tuple(F(x) for x in p) for p in query_patterns[:n]]
        values = [F((-1)**j*(j+1), n) for j in range(n)]
        prep_start = time.perf_counter()
        ps, qs, vs, D, metadata = finite_preprocess(points, queries, values, seed+800+ci,
                                                 variant=variant)
        T = F(32*metadata['ell'])
        before = Counter(stats)
        trials = 1 if n == 2 else 2
        for trial in range(trials):
            run_instance(ps, qs, vs, T, seed+900+ci*100+trial, stats,
                         checked=True, common_denominator=D)
            stats['instances'] += 1
            stats['finite_preprocessing_instances'] += 1
        metadata.update({
            'name': name, 'T': int(T), 'sampling_trials': trials,
            'sample_hulls_checked': stats['sample_hulls']-before['sample_hulls'],
            'accepted_nonempty_bad_children':
                stats['checked_nonempty_bad_children']-before['checked_nonempty_bad_children'],
            'diagnostic_wall_seconds': round(time.perf_counter()-prep_start, 6),
        })
        assert n <= 6 or metadata['sample_hulls_checked'] > 0
        preprocessing_summary.append(metadata)
    assert stats['checked_nonempty_bad_children'] > 0
    assert stats['checked_maximum_depth'] >= 2
    assert stats['queries_on_cone_boundaries'] > 0
    assert stats['maximum_normal_cone_polygon_size'] > 3
    assert stats['conflict_fallbacks'] > 0 and stats['degenerate_fallbacks'] > 0
    result = {
        'status': 'PASS', 'seed': seed,
        'scope': 'Finite exact sampled-hull selection and signed-moment checks; not a fast implementation or a complexity proof.',
        'arithmetic': 'Python standard-library Fraction and integers only; no floating-point acceptance tests.',
        'finite_test_parameters': {
            'bernoulli_probability': '1/2 plus the first four fixed keys',
            'base_key_count': 6,
            'checked_facet_conflict_bound': 'p/4, so each accepted child has at most 3p/4 keys',
            'theorem_probability_constants_used': False,
            'reason': 'The asymptotic theorem constants would send every small instance directly to a leaf; these reduced parameters exercise the exact geometric and algebraic mechanism.',
            'extra_diagnostics': 'Three runs omit the shrink rejection and check only exact selection correctness for poor samples. They make no time-complexity assertion.',
            'moment_degree': 3,
            'error_bound_scope': 'Degree-three contractions check exact reconstruction identities only. The inverse-polynomial approximation error is proved analytically in the paper, not tested by this degree-three diagnostic.',
        },
        'cases': instance_summary,
        'finite_preprocessing_cases': preprocessing_summary,
        'theorem_preprocessing_variant': 'deterministic_moment_curve',
        'finite_preprocessing_scope': 'The deterministic moment-curve cases use the final theorem R, theta=2^(-128 ell), D=R*2^(128 ell), and T, including n=2. Random-grid cases retain an earlier proof-draft variant. The tests verify magnitude, grid membership, affine determinants, perturbation error bounds, and the applicable union bound or exact determinant-polynomial domination. All use n keys and n queries; recursive sample and leaf thresholds remain reduced. Degree three checks identities only.',
        'diagnostic_wall_seconds': round(time.perf_counter()-start_time, 6),
        'counts': dict(sorted(stats.items())),
    }
    Path(__file__).with_name('sample_hull_check_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
