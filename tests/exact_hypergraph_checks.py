"""Independent exact enumeration of finite labelled hyperedge inequalities.

An edge is (incident_vertices, numerator, denominator). Integer configuration
weights have a common denominator, so every comparison below is exact.
"""
from itertools import combinations
from random import Random


def states(vertex_count, edges):
    denominator = 1
    for _, _, probability_denominator in edges:
        denominator *= probability_denominator
    configurations = []
    for mask in range(1 << len(edges)):
        weight = 1
        parent = list(range(vertex_count))

        def find(vertex):
            while parent[vertex] != vertex:
                vertex = parent[vertex]
            return vertex

        for index, (vertices, numerator, divisor) in enumerate(edges):
            is_open = (mask >> index) & 1
            weight *= numerator if is_open else divisor - numerator
            if is_open and vertices:
                for vertex in vertices[1:]:
                    parent[find(vertex)] = find(vertices[0])
        if weight:
            clusters = [sum(1 << other for other in range(vertex_count)
                            if find(other) == find(vertex))
                        for vertex in range(vertex_count)]
            configurations.append((weight, clusters))
    assert sum(weight for weight, _ in configurations) == denominator
    return denominator, configurations


def check(vertex_count, edges, check_functions=False):
    denominator, configurations = states(vertex_count, edges)
    connection = [[sum(weight for weight, clusters in configurations
                       if clusters[a] >> b & 1)
                   for b in range(vertex_count)] for a in range(vertex_count)]
    checks = 0
    for relay_mask in range(1, 1 << vertex_count):
        relays = [a for a in range(vertex_count) if relay_mask >> a & 1]
        for origin in range(vertex_count):
            hit = sum(weight for weight, clusters in configurations
                      if clusters[origin] & relay_mask)
            for target in range(vertex_count):
                joint = sum(weight for weight, clusters in configurations
                            if clusters[origin] & relay_mask
                            and clusters[origin] >> target & 1)
                assert denominator * joint >= hit * min(connection[a][target] for a in relays), (
                    edges, origin, target, relay_mask)
                checks += 1
    if check_functions:
        functions = [lambda cluster: bin(cluster).count("1") ** 2]
        functions.extend(lambda cluster, required=required: int(cluster & required == required)
                         for required in (1, 3, 7))
        for function in functions:
            means = [sum(weight * function(clusters[a]) for weight, clusters in configurations)
                     for a in range(vertex_count)]
            for relay_mask in range(1, 1 << vertex_count):
                relays = sorted((a for a in range(vertex_count) if relay_mask >> a & 1),
                                key=lambda a: (means[a], a))
                for origin in range(vertex_count):
                    left = sum(weight * function(clusters[origin])
                               for weight, clusters in configurations if clusters[origin] & relay_mask)
                    right = sum(weight * means[next(a for a in relays if clusters[origin] >> a & 1)]
                                for weight, clusters in configurations if clusters[origin] & relay_mask)
                    assert denominator * left >= right, ("first contact", edges, origin, relay_mask)
                    for relay in relays:
                        if means[relay] != means[relays[0]]:
                            break
                        fixed = sum(weight * function(clusters[relay])
                                    for weight, clusters in configurations if clusters[origin] & relay_mask)
                        assert left >= fixed, ("fixed minimizer", edges, origin, relay_mask, relay)
    return checks, len(configurations)


def main():
    checks = configuration_count = 0
    possible_edges = [edge for size in range(2, 5) for edge in combinations(range(4), size)]
    for mask in range(1 << len(possible_edges)):
        edges = [(edge, 1, 2) for index, edge in enumerate(possible_edges) if mask >> index & 1]
        count, configurations = check(4, edges)
        checks += count
        configuration_count += configurations
    print("Exhaustive four-vertex hypergraphs:", 1 << len(possible_edges),
          "states:", configuration_count, "strong gluing inequalities:", checks, flush=True)
    random = Random(20260905)
    for _ in range(100):
        edges = []
        for _ in range(random.randrange(3, 9)):
            vertices = tuple(vertex for vertex in range(5) if random.random() < 0.5)
            divisor = random.choice((2, 3, 5))
            edges.append((vertices, random.randrange(divisor + 1), divisor))
        check(5, edges, check_functions=True)
    print("Nonuniform five-vertex labelled models: 100; strong gluing, first-contact",
          "and fixed-minimizer checks passed", flush=True)


if __name__ == "__main__":
    main()
