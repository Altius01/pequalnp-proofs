"""Enumerate circuits of at most five binary forks routing three bits to three outputs.

Each receiver requests one of the three bits. For every demand, the local Boolean
functions may be chosen afresh. This relaxes a matrix-product circuit with its
column selectors fixed. Complementing a wire can always be absorbed downstream,
so only internal truth tables that vanish on input 000 need be enumerated.
"""
from functools import lru_cache
from itertools import combinations, permutations, product

INPUT_BITS = (0xAA, 0xCC, 0xF0)  # eight truth-table rows for three input bits
DEMANDS = tuple(dict.fromkeys((*permutations(range(3)), *product(range(3), repeat=3))))


@lru_cache(None)
def possible_tables(input_tables):
    classes = [255]
    for table in input_tables:
        classes = [part for old in classes for part in (old & table, old & ~table) if part]
    tables = [0]
    for part in classes:
        if not part & 1:
            tables += [current | part for current in tables]
    return frozenset(tables)


def can_route(fork_outputs, source_forks):
    forks = len(fork_outputs)
    parents = [[] for _ in range(forks + 3)]
    for source, destinations in enumerate(fork_outputs):
        for dest in destinations:
            parents[dest].append(source)
    for i, source in enumerate(source_forks):
        parents[source].append(forks + 3 + i)
    signals = [0] * (forks + 3) + list(INPUT_BITS)
    last_parent = [max(ports, default=-1) for ports in parents[forks:]]

    def options(node):
        return possible_tables(tuple(sorted({signals[p] for p in parents[node]})))

    def search(i, demand):
        for out, last in enumerate(last_parent):
            if last == i - 1 and INPUT_BITS[demand[out]] not in options(forks + out):
                return False
        if i == forks:
            return True
        for table in options(i):
            signals[i] = table
            if search(i + 1, demand):
                return True
        return False

    return all(search(0, demand) for demand in DEMANDS)


def reachable(fork_outputs, removed):
    forks = len(fork_outputs)
    mask = [0] * forks + [0 if forks+i in removed else 1 << i for i in range(3)]
    for node in reversed(range(forks)):
        left, right = fork_outputs[node]
        if node not in removed:
            mask[node] = mask[left] | mask[right]
    return mask


def enumerate_cores(forks):
    # Every fork sends its two copies forward. If both feed the same destination,
    # the duplicate adds no information and can instead go to another destination.
    destinations = [tuple(combinations(range(i+1, forks+3), 2)) for i in range(forks)]
    all_reachable = passes_cuts = passes_truth_tables = 0
    for edges in product(*destinations):
        start = [i for i, mask in enumerate(reachable(edges, ())[:forks]) if mask == 7]
        if len(start) < 3:
            continue
        one_removed = [reachable(edges, (i,)) for i in range(forks+3)]
        two_removed = [reachable(edges, pair) for pair in combinations(range(forks+3), 2)]
        # Source names are interchangeable because all demands must be served.
        for sources in combinations(start, 3):
            all_reachable += 1
            if any((mask[a] | mask[b]).bit_count() < 2
                   for mask in one_removed for a, b in combinations(sources, 2)):
                continue
            if any(not any(mask[a] for a in sources) for mask in two_removed):
                continue
            passes_cuts += 1
            if can_route(edges, sources):
                passes_truth_tables += 1
    return all_reachable, passes_cuts, passes_truth_tables


if __name__ == '__main__':
    control = ((3,6), (4,6), (5,6), (7,8), (7,8), (7,8))
    assert can_route(control, (0,1,2))
    for count in (3, 4, 5):
        print(count, *enumerate_cores(count))
