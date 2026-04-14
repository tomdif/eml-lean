#!/usr/bin/env python3
"""
Brute-force search for minimal EML trees, reproducing the paper's
exhaustive search (Section 2, Table 4).

eml(x, y) = exp(x) - ln(y)

Grammar: S -> 1 | x | eml(S, S)    (unary functions)
         S -> 1 | x | y | eml(S, S) (binary functions)

We evaluate at algebraically independent transcendental constants
(Euler-Mascheroni gamma, Glaisher-Kinkelin A) as the paper suggests,
to avoid coincidental matches (Schanuel conjecture).
"""
import math
import itertools
import sys

# Test values (algebraically independent transcendentals)
TEST_X1 = 0.5772156649015329  # Euler-Mascheroni gamma
TEST_X2 = 1.2824271291006226  # Glaisher-Kinkelin A
TEST_Y1 = 0.6931471805599453  # ln(2) - another transcendental
TEST_Y2 = 1.4426950408889634  # 1/ln(2)

def gen_trees(n):
    """Generate all full binary tree shapes with n internal nodes."""
    if n == 0:
        yield None  # leaf placeholder
        return
    for k in range(n):
        for left in gen_trees(k):
            for right in gen_trees(n - 1 - k):
                yield (left, right)

def count_leaves(tree):
    if tree is None:
        return 1
    return count_leaves(tree[0]) + count_leaves(tree[1])

def eval_tree(tree, leaves, idx):
    """Evaluate an EML tree. Returns None on domain error."""
    if tree is None:
        val = leaves[idx[0]]
        idx[0] += 1
        return val
    left_val = eval_tree(tree[0], leaves, idx)
    if left_val is None:
        # still consume leaves from right subtree
        eval_tree(tree[1], leaves, idx)
        return None
    right_val = eval_tree(tree[1], leaves, idx)
    if right_val is None:
        return None
    try:
        if left_val > 500:
            return None  # exp overflow guard
        exp_val = math.exp(left_val)
        if right_val <= 0:
            return None
        log_val = math.log(right_val)
        result = exp_val - log_val
        if math.isnan(result) or math.isinf(result) or abs(result) > 1e200:
            return None
        return result
    except (OverflowError, ValueError, ZeroDivisionError):
        return None

def tree_to_str(tree, leaves, idx):
    """Convert tree + leaves to a readable string."""
    if tree is None:
        name = leaves[idx[0]]
        idx[0] += 1
        return name
    left = tree_to_str(tree[0], leaves, idx)
    right = tree_to_str(tree[1], leaves, idx)
    return f"eml({left}, {right})"

def tree_to_lean(tree, leaves, idx):
    """Convert tree + leaves to Lean EmlExpr syntax."""
    if tree is None:
        name = leaves[idx[0]]
        idx[0] += 1
        if name == '1':
            return '.one'
        elif name == 'x':
            return '.var'
        else:
            return '.varY'
    left = tree_to_lean(tree[0], leaves, idx)
    right = tree_to_lean(tree[1], leaves, idx)
    return f'(.app {left} {right})'

def search_unary(name, target_func, max_n):
    """Search for a unary function f(x) expressible as EML tree."""
    target1 = target_func(TEST_X1)
    target2 = target_func(TEST_X2)

    leaf_vals = {'1': None, 'x': None}

    for n in range(1, max_n + 1):
        trees = list(gen_trees(n))
        num_leaves = n + 1
        K = 2 * n + 1
        total = len(trees) * (2 ** num_leaves)
        print(f"  n={n} (K={K}): {len(trees)} shapes × {2**num_leaves} assignments = {total}")

        for tree in trees:
            for leaf_combo in itertools.product(['1', 'x'], repeat=num_leaves):
                # Evaluate at test point 1
                leaves1 = [1.0 if l == '1' else TEST_X1 for l in leaf_combo]
                result1 = eval_tree(tree, leaves1, [0])
                if result1 is None or abs(result1 - target1) > 1e-8:
                    continue

                # Verify at test point 2
                leaves2 = [1.0 if l == '1' else TEST_X2 for l in leaf_combo]
                result2 = eval_tree(tree, leaves2, [0])
                if result2 is None or abs(result2 - target2) > 1e-8:
                    continue

                expr = tree_to_str(tree, list(leaf_combo), [0])
                lean = tree_to_lean(tree, list(leaf_combo), [0])
                print(f"\n  *** FOUND {name} at K={K} ***")
                print(f"  Expression: {expr}")
                print(f"  Lean:       {lean}")
                print(f"  Eval(x={TEST_X1:.6f}) = {result1:.10f} (target {target1:.10f})")
                print(f"  Eval(x={TEST_X2:.6f}) = {result2:.10f} (target {target2:.10f})")
                return K, expr, lean, list(leaf_combo)

    print(f"  Not found up to n={max_n}")
    return None

def search_binary(name, target_func, max_n):
    """Search for a binary function f(x, y) expressible as EML tree."""
    target1 = target_func(TEST_X1, TEST_Y1)
    target2 = target_func(TEST_X2, TEST_Y2)

    for n in range(1, max_n + 1):
        trees = list(gen_trees(n))
        num_leaves = n + 1
        K = 2 * n + 1
        total = len(trees) * (3 ** num_leaves)
        print(f"  n={n} (K={K}): {len(trees)} shapes × {3**num_leaves} assignments = {total}")

        for tree in trees:
            for leaf_combo in itertools.product(['1', 'x', 'y'], repeat=num_leaves):
                # Must use both x and y at least once
                if 'x' not in leaf_combo or 'y' not in leaf_combo:
                    continue

                leaves1 = [1.0 if l == '1' else TEST_X1 if l == 'x' else TEST_Y1 for l in leaf_combo]
                result1 = eval_tree(tree, leaves1, [0])
                if result1 is None or abs(result1 - target1) > 1e-8:
                    continue

                leaves2 = [1.0 if l == '1' else TEST_X2 if l == 'x' else TEST_Y2 for l in leaf_combo]
                result2 = eval_tree(tree, leaves2, [0])
                if result2 is None or abs(result2 - target2) > 1e-8:
                    continue

                expr = tree_to_str(tree, list(leaf_combo), [0])
                lean = tree_to_lean(tree, list(leaf_combo), [0])
                print(f"\n  *** FOUND {name} at K={K} ***")
                print(f"  Expression: {expr}")
                print(f"  Lean:       {lean}")
                print(f"  Eval(x={TEST_X1:.4f},y={TEST_Y1:.4f}) = {result1:.10f} (target {target1:.10f})")
                print(f"  Eval(x={TEST_X2:.4f},y={TEST_Y2:.4f}) = {result2:.10f} (target {target2:.10f})")
                return K, expr, lean, list(leaf_combo)

    print(f"  Not found up to n={max_n}")
    return None

if __name__ == '__main__':
    print("=" * 60)
    print("EML Tree Search — reproducing paper's Table 4")
    print("=" * 60)

    print("\n--- Searching for -x ---")
    result_neg = search_unary("-x", lambda x: -x, 8)

    print("\n--- Searching for 1/x ---")
    result_inv = search_unary("1/x", lambda x: 1.0/x, 8)

    print("\n--- Searching for x-y ---")
    result_sub = search_binary("x-y", lambda x, y: x - y, 6)

    print("\n--- Searching for x*y ---")
    result_mul = search_binary("x*y", lambda x, y: x * y, 8)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for name, result in [("-x", result_neg), ("1/x", result_inv),
                          ("x-y", result_sub), ("x*y", result_mul)]:
        if result:
            print(f"  {name}: K={result[0]}, {result[1]}")
        else:
            print(f"  {name}: NOT FOUND")
