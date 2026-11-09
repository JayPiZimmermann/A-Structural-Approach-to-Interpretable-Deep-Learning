"""Exact rational check: enumerate complete source histories vs matrix kernels.

This is finite independent review evidence, not a proof for arbitrary networks.
The history side retains stop, outside, and bias as distinct events. The other
side constructs the two parity matrices without constructing game histories.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent


def source_histories(layers, forward, layer, j, owner, epsilon, alpha, beta, forced_last=False):
    if layer < 0:
        return [(F(1), F(1), (j, owner), ("input",))]
    weights, bias = layers[layer]
    inputs = forward[layer]
    row = weights[j]
    z = sum((w * x for w, x in zip(row, inputs)), F(0)) + bias[j]
    if z <= 0 and not (forced_last and layer == len(layers) - 1):
        return [(F(1), F(1), None, ("stop",))]
    histories = []
    for sign, discount in [(False, 2 * alpha), (True, 2 * beta)]:
        next_owner = owner ^ sign
        if layer == 0:
            mass = [max((-1 if sign else 1) * w * x, F(0))
                    for w, x in zip(row, inputs)]
        else:
            mass = [max((-1 if sign else 1) * w, F(0)) * x
                    for w, x in zip(row, inputs)]
        bias_mass = max((-1 if sign else 1) * bias[j], F(0))
        total = epsilon + bias_mass + sum(mass, F(0))
        if total == 0:
            histories.append((F(1, 2), discount, None, (sign, "outside-empty")))
            continue
        histories.append((epsilon / total / 2, discount, None, (sign, "outside")))
        histories.append((bias_mass / total / 2, discount, None, (sign, "bias")))
        for i, weight in enumerate(mass):
            child = ([(F(1), F(1), (i, next_owner), ("fused-input",))]
                     if layer == 0 else source_histories(
                         layers, forward, layer - 1, i, next_owner, epsilon, alpha, beta,
                         forced_last))
            for prob, branch_discount, endpoint, event in child:
                histories.append((weight / total / 2 * prob,
                                  discount * branch_discount, endpoint, (sign, i, event)))
    return histories


def parity_matrices(layers, forward, epsilon, alpha, beta, forced_last=False):
    n = len(forward[0])
    pos = [[F(i == j) for i in range(n)] for j in range(n)]
    neg = [[F(0) for _ in range(n)] for _ in range(n)]
    for depth, (weights, bias) in enumerate(layers):
        new_pos, new_neg = [], []
        for row, b in zip(weights, bias):
            products = [w * x for w, x in zip(row, forward[depth])]
            a = [max(z, F(0)) for z in products]
            c = [max(-z, F(0)) for z in products]
            dp = sum(a, F(0)) + max(b, F(0)) + epsilon
            dn = sum(c, F(0)) + max(-b, F(0)) + epsilon
            active = sum(products, F(0)) + b > 0 or (forced_last and depth == len(layers) - 1)
            p = [(alpha * z / dp if dp and active else F(0)) for z in a]
            q = [(beta * z / dn if dn and active else F(0)) for z in c]
            new_pos.append([sum((p[k] * pos[k][i] + q[k] * neg[k][i]
                                 for k in range(len(row))), F(0)) for i in range(n)])
            new_neg.append([sum((p[k] * neg[k][i] + q[k] * pos[k][i]
                                 for k in range(len(row))), F(0)) for i in range(n)])
        pos, neg = new_pos, new_neg
    return pos, neg


def run_case(case):
    layers = [([[F(v) for v in row] for row in w], [F(v) for v in b])
              for w, b in case["layers"]]
    inputs = [F(v) for v in case["input"]]
    forward = [inputs]
    for weights, bias in layers:
        forward.append([max(sum((w * x for w, x in zip(row, forward[-1])), F(0)) + b, F(0))
                        for row, b in zip(weights, bias)])
    epsilon, alpha, beta = map(F, [case["epsilon"], case["alpha"], case["beta"]])
    forced_last = case["forced_last"]
    if case["label"] == "ungated-negative-logit":
        weights, bias = layers[-1]
        assert sum((w * x for w, x in zip(weights[0], forward[-2])), F(0)) + bias[0] < 0
    if case["label"] == "ungated-zero-logit":
        weights, bias = layers[-1]
        assert sum((w * x for w, x in zip(weights[0], forward[-2])), F(0)) + bias[0] == 0
    pos, neg = parity_matrices(layers, forward, epsilon, alpha, beta, forced_last)
    count = 0
    for j, owner in product(range(len(forward[-1])), [False, True]):
        histories = source_histories(layers, forward, len(layers) - 1,
                                    j, owner, epsilon, alpha, beta, forced_last)
        count += len(histories)
        assert all(prob >= 0 for prob, _, _, _ in histories)
        assert sum((prob for prob, _, _, _ in histories), F(0)) == 1
        for i, endpoint_owner in product(range(len(inputs)), [False, True]):
            actual = sum((prob * discount for prob, discount, endpoint, _ in histories
                          if endpoint == (i, endpoint_owner)), F(0))
            expected = (neg if owner ^ endpoint_owner else pos)[j][i]
            assert actual == expected, (case, i, owner, endpoint_owner, actual, expected)
    return count


def main():
    architectures = [
        ("identity-signed", ["-2", "3"], []),
        ("positive-empty-negative", ["2"], [([ ["3"] ], ["0"])]),
        ("signed-fused-negative-weight", ["-2", "3"], [([ ["-1", "-1"] ], ["5"])]),
        ("exact-preactivation-tie", ["2", "1"], [([ ["1", "-2"] ], ["0"])]),
        ("zero-width-bias-only", [], [([[]], ["2"])]),
        ("zero-width-zero-tie", [], [([[]], ["0"])]),
        ("negative-bias-and-mixed-streams", ["3", "1"], [([ ["2", "-1"] ], ["-2"])]),
        ("two-layers-owner-reversal", ["-2", "1"],
         [([ ["-2", "1"], ["1", "3"] ], ["-1", "1"]),
          ([ ["-1", "2"], ["2", "-1"] ], ["3", "-1"])]),
        ("three-layers-stopping-subtree", ["-1", "2"],
         [([ ["1", "0"], ["0", "1"] ], ["0", "0"]),
          ([ ["2", "-1"], ["-1", "2"] ], ["4", "0"]),
          ([ ["1", "-1"] ], ["4"])]),
        ("empty-intermediate", ["2"], [([], []), ([[]], ["3"])]),
        ("no-output", ["2"], [([], [])]),
        ("ungated-negative-logit", ["2"], [([["1"]], ["0"]), ([["-3"]], ["1"])]),
        ("ungated-zero-logit", ["2"], [([["1"]], ["0"]), ([["1"]], ["-2"])]),
        ("ungated-negative-bias-zero-width", [], [([], []), ([[]], ["-3"])]),
    ]
    cases = []
    for (label, inputs, layers), epsilon, coeffs in product(
            architectures, ["0", "1/3", "2"],
            [("1", "0"), ("2", "1"), ("1/2", "3/2"), ("-1", "2")]):
        cases.append(dict(label=label, input=inputs, layers=layers, epsilon=epsilon,
                          alpha=coeffs[0], beta=coeffs[1], forced_last=label.startswith("ungated-")))
    encoded = json.dumps(cases, indent=2) + "\n"
    (OUT / "experiment-cases.json").write_text(encoded)
    paths = sum(run_case(case) for case in cases)
    report = {
        "status": "passed",
        "arithmetic": "exact fractions.Fraction rational arithmetic",
        "cases": len(cases),
        "complete_histories_enumerated": paths,
        "case_sha256": hashlib.sha256(encoded.encode()).hexdigest(),
        "checks": ["full probability nonnegativity", "full probability normalization",
                   "individual owner endpoint occupation vs independent parity matrices"],
        "boundaries": [a[0] for a in architectures],
        "limitations": "Finite exact experiment only; no Lean proof or off-equilibrium/SPNE certificate. Includes a signed alpha case to test algebraic identity beyond nonnegative-occupation scope.",
    }
    (OUT / "experiment-results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
