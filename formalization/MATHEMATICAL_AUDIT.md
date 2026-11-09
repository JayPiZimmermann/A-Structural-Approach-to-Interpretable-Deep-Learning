# Mathematical audit: checked findings

Reported to the parent agent before paper corrections. The findings below distinguish
classical derivatives from a chosen automatic-differentiation mask at a nonsmooth point.

1. **Factor of two in the backward invariant.** The symmetric lift is
   `x ↦ (x/2,-x/2)`. Its derivative is `(partial_positive-partial_negative)/2`.
   Therefore the original gradient is half the difference of the two heads' partial
   differences. The invariant printed without one half is false. For one active
   scalar ReLU with weight 1, the four partials are `(1,0,0,1)`, giving 2 rather than 1.
   Checked by `lift_chain_rule`, `lift_differential`, and
   `paper_backward_invariant_counterexample`.

2. **Shift-product lower index.** In the hidden-monotonicity paper's
   `thm:closed_formula_shift`, the contribution arising when propagating through layer
   `j+1` uses shifts from layers `j+1,...,L`, not `j,...,L`. Equal subtraction at layer
   `j` cancels from that layer's signed difference. The thesis already uses
   `overline_alpha_(j+1)` and must not receive the paper's index correction twice.
   Counterexample: one inactive weight-1 ReLU, terminal shift zero, local input-layer
   shift 1/4. Head-g partials become `(-1/4,3/4)`, hence lift derivative `-1/2`.
   The printed product gives `-1/4`. Checked by `shifted_formula_counterexample`,
   `shifted_backward_difference`, `shifted_source_coefficient`.

3. **Missing weight/Jacobian factor.** The paper's final shifted recursion must have
   `2 delta_g^(l+1) W^(l+1,x)` before the source subtraction. Omitting this right
   multiplication is dimensionally wrong for unequal adjacent widths and numerically
   wrong already for a scalar active layer of weight 2. The exact rectangular identity
   is checked by `matrix_backward_difference`.

4. **Differentiability and common shifts.** ReLU is nonsmooth at zero. Classical
   derivative formulas require differentiability (e.g. strict nonzero preactivations).
   A selected mask at zero defines a computational convention, not a classical derivative.
   A constant common forward shift preserves the head derivatives where they exist;
   an input-dependent shift adds the derivative of its common-mode output. Example:
   `g=max(p,n)`, `h=n`, `p=x,n=0,x>0`, `c(x)=x`; the shifted heads are `2x,x`,
   rather than `x,0`. Their difference stays `x`. Detached shifts retain algorithmic
   sensitivities but should not be described as differentiating the shifted scalar function.

5. **Multiplication is not jointly convex on the positive quadrant.** For `f(x,y)=xy`,
   endpoints `(1,3)` and `(3,1)` have value 3, their midpoint `(2,2)` has value 4.
   Checked by `multiplicative_convexity_counterexample`. Nonnegative factors do not
   justify convexity of their product. A product decomposition can preserve its
   algebraic difference without establishing DC convexity.

6. **Auxiliary min-network Q.** Replacing all following activations by min(.,0) is
   valid for the bias-free absolute-weight tail: after the first min the activations
   are nonpositive, and nonnegative matrices preserve this cone. Arbitrary subsequent
   biases invalidate that reasoning. State the bias-free restriction or define Q with
   an explicitly linear absolute-weight tail. This point is analytically checked;
   a separate full Q-network derivative theorem is not included.

Additional source proof repairs identified analytically: difference quotients require
subtracting the base function value; the Jacobian product with the last activation mask
is the derivative of the activation `a`, not its preactivation `z`; bounding the number
of distinct multiplicative inputs does not bound their exponents (already `x^m` has
`m+1` binomial terms), whereas bounded total degree does.

The checked build establishes the listed Lean statements only; it does not establish
that every corrected prose claim, every equation, or either complete paper is correct.
