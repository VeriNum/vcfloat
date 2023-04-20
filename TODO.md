# Possible future work in VCFloat

- Common-subexpression elimination, by means of let-expressions, for the purposes of combining redundant deltas and epsilons
- Automatically calculate annotations (Norm, Denorm, Sterbenz)
- Allow relative/absolute errors on input variables
- Allow generalized floating formats (double-double, etc.)
- Allow flush-to-zero-on-underflow representations (i.e., without denormal numbers). 
     Remark: In such formats, Sterbenz subtraction works only in the normal range.
- Interval package could use hardware floats instead of synthesized, 
     but only where extra precision is not neeeded
- Make things a bit more efficient by better leveraging reflection and lemmas
- Use the affine algorithm from FPTaylor
- Avoid exponential blowup in prune_terms (might not be needed if we use the affine/FPTaylor algorithm)
