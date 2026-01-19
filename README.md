# Poncelet's closure theorem

[![Documentation](https://img.shields.io/badge/Documentation-passing-green)](https://wwylele.github.io/Poncelet/docs/)
[![Blueprint](https://img.shields.io/badge/Blueprint-WIP-blue)](https://wwylele.github.io/Poncelet/blueprint/)

⚠ **WARNING: the main statements in the repo depend on more axioms than the "standard three"**. It additionally depends on `Lean.ofReduceBool` and
`Lean.trustCompiler` because of `native_decide` usage in the `Poncelet/Heavy/` folder. These
in principle can be replaced by `decide +kernel` but I don't think any PC can finish those proofs
with kernel only.

## Status

Main statements
 - `EuclideanGeometry.poncelet`: one circle in another on Euclidean plane.
 - TODO: intersecting circles, cotangent circles, and separate circles
 - TODO: conics in projective plane