# Min-Max Construction of Minimal Surfaces

A formalization of the Colding-De Lellis paper "The min-max construction of minimal surfaces" in Lean 4.

## Main Goal

Formalize **Theorem 1.6 (Simon-Smith)**: 
> Let M be a closed 3-manifold with a Riemannian metric. For any saturated set of generalized families of surfaces Λ, there is a min–max sequence obtained from Λ and converging in the sense of varifolds to a smooth embedded minimal surface with area m₀(Λ).

## Project Structure

- `MinimalSurfaces/Basic.lean` - Basic definitions of manifolds and surfaces
- `MinimalSurfaces/Varifolds/` - Varifold theory
- `MinimalSurfaces/MinMax/` - Min-max theory and main theorem
- `MinimalSurfaces/Convergence/` - Convergence theory

## References

- [Colding-De Lellis: The min-max construction of minimal surfaces](https://arxiv.org/abs/math/0303305)
- Original works: Pitts (1981), Simon-Smith

## Status

🚧 Work in Progress - See blueprint for current progress
