# The Min-Max Construction of Minimal Surfaces in Lean4

A formalization of the Colding-De Lellis paper "The min-max construction of minimal surfaces" in Lean 4.

## Main Goal

Formalize **Theorem 1.6 (Simon-Smith)**:
> Let M be a closed 3-manifold with a Riemannian metric. For any saturated set of generalized families of surfaces Λ, there is a min–max sequence obtained from Λ and converging in the sense of varifolds to a smooth embedded minimal surface with area m₀(Λ) (multiplicity is allowed).

## Project Structure

```bash
MinimalSurfaces/
├── Basic.lean              - Basic definitions of manifolds and surfaces
├── Varifolds/
│   └── Basic.lean         - Varifold theory (Geometric Measure Theory)
├── MinMax/
│   └── Basic.lean         - Min-max theory and main theorem
└── Convergence/
    └── Basic.lean         - Convergence theory in varifold sense
```

## Key Concepts to Formalize

### ✅ Completed (Framework)

- Closed Riemannian 3-manifolds (`ClosedRiemannian3Manifold`)
- Embedded surfaces (`EmbeddedSurface`)
- Varifolds structure (`Varifold`, `IntegerVarifold`)
- Generalized families of surfaces (`GeneralizedFamily`)
- Saturated sets (`SaturatedSet`)
- Min-max sequences (`MinMaxSequence`)
- Basic theorem statement (`simon_smith`)

### 🚧 In Progress

- Area functional implementation using Hausdorff measure
- Mean curvature definition
- Varifold convergence precise definition
- Saturated set properties

### 📋 TODO

- First and second fundamental forms
- Regularity theory
- Compactness theorems
- Generic finiteness results
- Multiplicity one theorem

## Mathematical Components

### Geometric Measure Theory

- **Varifolds**: Radon measures on Grassmann bundles
- **Integer rectifiable varifolds**: With multiplicity functions
- **Mass functional**: Generalization of area

### Min-Max Theory

- **Sweep-outs**: 1-parameter families of surfaces
- **Width**: inf-sup of area over families
- **Saturation**: Closure under homotopies

### Convergence Theory

- **Varifold convergence**: Weak-* convergence of measures
- **Regularity**: From varifolds to smooth surfaces
- **Compactness**: Existence of convergent subsequences

## Building

```bash
# Build the project
lake build MinimalSurfaces

# Clean build
lake clean
lake build
```

## Installation

1. Install Lean 4:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

1. Clone the repository:

```bash
git clone https://github.com/Xinze-Li-Bryan/The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4.git
cd The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4
```

1. Build:

```bash
lake build
```

## Contributing

This is an open project and contributions are welcome!

### How to Contribute

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/AddSomeDefinition`)
3. Commit your changes (`git commit -m 'Add definition of X'`)
4. Push to the branch (`git push origin feature/AddSomeDefinition`)
5. Open a Pull Request

### Priority Areas

- Implementing `sorry` placeholders
- Adding documentation and comments
- Creating examples
- Setting up Blueprint visualization

## Blueprint (Coming Soon)

We plan to use [leanblueprint](https://github.com/PatrickMassot/leanblueprint) to visualize the dependency graph and track progress.

## References

### Primary Source

- [Colding-De Lellis: The min-max construction of minimal surfaces](https://arxiv.org/abs/math/0303305) (2003)

### Classical Works

- Pitts, J.T. (1981). *Existence and regularity of minimal surfaces on Riemannian manifolds*. Mathematical Notes, Princeton University Press
- Simon, L. (1987). *Lectures on geometric measure theory*. Proceedings of the Centre for Mathematical Analysis, Australian National University

### Related Papers

- Almgren, F. (1965). The theory of varifolds
- Marques, F. & Neves, A. (2014). Min-max theory and the Willmore conjecture
- Smith, F. (1982). On the existence of embedded minimal 2-spheres in the 3-sphere

## License

This project is licensed under the Apache 2.0 License - see the LICENSE file for details.

## Status

🚧 **Work in Progress** - Framework established, working on mathematical details

### Milestones

- [x] Project setup with Mathlib
- [x] Basic structure definitions
- [x] Theorem statement
- [ ] Complete varifold theory
- [ ] Implement min-max procedure
- [ ] Prove main theorem
- [ ] Set up Blueprint visualization

## Contact

- GitHub Issues: [Project Issues](https://github.com/Xinze-Li-Bryan/The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4/issues)
- Author: Xinze Li

---

*This formalization project aims to make advanced geometric measure theory accessible and verifiable through formal mathematics.*
