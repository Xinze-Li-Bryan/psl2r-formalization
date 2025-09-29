# The Min-Max Construction of Minimal Surfaces in Lean4

📊 **[View Live Blueprint](https://min-max-construction.zeabur.app/)** - Interactive dependency graph and formalization progress

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

blueprint/
├── src/                   - LaTeX source files for the blueprint
├── web/                   - Generated HTML with interactive dependency graph
└── lean_decls            - Lean declarations mapping
```

## Blueprint Visualization

The project includes an interactive blueprint that visualizes the dependency graph of theorems and definitions.

### Viewing the Blueprint Online

🌐 **[min-max-construction.zeabur.app](https://min-max-construction.zeabur.app/)** - Live deployment (auto-updates on push)

### Viewing Locally

For local development:

```bash
cd blueprint/web
python3 -m http.server 8000
# Then open http://localhost:8000
```

### Blueprint Features

- **Interactive dependency graph**: Shows relationships between theorems and definitions
- **Progress tracking**: Color-coded nodes indicate formalization status
- **LaTeX-Lean linking**: Click to navigate between mathematical statements and Lean code
- **Legend**:
  - Blue border: Statement ready to formalize
  - Green border: Statement formalized
  - Green background: Proof formalized

## Key Concepts to Formalize

### ✅ Completed (Framework)

- Closed Riemannian 3-manifolds (`ClosedRiemannian3Manifold`)
- Embedded surfaces (`EmbeddedSurface`)
- Varifolds structure (`Varifold`, `IntegerVarifold`)
- Generalized families of surfaces (`GeneralizedFamily`)
- Saturated sets (`SaturatedSet`)
- Min-max sequences (`MinMaxSequence`)
- Basic theorem statement (`simon_smith`)
- Blueprint dependency visualization

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

# Build documentation
lake -Kenv=dev build MinimalSurfaces:docs

# Generate blueprint
cd blueprint
leanblueprint web

# Clean build
lake clean
lake build
```

### Updating the Blueprint

To update the online blueprint after making changes:

```bash
# Use the update script
~/update-blueprint.sh

# Or manually:
cd blueprint
leanblueprint web
cd ..
cp -r blueprint/web/* .
git add *.html js styles declarations *.svg
git commit -m "Update blueprint"
git push origin main
```

The blueprint at [min-max-construction.zeabur.app](https://min-max-construction.zeabur.app/) will automatically update within a few minutes.

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

1. View blueprint locally (optional):

```bash
cd blueprint
leanblueprint web
python3 -m http.server 8000 --directory web
# Open http://localhost:8000 in browser
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
- Extending the blueprint with more theorem dependencies

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
- [x] Blueprint visualization with dependency graph
- [x] Online deployment with auto-update
- [ ] Complete varifold theory
- [ ] Implement min-max procedure
- [ ] Prove main theorem
- [ ] Full documentation

## Contact

- GitHub Issues: [Project Issues](https://github.com/Xinze-Li-Bryan/The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4/issues)
- Author: Xinze Li

---

*This formalization project aims to make advanced geometric measure theory accessible and verifiable through formal mathematics.*
