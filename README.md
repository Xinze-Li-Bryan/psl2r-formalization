# The Min-Max Construction of Minimal Surfaces in Lean4

## Main Goal

Formalize **Theorem 1.6 (Simon-Smith)**:
> Let M be a closed 3-manifold with a Riemannian metric. For any saturated set of generalized families of surfaces Λ, there is a min–max sequence obtained from Λ and converging in the sense of varifolds to a smooth embedded minimal surface with area m₀(Λ) (multiplicity is allowed).

## Project Structure

```bash
MinimalSurfaces/
├── Basic.lean              # Basic definitions of manifolds and surfaces
├── Area.lean              # Hausdorff measure and area functional
├── Isotopy.lean           # Isotopy and diffeomorphisms
├── Varifolds/
│   └── Basic.lean         # Varifold theory (Geometric Measure Theory)
├── MinMax/
│   └── Basic.lean         # Min-max theory and main theorem
└── Convergence/
    └── Basic.lean         # Convergence theory in varifold sense

blueprint/
├── src/                   # LaTeX source files for the blueprint
├── web/                   # Generated HTML with interactive dependency graph
└── lean_decls            # Lean declarations mapping
```

## Recent Progress (2025-09-29)

### ✅ Completed Today

- Fixed all Mathlib import paths (`BorelSpace`, `ContinuousMap`, etc.)
- Implemented `hausdorffArea` using 2-dimensional Hausdorff measure
- Added `GeneralizedFamilyOfSurfaces` and `Isotopy` structures
- Connected LaTeX blueprint definitions with Lean code
- Fixed `MinMaxSequence` and `SaturatedSet` type parameters
- Blueprint dependency graph now correctly displays all definitions

### 🔧 Technical Improvements

- Resolved all compilation errors in the project
- Added proper `BorelSpace` instances where needed
- Fixed `EmbeddedSurface` constructor (4 fields)
- Integrated `𝓝` (neighborhood filter) notation

## Blueprint Visualization

The project includes an interactive blueprint that visualizes the dependency graph of theorems and definitions.

### Viewing the Blueprint

🌐 **Online**: [min-max-construction.zeabur.app](https://min-max-construction.zeabur.app/)

- Automatically updates on push to main branch
- Shows real-time formalization progress

🖥️ **Local Development**:

```bash
cd ~/minimal_surfaces_new
python3 -m http.server 8001
# Open http://localhost:8001 in browser
```

### Blueprint Features

- **Interactive dependency graph**: Click nodes to see definitions
- **Color coding**:
  - 🔵 Blue border: Statement ready to formalize
  - 🟢 Green border: Statement formalized in Lean
  - ✅ Green background: Proof completed
- **LaTeX-Lean linking**: Direct navigation between math and code

## Key Formalized Structures

### Core Definitions

```lean
-- Manifold structure
class ClosedRiemannian3Manifold (M : Type*) 

-- Surface representation
structure EmbeddedSurface (M : Type*) where
  carrier : Set M
  is_closed : IsClosed carrier
  dim_two : True
  is_embedded : True

-- Varifold structures
structure Varifold (k n : ℕ) (M : Type*)
structure IntegerVarifold (k n : ℕ) (M : Type*)

-- Min-max machinery
structure GeneralizedFamilyOfSurfaces (M : Type*)
structure SaturatedSet (M : Type*)
structure MinMaxSequence (Λ : SaturatedSet M)
noncomputable def m0 (Λ : SaturatedSet M) : ℝ  -- Width functional
```

### Main Theorem Statement

```lean
theorem simon_smith (Λ : SaturatedSet M) :
  ∃ (seq : MinMaxSequence Λ) (S : EmbeddedSurface M),
    is_minimal S ∧ 
    area S = m0 Λ ∧
    ∃ (V : IntegerVarifold 2 3 M), 
      convergesInVarifoldSense (fun n => sorry) V.toVarifold
```

## Building & Development

### Quick Start

```bash
# Build the project
lake build MinimalSurfaces

# Update blueprint and deploy
~/update-blueprint.sh

# View local changes
python3 -m http.server 8001
```

### Manual Blueprint Update

```bash
cd blueprint
leanblueprint web
cd ..
cp -r blueprint/web/* .
git add *.html js styles declarations *.svg
git commit -m "Update blueprint"
git push origin main
```

## TODO List

### High Priority

- [ ] Implement `is_minimal` predicate (mean curvature = 0)
- [ ] Define proper varifold convergence
- [ ] Implement isotopy action on families
- [ ] Prove area functional properties

### Medium Priority

- [ ] First variation formula
- [ ] Monotonicity formula
- [ ] Allard regularity theorem
- [ ] Caccioppoli sets

### Future Work

- [ ] Complete compactness theory
- [ ] Generic finiteness results
- [ ] Multiplicity one theorem
- [ ] Full Simon-Smith theorem proof

## Mathematical Components

### Geometric Measure Theory

- **Hausdorff Measure**: 2-dimensional measure for surfaces
- **Varifolds**: Generalized surfaces as measures on Grassmann bundles
- **Convergence**: Weak-* convergence in measure spaces

### Min-Max Theory

- **Width**: inf-sup characterization of minimal surfaces
- **Saturation**: Closure under diffeomorphisms
- **Min-max sequences**: Realizing the width

## Installation

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone repository
git clone https://github.com/Xinze-Li-Bryan/The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4.git
cd The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4

# Build with Mathlib cache
lake exe cache get
lake build
```

## Contributing

Contributions are welcome! Priority areas:

- Filling in `sorry` placeholders
- Adding documentation
- Extending the blueprint
- Creating examples

### Development Workflow

1. Make changes to Lean files
2. Run `lake build` to verify
3. Update blueprint LaTeX if needed
4. Run `~/update-blueprint.sh`
5. Submit pull request

## References

### Primary Source

- [Colding-De Lellis: The min-max construction of minimal surfaces](https://arxiv.org/abs/math/0303305) (2003)

### Classical Works

- Pitts, J.T. (1981). *Existence and regularity of minimal surfaces on Riemannian manifolds*
- Simon, L. (1987). *Lectures on geometric measure theory*
- Almgren, F. (1965). The theory of varifolds

### Modern Developments

- Marques, F. & Neves, A. (2014). Min-max theory and the Willmore conjecture
- De Lellis, C. & Pellandini, F. (2010). Genus bounds for minimal surfaces

## Project Statistics

- **Definitions formalized**: 12
- **Theorems stated**: 3
- **Proofs completed**: 0 (framework ready)
- **Lines of Lean code**: ~500
- **Blueprint pages**: 8

## License

Apache 2.0 License - see LICENSE file for details.

## Contact

- GitHub Issues: [Project Issues](https://github.com/Xinze-Li-Bryan/The-Min-Max-Construction-of-Minimal-Surfaces-in-Lean4/issues)
- Author: Xinze Li
