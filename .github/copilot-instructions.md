# AI Agent Instructions for Sphere-Packing-Lean

This project formalizes Viazovska's proof of the sphere packing problem in 8 dimensions using the Lean theorem prover. These instructions help AI agents understand the project's key aspects.

## Project Architecture

### Core Components
- `SpherePacking/Basic/`: Core definitions and theorems about sphere packings
  - `SpherePacking.lean`: Fundamental structures (`SpherePacking`, `PeriodicSpherePacking`)
  - `E8.lean`: E8 lattice definitions and properties
  - `PeriodicPacking.lean`: Theory of periodic sphere packings

### Key Mathematical Components
- `SpherePacking/ModularForms/`: Modular forms theory
- `SpherePacking/ForMathlib/`: General mathematical results needed by the project
- `SpherePacking/CohnElkies/`: Implementation of Cohn-Elkies bounds
- `SpherePacking/MagicFunction/`: Viazovska's magic function construction

## Development Workflow

### Build Process
1. Run `lake exe cache get!` to download pre-built dependencies
2. Use `lake build` to compile the project

### Testing
- Tests are organized under `Tactic/Test/`
- Ensure any new definitions have corresponding tests

### Contribution Flow
1. Find unclaimed tasks in the [project dashboard](https://github.com/users/thefundamentaltheor3m/projects/2/views/1)
2. Comment "claim" on chosen issue
3. Create branch from `main`
4. Run `lake exe mk_all` after adding files
5. Submit PR and comment "propose #PR_NUMBER" on issue
6. Add "awaiting-review" label when ready

## Project-Specific Conventions

### Code Organization
- Definitions go in corresponding component directories
- Supporting lemmas should be in same file as main theorems
- Use `ForMathlib/` for general math results

### Proof Style
- Use `sorry` for unfinished proofs
- Structure large proofs into smaller lemmas
- Document key proof steps with comments

### Documentation
- Update blueprint in `blueprint/src/` for significant changes
- Main documentation at `/home_page/`
- Use Zulip for technical discussions

## Integration Points

### Key Dependencies
- Lean's mathlib standard library
- Custom tactics in `Tactic/`
- Blueprint system for documentation generation

### Cross-Component Communication
- `MainTheorem.lean` ties components together
- Modular forms interface with sphere packing via Fourier transforms
- E8 lattice definitions used throughout periodic packing proofs