# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a LaTeX academic paper repository documenting the formalization of Symbolic Finite Transducers (SFTs) in Isabelle/HOL. The paper titled "Certified Symbolic Finite Transducers: Formalization and Applications to String Manipulation" presents the first formalization of SFTs and their application to string constraint solving.

## Document Structure

- `main.tex` - Main paper document using the LIPIcs conference style
- `literature.bib` - Bibliography file containing all paper references  
- `lipics-v2021.cls` - LIPIcs LaTeX document class
- `sigplanconf.cls` - SIGPLAN conference style class (alternative format)

## Building the Paper

### Primary Build Command
```bash
latexmk -pdf main.tex
```

This command automatically handles:
- Multiple LaTeX compilation passes
- Bibliography generation with BibTeX
- Reference resolution
- Index generation if needed

### Alternative Build Commands
```bash
# Manual compilation (requires multiple runs)
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex

# Quick compilation (no bibliography updates)
pdflatex main.tex
```

### Clean Build Files
```bash
latexmk -c main.tex    # Clean auxiliary files
latexmk -C main.tex    # Clean all generated files including PDF
```

## Document Classes and Formatting

The paper can be compiled with different document classes:
- **LIPIcs style** (current): Uses `\documentclass[sigplan,10pt,anonymous,review]{acmart}`
- **SIGPLAN style**: Alternative using `sigplanconf.cls`

Key LaTeX packages used:
- `tikz` - For drawing automata diagrams
- `listings` - For code formatting (SMT-LIB syntax highlighting)
- `booktabs` - For professional table formatting
- `stmaryrd` - For mathematical symbols

## Content Organization

The paper follows this structure:
1. **Introduction** - Motivation and contributions
2. **Formalization of SFTs** - Mathematical definitions and Isabelle/HOL implementation
3. **Product Operation** - Core algorithmic contribution  
4. **Algorithm Level Refinement** - Implementation details with interval algebra
5. **String Solving Application** - Practical demonstration with replacement operations
6. **Related Work** - Comparison with existing approaches
7. **Conclusion** - Summary and future directions

## Key Technical Content

- **Symbolic Finite Transducers**: Extension of finite automata supporting infinite alphabets
- **Three-layered formalization**: Abstract → Locale → Implementation layers
- **Interval algebra**: Efficient Boolean algebra implementation  
- **Product operation**: Core algorithm for SFT × SFA composition
- **String replacement**: Application to SMT-LIB constraint solving

## Bibliography Management

References are managed in `literature.bib` using standard BibTeX format. The paper uses `plainurl` bibliography style for consistent URL formatting.

## VS Code Configuration

The repository includes VS Code settings (`.vscode/settings.json`) with:
- LaTeX-specific formatting disabled on save
- Word wrap configured for academic writing (70 columns)
- Proper indentation for wrapped lines