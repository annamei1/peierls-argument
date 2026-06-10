# CLAUDE.md — Project Instructions for Claude Code

You are an expert in mathematical physics and the rigorous formalization of
statistical mechanics.

## Project Overview

This repository (`peierls-argument`) holds a **structured LaTeX reference
transcription of Chapter 3 ("The Ising Model") of Friedli & Velenik,
*Statistical Mechanics of Lattice Systems: a Concrete Mathematical
Introduction*** (Cambridge University Press, 2017). It reproduces the
chapter's organization, numbered definitions and theorem statements, and
connecting exposition; **proofs are summarized, not transcribed verbatim**,
and equation/result numbering follows the source.



## Repository Layout

Flat, single-document repo — all paths are relative to the repo root:

- `Ising_Model.tex` — the transcription. Section numbering starts at 3
  (`\setcounter{section}{3}`) to mirror the book's Chapter 3. Theorem
  environments (`theorem`, `lemma`, `proposition`, `corollary`, `definition`,
  `exercise`, `remark`) are numbered within sections. Notation macros
  (`\Z`, `\La`, `\sg`, `\Ham`, `\fin`, `\incr`, `\meanp`, `\meanm`, …) live in
  the preamble — reuse them; do not introduce parallel notation.
- `Ising_Model.pdf` — compiled output, kept in the repo and committed
  alongside `.tex` changes so the rendered document stays in sync.
- `README.md` — top-level overview.

This file is the **single source of truth** for project rules.

## Transcription Fidelity Rules

1. Statements (definitions, theorems, lemmas, propositions, corollaries) must
   be **faithful to the book**. Do not "simplify" by changing meaning, weaken
   hypotheses, or silently strengthen conclusions.
2. Numbering follows the source. Do not renumber, reorder, or interleave
   results in a way that breaks correspondence with the book.
3. Proofs are summaries: capture the strategy and key estimates, not a
   verbatim copy. If a proof summary is added or expanded, make clear which
   steps are sketched.
4. If the book justifies only a limited statement, transcribe that limited
   statement. Do not upgrade it.
5. When adding material beyond the book (remarks, cross-references to the
   Lean formalization), mark it clearly as an addition so it cannot be
   mistaken for the source text.
6. When asked to explain a theorem or definition, **read the actual LaTeX
   statement** rather than relying on surrounding exposition — the statement
   is the source of truth within this repo, and the book is the authority
   above it.

## Editing Workflow

**Do not try to write large LaTeX additions all at once.** Iterate:

1. Write a coherent chunk (a subsection, a block of statements).
2. Compile and check the log for errors and warnings (undefined references,
   missing `$`, unbalanced environments).
3. Correct based on the feedback.
4. Repeat until it compiles cleanly.

Before writing new macros or theorem environments, **check the preamble** for
existing ones to reuse. Do not duplicate notation.

## Build & Verification Commands

1. Compile with `pdflatex Ising_Model.tex` (run twice when labels/references
   changed, so cross-references resolve).
2. After any `.tex` edit that will be committed, recompile and include the
   updated `Ising_Model.pdf` in the same commit.
3. Clean up auxiliary files (`.aux`, `.log`, `.out`, `.toc`) — do not commit
   them.

## Relationship to the Lean Formalization


- When a formalization question hinges on the precise wording of a
  definition or theorem, quote this transcription by section/number, and if
  the transcription looks off, verify against the book before relying on it.
- Do not edit Lean files from this repo's sessions; record any discovered
  statement discrepancies here (fix the transcription) and surface them to
  the user.

## Git Hygiene

1. The worktree may contain user or agent changes. Do not revert changes you
   did not make unless the user explicitly asks.
2. Before committing, inspect `git status --short` and stage intentionally.
3. Leave `.claude/` and LaTeX auxiliary files out of commits.
4. Commit or push only when the user asks.
5. Keep `Ising_Model.pdf` in sync with `Ising_Model.tex` in every commit that
   touches the document.

## Environment & Tooling

- `gh` (GitHub CLI) is at `/opt/homebrew/bin/gh` (not on default PATH — use
  full path).
- Use Gemini for mathematical strategy, statement checking, and references
  when helpful. Never run Gemini inside the sandbox; use an out-of-sandbox
  invocation, because the in-sandbox path is unreliable and can hang
  silently.
