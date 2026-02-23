# Product Guide — Haskell Backend (K Framework Symbolic Execution Engine)

## Overview

The haskell-backend project implements the symbolic execution engine for the [K Framework](https://github.com/runtimeverification/k). It operates on **Kore**, an intermediate representation produced by the K compiler from language specifications. The engine is a symbolic term rewriter exposed via a JSON RPC server implementing the [KORE RPC protocol](./docs/2022-07-18-JSON-RPC-Server-API.md).

This is a low-level infrastructure component, not intended as a user-facing tool. End users interact with the K Framework through higher-level interfaces such as the [pyk](https://github.com/runtimeverification/k/tree/master/pyk) Python package.

## Target Audience

Internal Runtime Verification engineers who maintain, extend, and optimize the symbolic execution backend. Downstream consumers include the `pyk` theorem prover and other tools that communicate via the KORE RPC protocol.

## Core Functionality

- **JSON RPC-based symbolic term rewriter (`kore-rpc-booster`):** The primary entry point. Parses and internalises a Kore definition file, then launches an RPC server that executes rewriting requests against that definition.
- **LLVM backend integration:** Accepts a dynamically-linked library compiled by the LLVM backend for efficient simplification of bool-sorted terms.
- **KORE RPC protocol compliance:** Implements the standardized protocol enabling interoperability with upstream tools like `pyk` and the broader K ecosystem.

## Key Quality Attributes

- **Performance:** Fast symbolic execution capable of handling large K definitions and complex rewriting tasks. Performance benchmarks against downstream projects (KEVM, Kontrol) are part of the development workflow.
- **Correctness:** The rewriter must produce semantically faithful results that match K Framework specifications. Formal verification principles underpin the project's purpose.
- **Maintainability:** Strict Haskell coding standards enforced via `-Wall -Werror`, `fourmolu` formatting, and `hlint` linting. CI validates compliance on every change.

## Project Structure

The repository is a multi-package Haskell monorepo containing four packages:

| Package | Purpose |
|---|---|
| `kore` | Core symbolic execution engine and legacy RPC server (`kore-rpc`) |
| `booster` | Accelerated rewrite engine (`kore-rpc-booster`) |
| `kore-rpc-types` | Shared RPC type definitions |
| `dev-tools` | Developer utilities (e.g., `pretty` for KORE JSON pretty-printing) |
