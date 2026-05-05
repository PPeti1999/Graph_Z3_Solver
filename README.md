# 🌳 Graph_Z3_Solver: Acyclic Theory Propagator

[cite_start]A high-performance Python integration for the **Z3 SMT Solver** designed to efficiently enforce acyclicity (forest property) in undirected graphs using **Custom Theory Propagation**[cite: 4, 6].

[![Z3 Solver](https://img.shields.io/badge/Powered%20by-Z3%20Solver-blue)](https://github.com/Z3Prover/z3)
[![Python](https://img.shields.io/badge/Language-Python%203.x-green)](https://www.python.org/)

---

## 📖 Project Overview

[cite_start]The core goal of this project is to handle graph logical properties and constraint propagation within an SMT environment[cite: 4, 5]. [cite_start]Instead of pre-generating an exponential number of cycle-forbidding clauses, this module incrementally enforces the "forest" property[cite: 6, 7].

### Key Functionalities
* [cite_start]**Dynamic Cycle Detection**: Real-time monitoring of Z3's decisions with immediate intervention upon cycle formation[cite: 9].
* [cite_start]**Conflict Explanation**: Generates minimal conflict clauses by identifying fundamental cycles, allowing the solver to learn from mistakes (CDCL)[cite: 11, 35].
* [cite_start]**Backtracking Support**: Fully integrated with Z3’s `push/pop` mechanism to ensure state consistency[cite: 10, 21].

---

## 🏗️ System Architecture

[cite_start]The system is built on two tightly coupled components[cite: 16]:

### 1. Union-Find with Backtracking
[cite_start]A specialized data structure that tracks connected components and supports state reversal[cite: 17, 19].
* [cite_start]**Trail-based Logging**: Every modification (e.g., merging components) registers an `undo` function in a trail stack[cite: 23, 71].
* [cite_start]**Closure-based Undo**: Uses Python closures to encapsulate state-reversal logic, hiding internal complexity[cite: 49, 50, 54].
* [cite_start]**Efficiency**: Utilizes "Union by Size" to maintain balanced trees for fast connectivity queries[cite: 62, 80].

### 2. AcyclicPropagator
[cite_start]Derived from Z3's `UserPropagateBase`, this class acts as the middleware between the solver and the graph logic[cite: 25, 84].
* [cite_start]**Event Handling**: Listens for `fixed` callbacks (when an edge is assigned True/False) and `push/pop` events[cite: 29, 120, 122].
* [cite_start]**Conflict Logic**: If a new edge connects two nodes already in the same component, a cycle is detected[cite: 30, 88].
* [cite_start]**Explanation Generation**: Uses BFS to find the path in the current forest that bridges the two nodes, creating a logical proof for the conflict[cite: 39, 149].

---

## ⚙️ Technical Specifications

### Propagation Modes
[cite_start]The propagator supports two strategies via the `eager` flag[cite: 43]:
* [cite_start]**Lazy (Default)**: Reacts only when the solver explicitly creates a cycle[cite: 44, 107].
* [cite_start]**Eager**: Proactively forbids all potential "internal" edges within a component as soon as it is merged, narrowing the search space[cite: 45, 91, 106].

### Core Data Structures
| Component | Description |
| :--- | :--- |
| `self.trail` | [cite_start]A list of undo closures for state restoration[cite: 94, 95]. |
| `self.fixed_edges` | [cite_start]Z3 terms representing the current forest structure[cite: 99, 100]. |
| `self._true_edge_keys` | [cite_start]A cache for $O(1)$ edge existence checks[cite: 101, 102]. |
| `self._propagated_pairs` | [cite_start]Ensures idempotency by avoiding redundant clause generation[cite: 103, 104, 161]. |

---

## 🚀 Quick Start

### Prerequisites
* Python 3.x
* `z3-solver` library

### Installation
```bash
pip install z3-solver