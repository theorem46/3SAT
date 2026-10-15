#!/usr/bin/env python3
"""APPENDIX E -- THE RESOLUTION, INSTANCE 2 (n = 12, m = 51).

Validates Theorem 4 of
  "Relational Lysis and Computational Efficiency II".

Independent instance, independent planted solution, independent seed.
Deterministic.  No third-party dependencies.  Exits non-zero on any failure.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _resolve_common import run
sys.exit(run("instance2.json", "E", "Instance 2"))
