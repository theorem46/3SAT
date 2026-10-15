#!/usr/bin/env python3
"""APPENDIX D -- THE RESOLUTION, INSTANCE 1 (n = 10, m = 43).

Validates Theorem 4 of
  "Relational Lysis and Computational Efficiency II".

Deterministic.  No third-party dependencies.  Exits non-zero on any failure.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _resolve_common import run
sys.exit(run("instance1.json", "D", "Instance 1"))
