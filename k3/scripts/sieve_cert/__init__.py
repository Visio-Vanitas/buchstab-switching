"""Modular zero-float certification package for shifted `Ω(m) ≤ 3` switching."""

from .regime_asymptotic import RayCertificate, certify_asymptotic_ray
from .regime_slabs import SlabCertificate, certify_slab_2a, certify_slab_2b, certify_slab_2c
from .schedule import ASYMPTOTIC_SPEC, SLABS_2A, SLABS_2B, SLABS_2C, AsymptoticRaySpec

__all__ = [
    "ASYMPTOTIC_SPEC",
    "AsymptoticRaySpec",
    "RayCertificate",
    "SLABS_2A",
    "SLABS_2B",
    "SLABS_2C",
    "SlabCertificate",
    "certify_asymptotic_ray",
    "certify_slab_2a",
    "certify_slab_2b",
    "certify_slab_2c",
]
