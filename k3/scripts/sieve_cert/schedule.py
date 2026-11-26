"""
Declarative contiguous slab and asymptotic ray parameter schedule covering all
even integers `N >= 4 * 10^18` up to `+∞`.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Slab2ASpec:
    x_lo: int
    x_hi: int
    z: int
    a: int
    m_odd: int


@dataclass(frozen=True)
class Slab2BSpec:
    x_lo: int
    x_hi: int
    m_div: int
    a: int
    m_odd: int


@dataclass(frozen=True)
class Slab2CSpec:
    x_lo: int
    x_hi: int
    m_div: int


@dataclass(frozen=True)
class AsymptoticRaySpec:
    exp10: int
    m_div: int
    k_target: int = 100
    rec_mode: str = "old"
    b_a_str: str = "2.5"
    b_q_str: str = "5.5"
    l_strips: int = 120
    c2_lean_cap: int | None = None


SLABS_2A: list[Slab2ASpec] = [
    Slab2ASpec(4 * 10**18, 45 * 10**17, 19, 1, 5),
    Slab2ASpec(45 * 10**17, 5 * 10**18, 19, 1, 5),
    Slab2ASpec(5 * 10**18, 7 * 10**18, 23, 0, 7),
    Slab2ASpec(7 * 10**18, 10**19, 23, 0, 7),
    Slab2ASpec(10**19, 15 * 10**18, 23, 0, 7),
    Slab2ASpec(15 * 10**18, 2 * 10**19, 23, 0, 7),
    Slab2ASpec(2 * 10**19, 3 * 10**19, 23, 0, 7),
    Slab2ASpec(3 * 10**19, 5 * 10**19, 23, 0, 7),
    Slab2ASpec(5 * 10**19, 8 * 10**19, 23, 0, 7),
    Slab2ASpec(8 * 10**19, 10**20, 23, 0, 7),
    Slab2ASpec(10**20, 2 * 10**20, 23, 0, 7),
    Slab2ASpec(2 * 10**20, 4 * 10**20, 23, 0, 7),
    Slab2ASpec(4 * 10**20, 7 * 10**20, 29, 1, 7),
    Slab2ASpec(7 * 10**20, 10**21, 29, 1, 7),
    Slab2ASpec(10**21, 2 * 10**21, 29, 1, 7),
    Slab2ASpec(2 * 10**21, 5 * 10**21, 29, 1, 7),
    Slab2ASpec(5 * 10**21, 10**22, 23, 0, 7),
    Slab2ASpec(10**22, 2 * 10**22, 31, 0, 7),
    Slab2ASpec(2 * 10**22, 5 * 10**22, 31, 0, 7),
    Slab2ASpec(5 * 10**22, 10**23, 31, 0, 7),
    Slab2ASpec(10**23, 2 * 10**23, 37, 1, 7),
]

SLABS_2B: list[Slab2BSpec] = [
    Slab2BSpec(2 * 10**23, 4 * 10**23, 13, 3, 5),
    Slab2BSpec(4 * 10**23, 10**24, 13, 3, 5),
    Slab2BSpec(10**24, 2 * 10**24, 13, 3, 5),
    Slab2BSpec(2 * 10**24, 3 * 10**24, 13, 3, 5),
    Slab2BSpec(3 * 10**24, 10**25, 12, 2, 5),
    Slab2BSpec(10**25, 3 * 10**25, 13, 3, 5),
    Slab2BSpec(3 * 10**25, 10**26, 13, 3, 5),
    Slab2BSpec(10**26, 3 * 10**26, 13, 3, 5),
    Slab2BSpec(3 * 10**26, 10**27, 13, 3, 5),
    Slab2BSpec(10**27, 3 * 10**27, 13, 4, 5),
    Slab2BSpec(3 * 10**27, 10**28, 13, 4, 5),
    Slab2BSpec(10**28, 3 * 10**28, 13, 4, 5),
    Slab2BSpec(3 * 10**28, 10**29, 13, 4, 5),
    Slab2BSpec(10**29, 3 * 10**29, 13, 4, 5),
    Slab2BSpec(3 * 10**29, 10**30, 14, 5, 5),
    Slab2BSpec(10**30, 10**32, 15, 5, 5),
    Slab2BSpec(10**32, 10**34, 15, 5, 5),
    Slab2BSpec(10**34, 10**36, 15, 5, 5),
    Slab2BSpec(10**36, 10**39, 16, 6, 5),
    Slab2BSpec(10**39, 10**42, 16, 2, 7),
    Slab2BSpec(10**42, 10**45, 17, 3, 7),
    Slab2BSpec(10**45, 10**48, 17, 3, 7),
    Slab2BSpec(10**48, 10**50, 19, 6, 7),
    Slab2BSpec(10**50, 10**52, 19, 6, 7),
    Slab2BSpec(10**52, 10**54, 19, 6, 7),
    Slab2BSpec(10**54, 10**56, 19, 6, 7),
    Slab2BSpec(10**56, 10**58, 19, 7, 7),
    Slab2BSpec(10**58, 10**60, 19, 7, 7),
    Slab2BSpec(10**60, 10**62, 19, 7, 7),
    Slab2BSpec(10**62, 10**64, 19, 7, 7),
    Slab2BSpec(10**64, 10**66, 19, 7, 7),
    Slab2BSpec(10**66, 10**68, 19, 7, 7),
    Slab2BSpec(10**68, 10**70, 19, 8, 7),
    Slab2BSpec(10**70, 10**72, 19, 8, 7),
    Slab2BSpec(10**72, 10**74, 19, 8, 7),
    Slab2BSpec(10**74, 10**76, 19, 8, 7),
    Slab2BSpec(10**76, 10**78, 19, 1, 9),
    Slab2BSpec(10**78, 10**80, 19, 1, 9),
    Slab2BSpec(10**80, 10**82, 19, 9, 7),
    Slab2BSpec(10**82, 10**84, 19, 2, 9),
]

_C_EDGES: list[tuple[int, int, int]] = (
    [(e, e + 2, 18) for e in range(84, 94, 2)]
    + [(e, e + 2, 17) for e in range(94, 120, 2)]
    + [(e, e + 2, 16) for e in range(120, 126, 2)]
    + [
        (126, 128, 15), (128, 131, 15), (131, 134, 15), (134, 137, 15),
        (137, 141, 15), (141, 145, 15), (145, 149, 15), (149, 154, 15),
        (154, 159, 15), (159, 164, 15), (164, 169, 15), (169, 175, 15),
        (175, 181, 15), (181, 187, 15), (187, 194, 15), (194, 201, 15),
        (201, 208, 15), (208, 216, 15), (216, 224, 15), (224, 232, 15),
        (232, 240, 15), (240, 249, 15), (249, 258, 15), (258, 268, 15),
        (268, 278, 15), (278, 289, 15), (289, 300, 15), (300, 312, 15),
        (312, 324, 15), (324, 337, 15), (337, 350, 15), (350, 364, 15),
        (364, 378, 15), (378, 393, 15), (393, 409, 15), (409, 425, 15),
        (425, 442, 15), (442, 460, 15), (460, 478, 15), (478, 497, 15),
        (497, 517, 15), (517, 537, 15), (537, 558, 15), (558, 579, 15),
        (579, 600, 15),
    ]
)

SLABS_2C: list[Slab2CSpec] = [
    Slab2CSpec(10**e0, 10**e1, m_div)
    for (e0, e1, m_div) in _C_EDGES
]

ASYMPTOTIC_SPEC = AsymptoticRaySpec(
    exp10=600, m_div=16, k_target=100, rec_mode="old", c2_lean_cap=495
)
