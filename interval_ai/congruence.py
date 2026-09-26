"""整数同余域 x ≡ r (mod m)。

``m = 0`` 表示精确常量集合 ``{r}``；``m = 1`` 表示任意整数。
有限模数总是规范为非负整数，余数规范为 ``0 <= r < m``。
Python 的 ``%`` 对负被除数也返回该非负余数，因此负起点和负常数运算一致。
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from .errors import ValidationError, require_int


@dataclass(frozen=True, slots=True)
class Congruence:
    modulus: int
    residue: int

    def __post_init__(self) -> None:
        require_int(self.modulus, "Congruence.modulus")
        require_int(self.residue, "Congruence.residue")
        if self.modulus < 0:
            raise ValidationError("congruence modulus must be >= 0", "Congruence.modulus")
        if self.modulus == 0:
            object.__setattr__(self, "residue", self.residue)
        else:
            object.__setattr__(self, "residue", self.residue % self.modulus)

    @classmethod
    def exact(cls, value: int) -> "Congruence":
        require_int(value, "Congruence.exact.value")
        return cls(0, value)

    @classmethod
    def arbitrary(cls) -> "Congruence":
        return cls(1, 0)

    @classmethod
    def even(cls) -> "Congruence":
        return cls(2, 0)

    @classmethod
    def odd(cls) -> "Congruence":
        return cls(2, 1)

    @property
    def is_exact(self) -> bool:
        return self.modulus == 0

    @property
    def is_top(self) -> bool:
        return self.modulus == 1

    def contains_int(self, value: int) -> bool:
        require_int(value, "Congruence.contains_int.value")
        return value == self.residue if self.modulus == 0 else value % self.modulus == self.residue

    def subseteq(self, other: "Congruence") -> bool:
        if other.modulus == 0:
            return self.modulus == 0 and self.residue == other.residue
        if self.modulus == 0:
            return self.residue % other.modulus == other.residue
        return self.modulus % other.modulus == 0 and self.residue % other.modulus == other.residue

    def join(self, other: "Congruence") -> "Congruence":
        """最小同余上界：包含两个同余类的最大公共限制。"""
        modulus = gcd(self.modulus, other.modulus, abs(self.residue - other.residue))
        residue = self.residue if modulus == 0 else self.residue % modulus
        return Congruence(modulus, residue)

    def shift(self, k: int) -> "Congruence":
        require_int(k, "Congruence.shift.k")
        if self.modulus == 0:
            return Congruence.exact(self.residue + k)
        return Congruence(self.modulus, self.residue + k)

    def scale(self, k: int) -> "Congruence":
        """仿射常量乘法 x -> k*x；k 可为负整数或 0。"""
        require_int(k, "Congruence.scale.k")
        if self.modulus == 0:
            return Congruence.exact(self.residue * k)
        if k == 0:
            return Congruence.exact(0)
        modulus = gcd(abs(k), self.modulus)
        return Congruence(modulus, self.residue * k)

    def has_point_within(
        self, lower: int | None, upper: int | None
    ) -> bool:
        """判断闭整数区间内是否存在满足同余的点；不做有界枚举。"""
        if lower is not None and upper is not None and lower > upper:
            return False
        if self.modulus == 0:
            value = self.residue
            return (lower is None or value >= lower) and (upper is None or value <= upper)
        if lower is None:
            return True
        first = lower + (self.residue - lower) % self.modulus
        return upper is None or first <= upper

    def normalized_for_interval(self, lower: int | None, upper: int | None) -> "Congruence | None":
        """与区间归约：单元素区间变精确；区间内无合法同余点返回 ``None``。"""
        if lower is not None and upper is not None and lower == upper:
            exact = Congruence.exact(lower)
            return exact if exact.subseteq(self) else None
        return self if self.has_point_within(lower, upper) else None

    @property
    def text(self) -> str:
        if self.modulus == 0:
            return f"x = {self.residue}"
        if self.modulus == 1:
            return "x ∈ Z"
        return f"x ≡ {self.residue} (mod {self.modulus})"

    def to_dict(self) -> dict[str, int]:
        return {"modulus": self.modulus, "residue": self.residue}
