library;

use std::u128::U128;

/// The 128-bit signed integer type.
///
/// # Additional Information
///
/// Represented as an underlying U128 value.
/// Actual value is abs of underlying value & (2 ^ 127 - 1) with sign `+` if 127-bit is empty or `-` if it's set
/// Max actual value is 2 ^ 127 - 1, min actual value is - 2 ^ 127
pub struct I128 {
    /// The underlying unsigned number representing the `I128` type.
    underlying: U128,
}

const INDENT_I128 = U128::from((0x8000000000000000u64, 0x0000000000000000u64));

impl I128 {
    /// The size of this type in bits.
    ///
    /// # Returns
    ///
    /// [u32] - The defined size of the `I128` type.
    ///
    /// # Examples
    ///
    /// ``sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::bits() == 128);
    /// }
    /// ```
    pub fn bits() -> u32 {
        U128::bits()
    }

    /// The largest value that can be represented by this integer type.
    ///
    /// # Returns
    ///
    /// * [I128] - The newly created `I128` struct.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::max().underlying() == U128::max());
    /// }
    /// ```
    pub fn max() -> Self {
        Self {
            underlying: U128::max(),
        }
    }

    /// The smallest value that can be represented by this integer type.
    ///
    /// # Returns
    ///
    /// * [I128] - The newly created `I128` type.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::min().underlying() == U128::min());
    /// }
    /// ```
    pub fn min() -> Self {
        Self {
            underlying: U128::min(),
        }
    }

    /// Initializes a new, zeroed I128.
    ///
    /// # Additional Information
    ///
    /// The zero value of I128 is 0.
    ///
    /// # Returns
    ///
    /// * [I128] - The newly created `I128` struct.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::new().underlying() == INDENT_I128);
    /// }
    /// ```
    pub fn new() -> Self {
        Self::zero()
    }

    /// The zero value `I128`.
    ///
    /// # Returns
    ///
    /// * [I128] - The newly created `I128` type.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::zero().underlying() == INDENT_I128);
    /// }
    /// ```
    pub fn zero() -> Self {
        Self {
            underlying: INDENT_I128,
        }
    }
    /// Returns whether a `I128` is set to zero.
    ///
    /// # Returns
    ///
    /// * [bool] -> True if the `I128` is zero, otherwise false.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::zero().is_zero());
    /// }
    /// ```
    pub fn is_zero(self) -> bool {
        self.underlying == INDENT_I128
    }

    /// Returns the underlying `u64` representing the `I128`.
    ///
    /// # Returns
    ///
    /// * [u64] - The `u64` representing the `I128`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::zero().underlying() == INDENT_I128);
    /// }
    /// ```
    pub fn underlying(self) -> U128 {
        self.underlying
    }

    /// Check if number is negative of given I128.
    ///
    /// # Returns
    ///
    /// * [bool] - Returns true if number is negative otherwise false.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::min().is_negative());
    /// }
    /// ```
    pub fn is_negative(self) -> bool {
        self.underlying < INDENT_I128
    }

    /// Check if number is positive of given I128.
    ///
    /// # Returns
    ///
    /// * [bool] - Returns true if number is positive otherwise false.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::max().is_positive());
    /// }
    /// ```
    pub fn is_positive(self) -> bool {
        self.underlying > INDENT_I128
    }
}

impl From<U128> for I128 {
    /// Converts a `U128` to a `I128`.
    ///
    /// # Returns
    ///
    /// * [I128] - The `I128` representation of the `U128` value.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::from(U128::from(1u64)).underlying() == INDENT_I128 + 1u64.into());
    /// }
    /// ```
    fn from(val: U128) -> Self {
        Self {
            underlying: INDENT_I128 + val,
        }
    }
}

impl From<u64> for I128 {
    /// Converts a `u64` to a `I128`.
    ///
    /// # Returns
    ///
    /// * [I128] - The `I128` representation of the `u64` value.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::from(1u64).underlying() == INDENT_I128 + 1u64.into());
    /// }
    /// ```
    fn from(val: u64) -> Self {
        Self {
            underlying: INDENT_I128 + val.into(),
        }
    }
}

impl I128 {
    /// The absolute of given I128.
    ///
    /// # Returns
    ///
    /// * [u64] - The absolute value of `u64` type.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::min().abs() == INDENT_I128);
    ///     assert(I128::max().abs() == INDENT_I128 - 1u64.into());
    /// }
    /// ```
    pub fn abs(self) -> U128 {
        match self.is_positive() {
            true => self.underlying - INDENT_I128,
            _ => INDENT_I128 - self.underlying,
        }
    }

    /// Returns the signed reversed `I128` representing the `I128`.
    ///
    /// # Returns
    ///
    /// * [I128] - The signed reversed `I128` representing the `I128`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::max().reverse_sign().underlying() == 1u64.into());
    /// }
    /// ```
    pub fn reverse_sign(self) -> I128 {
        Self {
            underlying: U128::max() - self.underlying + 1u64.into(),
        }
    }

    /// Returns the signed reversed `I128` if condition is true representing the `I128`.
    ///
    /// # Returns
    ///
    /// * [I128] - The signed reversed `I128` representing the `I128`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::max().reverse_sign_if(true).underlying() == 1u64.into());
    ///     assert(I128::max().reverse_sign_if(false) == I128::max());
    /// }
    /// ```
    pub fn reverse_sign_if(self, reverse: bool) -> I128 {
        match reverse {
            true => self.reverse_sign(),
            _ => self,
        }
    }
}

impl core::ops::Eq for I128 {
    /// Check a `I128` equal to a `I128`.
    ///
    /// # Returns
    ///
    /// * [bool] - The `true` if equal otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::from(1u64) == I128::from(1u64));
    ///     assert(!(I128::from(2u64) == I128::from(1u64)));
    /// }
    /// ```
    fn eq(self, other: Self) -> bool {
        self.underlying == other.underlying
    }
}

impl core::ops::Ord for I128 {
    /// Check a `I128` greater than a `I128`.
    ///
    /// # Returns
    ///
    /// * [bool] - The `true` if greater otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::from(2u64) > I128::from(1u64));
    ///     assert((I128::from(1u64) > I128::from(1u64)));
    /// }
    /// ```
    fn gt(self, other: Self) -> bool {
        self.underlying > other.underlying
    }

    /// Check a `I128` less than a `I128`.
    ///
    /// # Returns
    ///
    /// * [bool] - The `true` if less otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert(I128::from(1u64) < I128::from(2u64));
    ///     assert(!(I128::from(1u64) < I128::from(1u64)));
    /// }
    /// ```
    fn lt(self, other: Self) -> bool {
        self.underlying < other.underlying
    }
}

impl core::ops::OrdEq for I128 {}

impl core::ops::Add for I128 {
    /// Summarize two signed `I128`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I128] - The result of summary result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert((I128::from(1u64) + I128::from(2u64)).underlying() == INDENT_I128 + 3u64.into());
    /// }
    /// ```
    fn add(self, other: Self) -> Self {
        let (op_l, op_r) = match self > other {
            true => (self, other),
            _ => (other, self),
        };
        Self {
            underlying: match op_l.underlying >= INDENT_I128 {
                true => op_l.underlying - INDENT_I128 + op_r.underlying,
                _ => op_l.underlying + op_r.underlying - INDENT_I128,
            },
        }
    }
}

impl core::ops::Subtract for I128 {
    /// Substruct two signed `I128`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I128] - The result of substruction result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert((I128::from(2u64) - I128::from(1u64)).underlying() == INDENT_I128 + 1u64.into());
    ///     assert((I128::from(1u64) - I128::from(2u64)).underlying() == INDENT_I128 - 1u64.into());
    /// }
    /// }
    /// ```
    fn subtract(self, other: Self) -> Self {
        self.add(other.reverse_sign())
    }
}

impl core::ops::Multiply for I128 {
    /// Multiply two signed `I128`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I128] - The result of multiplication result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert((I128::from(3u64) * I128::from(2u64)).underlying() == INDENT_I128 + 6u64.into());
    /// }
    /// }
    /// ```
    fn multiply(self, other: Self) -> Self {
        I128::from(self.abs() * other.abs()).reverse_sign_if(self.is_positive() != other.is_positive())
    }
}

impl core::ops::Divide for I128 {
    /// Divide two signed `I128`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I128] - The result of multiplication result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::I128::I128;
    ///
    /// fn foo() {
    ///     assert((I128::from(6u64) / I128::from(2u64)).underlying() == INDENT_I128 + 3u64.into());
    /// }
    /// }
    /// ```
    fn divide(self, other: Self) -> Self {
        I128::from(self.abs() / other.abs()).reverse_sign_if(self.is_positive() != other.is_positive())
    }
}

#[test()]
fn test_i128_bits() {
    assert(I128::bits() == 128);
}

#[test()]
fn test_i128_max() {
    assert(I128::max().underlying() == U128::max());
}

#[test()]
fn test_i128_min() {
    assert(I128::min().underlying() == U128::min());
}

#[test()]
fn test_i128_new() {
    assert(I128::new().underlying() == INDENT_I128);
}

#[test()]
fn test_i128_zero() {
    assert(I128::zero().underlying() == INDENT_I128);
}

#[test()]
fn test_i128_is_zero() {
    assert(I128::zero().is_zero());
}

#[test()]
fn test_i128_is_negative() {
    assert(I128::min().is_negative());
}

#[test()]
fn test_i128_is_positive() {
    assert(I128::max().is_positive());
}

#[test()]
fn test_i128_from_u128() {
    assert(I128::from(U128::from(1u64)).underlying() == INDENT_I128 + 1u64.into());
}

#[test()]
fn test_i128_from_u64() {
    assert(I128::from(1u64).underlying() == INDENT_I128 + 1u64.into());
}

#[test()]
fn test_i128_abs() {
    assert(I128::min().abs() == INDENT_I128);
    assert(I128::max().abs() == INDENT_I128 - 1u64.into());
}

#[test()]
fn test_i128_reverse_sign() {
    assert(I128::max().reverse_sign().underlying() == 1u64.into());
}

#[test()]
fn test_i128_reverse_sign_if() {
    assert(I128::max().reverse_sign_if(true).underlying() == 1u64.into());
    assert(I128::max().reverse_sign_if(false) == I128::max());
}

#[test()]
fn test_i128_eq() {
    assert(I128::from(1u64) == I128::from(1u64));
    assert(!(I128::from(2u64) == I128::from(1u64)));
}

#[test()]
fn test_i128_ne() {
    assert(I128::from(2u64) != I128::from(1u64));
    assert(!(I128::from(1u64) != I128::from(1u64)));
}

#[test()]
fn test_i128_gt() {
    assert(I128::from(2u64) > I128::from(1u64));
    assert(!(I128::from(1u64) > I128::from(1u64)));
}

#[test()]
fn test_i128_lt() {
    assert(I128::from(1u64) < I128::from(2u64));
    assert(!(I128::from(1u64) < I128::from(1u64)));
}

#[test()]
fn test_i128_ge() {
    assert(I128::from(2u64) > I128::from(1u64));
    assert(I128::from(1u64) >= I128::from(1u64));
}

#[test()]
fn test_i128_le() {
    assert(I128::from(1u64) < I128::from(2u64));
    assert(I128::from(1u64) <= I128::from(1u64));
}

#[test()]
fn test_i128_add() {
    assert((I128::from(1u64) + I128::from(2u64)).underlying() == INDENT_I128 + 3u64.into());
    assert(
        (I128::from(1u64)
                .reverse_sign() + I128::from(2u64))
            .underlying() == INDENT_I128 + 1u64
            .into(),
    );
    assert(
        (I128::from(1u64)
                .reverse_sign() + I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 - 3u64
            .into(),
    );
    assert(
        (I128::from(1u64) + I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 - 1u64
            .into(),
    );
}

#[test()]
fn test_i128_sub() {
    assert((I128::from(2u64) - I128::from(1u64)).underlying() == INDENT_I128 + 1u64.into());
    assert((I128::from(1u64) - I128::from(2u64)).underlying() == INDENT_I128 - 1u64.into());
    assert(
        (I128::from(1u64)
                .reverse_sign() - I128::from(2u64))
            .underlying() == INDENT_I128 - 3u64
            .into(),
    );
    assert(
        (I128::from(1u64)
                .reverse_sign() - I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 + 1u64
            .into(),
    );
    assert(
        (I128::from(1u64) - I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 + 3u64
            .into(),
    );
}

#[test()]
fn test_i128_mul() {
    assert((I128::from(3u64) * I128::from(2u64)).underlying() == INDENT_I128 + 6u64.into());
    assert(
        (I128::from(3u64)
                .reverse_sign() * I128::from(2u64))
            .underlying() == INDENT_I128 - 6u64
            .into(),
    );
    assert(
        (I128::from(3u64)
                .reverse_sign() * I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 + 6u64
            .into(),
    );
    assert(
        (I128::from(3u64) * I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 - 6u64
            .into(),
    );
}

#[test()]
fn test_i128_div() {
    assert((I128::from(6u64) / I128::from(2u64)).underlying() == INDENT_I128 + 3u64.into());
    assert(
        (I128::from(6u64)
                .reverse_sign() / I128::from(2u64))
            .underlying() == INDENT_I128 - 3u64
            .into(),
    );
    assert(
        (I128::from(6u64)
                .reverse_sign() / I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 + 3u64
            .into(),
    );
    assert(
        (I128::from(6u64) / I128::from(2u64)
                .reverse_sign())
            .underlying() == INDENT_I128 - 3u64
            .into(),
    );
}
