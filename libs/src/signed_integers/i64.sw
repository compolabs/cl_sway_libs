library;

use std::u128::U128;

/// The 64-bit signed integer type.
///
/// # Additional Information
///
/// Represented as an underlying u64 value.
/// Actual value is abs of underlying value & (2 ^ 63 - 1) with sign `+` if 63-bit is empty or `-` if it's set
/// Max actual value is 2 ^ 63 - 1, min actual value is - 2 ^ 63
pub struct I64 {
    /// The underlying unsigned number representing the `I64` type.
    underlying: u64,
}

const INDENT_I64 = 0x8000000000000000u64;

impl I64 {
    /// The size of this type in bits.
    ///
    /// # Returns
    ///
    /// [u64] - The defined size of the `I64` type.
    ///
    /// # Examples
    ///
    /// ``sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::bits() == 64);
    /// }
    /// ```
    pub fn bits() -> u64 {
        64
    }

    /// The largest value that can be represented by this integer type.
    ///
    /// # Returns
    ///
    /// * [I64] - The newly created `I64` struct.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::max().underlying() == u64::max());
    /// }
    /// ```
    pub fn max() -> Self {
        Self {
            underlying: u64::max(),
        }
    }

    /// The smallest value that can be represented by this integer type.
    ///
    /// # Returns
    ///
    /// * [I64] - The newly created `I64` type.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::min().underlying() == u64::min());
    /// }
    /// ```
    pub fn min() -> Self {
        Self {
            underlying: u64::min(),
        }
    }

    /// Initializes a new, zeroed I64.
    ///
    /// # Additional Information
    ///
    /// The zero value of I64 is 0.
    ///
    /// # Returns
    ///
    /// * [I64] - The newly created `I64` struct.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::new().underlying() == INDENT_I64);
    /// }
    /// ```
    pub fn new() -> Self {
        Self::zero()
    }

    /// The zero value `I64`.
    ///
    /// # Returns
    ///
    /// * [I64] - The newly created `I64` type.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::zero().underlying() == INDENT_I64);
    /// }
    /// ```
    pub fn zero() -> Self {
        Self {
            underlying: INDENT_I64,
        }
    }
    /// Returns whether a `I64` is set to zero.
    ///
    /// # Returns
    ///
    /// * [bool] -> True if the `I64` is zero, otherwise false.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::zero().is_zero());
    /// }
    /// ```
    pub fn is_zero(self) -> bool {
        self.underlying == INDENT_I64
    }

    /// Returns the underlying `u64` representing the `I64`.
    ///
    /// # Returns
    ///
    /// * [u64] - The `u64` representing the `I64`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::zero().underlying() == INDENT_I64);
    /// }
    /// ```
    pub fn underlying(self) -> u64 {
        self.underlying
    }

    /// Check if number is negative of given i64.
    ///
    /// # Returns
    ///
    /// * [bool] - Returns true if number is negative otherwise false.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::min().is_negative());
    /// }
    /// ```
    pub fn is_negative(self) -> bool {
        self.underlying < INDENT_I64
    }

    /// Check if number is positive of given i64.
    ///
    /// # Returns
    ///
    /// * [bool] - Returns true if number is positive otherwise false.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::max().is_positive());
    /// }
    /// ```
    pub fn is_positive(self) -> bool {
        self.underlying > INDENT_I64
    }
}

impl From<u64> for I64 {
    /// Converts a `u64` to a `I64`.
    ///
    /// # Returns
    ///
    /// * [I64] - The `I64` representation of the `u64` value.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::from(1u64).underlying() == 0x8000000000000001);
    /// }
    /// ```
    fn from(val: u64) -> Self {
        Self {
            underlying: INDENT_I64 + val,
        }
    }
}

impl I64 {
    /// The absolute of given i64.
    ///
    /// # Returns
    ///
    /// * [u64] - The absolute value of `u64` type.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::min().abs() == 0x8000000000000000);
    ///     assert(I64::max().abs() == 0x7FFFFFFFFFFFFFFF);
    /// }
    /// ```
    pub fn abs(self) -> u64 {
        match self.is_positive() {
            true => self.underlying - INDENT_I64,
            _ => INDENT_I64 - self.underlying,
        }
    }

    /// Returns the signed reversed `I64` representing the `I64`.
    ///
    /// # Returns
    ///
    /// * [I64] - The signed reversed `I64` representing the `I64`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::max().reverse_sign().underlying() == 1);
    /// }
    /// ```
    pub fn reverse_sign(self) -> I64 {
        Self {
            underlying: u64::max() - self.underlying + 1,
        }
    }

    /// Returns the signed reversed `I64` if condition is true representing the `I64`.
    ///
    /// # Returns
    ///
    /// * [I64] - The signed reversed `I64` representing the `I64`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::max().reverse_sign_if(true).underlying() == 1);
    ///     assert(I64::max().reverse_sign_if(false).underlying() == I64::max());
    /// }
    /// ```
    pub fn reverse_sign_if(self, reverse: bool) -> I64 {
        match reverse {
            true => self.reverse_sign(),
            _ => self,
        }
    }

    /// Returns `I64` of muliplicaion and division using 128-bit math.
    ///
    /// # Returns
    ///
    /// * [I64] - The result of mul and div.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::from(6).mul_div(I64::from(3), I64::from(2)) == I64::from(9));
    /// }
    /// ```
    pub fn mul_div(self, mul: Self, div: Self) -> I64 {
        let res = U128::from((0, self.abs())) * U128::from((0, mul.abs()));
        let res = (res / U128::from((0, div.abs()))).as_u64().unwrap();
        let sign = (self.is_positive() == mul.is_positive()) == div.is_positive();
        I64::from(res).reverse_sign_if(!sign)
    }
}

impl core::ops::Eq for I64 {
    /// Check a `I64` equal to a `I64`.
    ///
    /// # Returns
    ///
    /// * [bool] - The `true` if equal otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::from(1u64) == I64::from(1u64));
    /// }
    /// ```
    fn eq(self, other: Self) -> bool {
        self.underlying == other.underlying
    }
}

impl core::ops::Ord for I64 {
    /// Check a `I64` greater than a `I64`.
    ///
    /// # Returns
    ///
    /// * [bool] - The `true` if greater otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::from(2u64) > I64::from(1u64));
    /// }
    /// ```
    fn gt(self, other: Self) -> bool {
        self.underlying > other.underlying
    }

    /// Check a `I64` less than a `I64`.
    ///
    /// # Returns
    ///
    /// * [bool] - The `true` if less otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert(I64::from(1u64) < I64::from(2u64));
    /// }
    /// ```
    fn lt(self, other: Self) -> bool {
        self.underlying < other.underlying
    }
}

impl core::ops::OrdEq for I64 {}

impl core::ops::Add for I64 {
    /// Summarize two signed `I64`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I64] - The result of summary result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert((I64::from(1u64) + I64::from(2u64)).underlying() == 0x8000000000000003);
    /// }
    /// ```
    fn add(self, other: Self) -> Self {
        let (op_l, op_r) = match self > other {
            true => (self, other),
            _ => (other, self),
        };
        Self {
            underlying: match op_l.underlying >= INDENT_I64 {
                true => op_l.underlying - INDENT_I64 + op_r.underlying,
                _ => op_l.underlying + op_r.underlying - INDENT_I64,
            },
        }
    }
}

impl core::ops::Subtract for I64 {
    /// Substruct two signed `I64`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I64] - The result of substruction result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert((I64::from(1u64) - I64::from(2u64)).underlying() == 0x7FFFFFFFFFFFFFFF);
    /// }
    /// }
    /// ```
    fn subtract(self, other: Self) -> Self {
        self.add(other.reverse_sign())
    }
}

impl core::ops::Multiply for I64 {
    /// Multiply two signed `I64`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I64] - The result of multiplication result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert((I64::from(3u64) * I64::from(2u64)).underlying() == 0x8000000000000006);
    /// }
    /// }
    /// ```
    fn multiply(self, other: Self) -> Self {
        I64::from(self.abs() * other.abs()).reverse_sign_if(self.is_positive() != other.is_positive())
    }
}

impl core::ops::Divide for I64 {
    /// Divide two signed `I64`. Panics on overflow.
    ///
    /// # Returns
    ///
    /// * [I64] - The result of multiplication result.
    ///
    /// # Examples
    ///
    /// ```sway
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert((I64::from(6u64) / I64::from(2u64)).underlying() == 0x8000000000000003);
    /// }
    /// }
    /// ```
    fn divide(self, other: Self) -> Self {
        I64::from(self.abs() / other.abs()).reverse_sign_if(self.is_positive() != other.is_positive())
    }
}

#[test()]
fn test_i64_bits() {
    assert(I64::bits() == 64);
}

#[test()]
fn test_i64_max() {
    assert(I64::max().underlying() == u64::max());
}

#[test()]
fn test_i64_min() {
    assert(I64::min().underlying() == u64::min());
}

#[test()]
fn test_i64_new() {
    assert(I64::new().underlying() == INDENT_I64);
}

#[test()]
fn test_i64_zero() {
    assert(I64::zero().underlying() == INDENT_I64);
}

#[test()]
fn test_i64_is_zero() {
    assert(I64::zero().is_zero());
}

#[test()]
fn test_i64_is_negative() {
    assert(I64::min().is_negative());
}

#[test()]
fn test_i64_is_positive() {
    assert(I64::max().is_positive());
}

#[test()]
fn test_i64_abs() {
    assert(I64::min().abs() == 0x8000000000000000);
    assert(I64::max().abs() == 0x7FFFFFFFFFFFFFFF);
}

#[test()]
fn test_i64_reverse_sign() {
    assert(I64::max().reverse_sign().underlying() == 1);
}

#[test()]
fn test_i64_reverse_sign_if() {
    assert(I64::max().reverse_sign_if(true).underlying() == 1);
    assert(I64::max().reverse_sign_if(false) == I64::max());
}

#[test()]
fn test_i64_from() {
    assert(I64::from(1u64).underlying() == 0x8000000000000001);
}

#[test()]
fn test_i64_eq() {
    assert(I64::from(1u64) == I64::from(1u64));
    assert((I64::from(2u64) == I64::from(1u64)) == false);
}

#[test()]
fn test_i64_ne() {
    assert(I64::from(2u64) != I64::from(1u64));
    assert((I64::from(1u64) != I64::from(1u64)) == false);
}

#[test()]
fn test_i64_gt() {
    assert(I64::from(2u64) > I64::from(1u64));
    assert((I64::from(1u64) > I64::from(1u64)) == false);
}

#[test()]
fn test_i64_lt() {
    assert(I64::from(1u64) < I64::from(2u64));
    assert((I64::from(1u64) < I64::from(1u64)) == false);
}

#[test()]
fn test_i64_ge() {
    assert(I64::from(2u64) > I64::from(1u64));
    assert(I64::from(1u64) >= I64::from(1u64));
}

#[test()]
fn test_i64_le() {
    assert(I64::from(1u64) < I64::from(2u64));
    assert(I64::from(1u64) <= I64::from(1u64));
}

#[test()]
fn test_i64_add() {
    assert((I64::from(1u64) + I64::from(2u64)).underlying() == 0x8000000000000003);
    assert(
        (I64::from(1u64)
                .reverse_sign() + I64::from(2u64))
            .underlying() == 0x8000000000000001,
    );
    assert(
        (I64::from(1u64)
                .reverse_sign() + I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x7FFFFFFFFFFFFFFD,
    );
    assert(
        (I64::from(1u64) + I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x7FFFFFFFFFFFFFFF,
    );
}

#[test()]
fn test_i64_sub() {
    assert((I64::from(2u64) - I64::from(1u64)).underlying() == 0x8000000000000001);
    assert((I64::from(1u64) - I64::from(2u64)).underlying() == 0x7FFFFFFFFFFFFFFF);
    assert(
        (I64::from(1u64)
                .reverse_sign() - I64::from(2u64))
            .underlying() == 0x7FFFFFFFFFFFFFFD,
    );
    assert(
        (I64::from(1u64)
                .reverse_sign() - I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x8000000000000001,
    );
    assert(
        (I64::from(1u64) - I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x8000000000000003,
    );
}

#[test()]
fn test_i64_mul() {
    assert((I64::from(3u64) * I64::from(2u64)).underlying() == 0x8000000000000006);
    assert(
        (I64::from(3u64)
                .reverse_sign() * I64::from(2u64))
            .underlying() == 0x7FFFFFFFFFFFFFFA,
    );
    assert(
        (I64::from(3u64)
                .reverse_sign() * I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x8000000000000006,
    );
    assert(
        (I64::from(3u64) * I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x7FFFFFFFFFFFFFFA,
    );
}

#[test()]
fn test_i64_div() {
    assert((I64::from(6u64) / I64::from(2u64)).underlying() == 0x8000000000000003);
    assert(
        (I64::from(6u64)
                .reverse_sign() / I64::from(2u64))
            .underlying() == 0x7FFFFFFFFFFFFFFD,
    );
    assert(
        (I64::from(6u64)
                .reverse_sign() / I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x8000000000000003,
    );
    assert(
        (I64::from(6u64) / I64::from(2u64)
                .reverse_sign())
            .underlying() == 0x7FFFFFFFFFFFFFFD,
    );
}

#[test()]
fn test_i64_mul_div() {
    assert(I64::from(6).mul_div(I64::from(3), I64::from(2)) == I64::from(9));
    assert(
        I64::from(6)
            .reverse_sign()
            .mul_div(I64::from(3), I64::from(2)) == I64::from(9)
            .reverse_sign(),
    );
    assert(
        I64::from(6)
            .mul_div(I64::from(3).reverse_sign(), I64::from(2)) == I64::from(9)
            .reverse_sign(),
    );
    assert(
        I64::from(6)
            .mul_div(I64::from(3), I64::from(2).reverse_sign()) == I64::from(9)
            .reverse_sign(),
    );
    assert(
        I64::from(6)
            .mul_div(I64::from(3).reverse_sign(), I64::from(2).reverse_sign()) == I64::from(9),
    );
    assert(
        I64::from(6)
            .reverse_sign()
            .mul_div(I64::from(3), I64::from(2).reverse_sign()) == I64::from(9),
    );
}
