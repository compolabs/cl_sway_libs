#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct I64 {
    /// The underlying unsigned number representing the `I64` type.
    pub(crate) underlying: u64,
}

pub const INDENT_I64: u64 = 0x8000000000000000;

impl I64 {
    /// The size of this type in bits.
    ///
    /// # Returns
    ///
    /// [u32] - The defined size of the `I64` type.
    ///
    /// # Examples
    ///
    /// ``rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::bits(), 64);
    /// }
    /// ```
    pub fn bits() -> u32 {
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::*;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::max().underlying(), u64::MAX);
    /// }
    /// ```
    pub fn max() -> Self {
        Self {
            underlying: u64::MAX,
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::min().underlying(), 0);
    /// }
    /// ```
    pub fn min() -> Self {
        Self {
            underlying: u64::MIN,
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::*;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::new().underlying(), INDENT_I64);
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::*;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::zero().underlying(), INDENT_I64);
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert!(I64::zero().is_zero());
    /// }
    /// ```
    pub fn is_zero(&self) -> bool {
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::*;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::zero().underlying(), INDENT_I64);
    /// }
    /// ```
    pub fn underlying(&self) -> u64 {
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert!(I64::min().is_negative());
    /// }
    /// ```
    pub fn is_negative(&self) -> bool {
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert!(I64::max().is_positive());
    /// }
    /// ```
    pub fn is_positive(&self) -> bool {
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::*;
    ///
    /// fn foo() {
    ///    assert_eq!(I64::from(1u64).underlying(), INDENT_I64 + 1);
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::*;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::min().abs(), INDENT_I64);
    ///     assert_eq!(I64::max().abs(), INDENT_I64 - 1);
    /// }
    /// ```
    pub fn abs(&self) -> u64 {
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::max().reverse_sign().underlying(), 1);
    /// }
    /// ```
    pub fn reverse_sign(&self) -> I64 {
        Self {
            underlying: u64::MAX - self.underlying + 1,
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
    /// ```rust
    /// use compolabs_sway_libs::signed_integers::i64::I64;
    ///
    /// fn foo() {
    ///     assert_eq!(I64::max().reverse_sign_if(true).underlying(), 1);
    ///     assert_eq!(I64::max().reverse_sign_if(false).underlying(), u64::MAX);
    /// }
    /// ```
    pub fn reverse_sign_if(&self, reverse: bool) -> I64 {
        match reverse {
            true => self.reverse_sign(),
            _ => *self,
        }
    }
}
