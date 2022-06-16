//! General utilities of UTxO
//!
//! This package provides tools to ease the development of Cryptocurrencies based on UTxO model.
//!

use std::cmp::Ordering;

/// The Select trait offers an interface of UTxO selection.
///
pub trait Select: Sized {
    /// Create zero value of the UTxO type.
    fn zero() -> Self;

    /// Add two values, return `None` if any value overflows.
    fn checked_add(&self, rhs: &Self) -> Option<Self>;

    /// Subtract value on right side, return `None` if any value on the left is smaller
    /// than the value on the right.
    fn checked_sub(&self, rhs: &Self) -> Option<Self>;

    /// Subtract value on right side, return zero if any value on the left is smaller
    /// than the value on the right.
    fn clamped_sub(&self, rhs: &Self) -> Self;

    /// Return true if it is enough to pay the value on right side, otherwise return false.
    fn is_enough(&self, rhs: &Self) -> bool;

    /// Compare two UTxOs to see which is better for the output, the less the better.
    /// A good strategy of UTxO selection should:
    ///
    /// * spend as fewer UTxOs as possible;
    /// * spend as fewer native assets as possible;
    /// * produce as fewer [Dust] as possible;
    ///
    /// [Dust]: https://www.investopedia.com/terms/b/bitcoin-dust.asp
    fn compare(&self, other: &Self, output: &Self) -> Ordering;
}

/// Select UTxOs.
///
/// # Arguments
///
/// * `inputs` - The available UTxOs to be selected from
/// * `output` - The total output required
/// * `threshold` - The minimum the total inputs exceed the total outputs, reserved to pay fees and avoid Dust
///
/// Returns `Some((selected, unselected, excess))` on success,
/// otherwise returns `None` (no enough inputs).
/// The `excess` can be used to pay the fee and return the change.
/// The `unselected` UTxOs can be selected later if more are needed.
pub fn select<'a, T: Select + Clone>(
    inputs: &'a mut [T],
    output: &T,
    threshold: &T,
) -> Option<(&'a mut [T], &'a mut [T], T)> {
    let mut total_selected = T::zero();
    let mut index = 0;
    let mut goal = output.clone();
    let extra_output = output.checked_add(threshold)?;

    while !total_selected.is_enough(&extra_output) {
        inputs.get(index)?;
        let (_, input, _) = inputs[index..].select_nth_unstable_by(0, |x, y| x.compare(y, &goal));
        total_selected = total_selected.checked_add(input)?;
        goal = goal.clamped_sub(&input);
        index += 1;
    }

    let excess = total_selected.checked_sub(output)?;
    let (selected, unselected) = inputs.split_at_mut(index);
    Some((selected, unselected, excess))
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use crate::{select, Select};

    #[derive(Clone, Debug, PartialEq, PartialOrd)]
    struct Value(u8);

    impl Select for Value {
        fn zero() -> Self {
            Self(0)
        }

        fn checked_add(&self, rhs: &Self) -> Option<Self> {
            Some(Self(self.0.checked_add(rhs.0)?))
        }

        fn checked_sub(&self, rhs: &Self) -> Option<Self> {
            Some(Self(self.0.checked_sub(rhs.0)?))
        }

        fn clamped_sub(&self, rhs: &Self) -> Self {
            self.checked_sub(rhs).unwrap_or(Self(0))
        }

        fn is_enough(&self, rhs: &Self) -> bool {
            self >= rhs
        }

        fn compare(&self, other: &Self, output: &Self) -> Ordering {
            let left = self.0.abs_diff(output.0);
            let right = other.0.abs_diff(output.0);
            left.cmp(&right)
        }
    }

    #[test]
    fn test_dummy_value() {
        assert_eq!(
            Value(7).compare(&Value(8), &Value(9)),
            Ordering::Greater
        )
    }

    #[test]
    fn test_select_ok() {
        let mut inputs = [Value(5), Value(7), Value(4), Value(3), Value(8)];
        let total_output = Value(13);

        assert_eq!(
            select(&mut inputs, &total_output, &Value::zero()),
            Some((
                [Value(8), Value(5)].as_mut_slice(),
                [Value(4), Value(3), Value(7)].as_mut_slice(),
                Value(0)
            ))
        );
    }

    #[test]
    fn test_select_failed() {
        let mut inputs = [Value(5), Value(7)];
        let total_output = Value(13);

        assert_eq!(select(&mut inputs, &total_output, &Value::zero()), None);
    }
}
