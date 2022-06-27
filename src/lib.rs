//! General utilities of UTxO
//!
//! This package provides tools to ease the development of Cryptocurrencies based on UTxO model.
//!

use std::{cmp::Ordering, collections::BTreeMap};

/// The Select trait offers an interface of UTxO selection.
///
pub trait Select: Sized {
    /// Creates zero value of the UTxO type.
    fn zero() -> Self;

    /// Computes `self + rhs`, returning `None` if overflow occurred.
    fn checked_add(&self, rhs: &Self) -> Option<Self>;

    /// Computes `self - rhs`, returning `None` if overflow occurred.
    fn checked_sub(&self, rhs: &Self) -> Option<Self>;

    /// Computes `self - rhs`, saturating at the lowest bound if overflow occurred.
    fn saturating_sub(&self, rhs: &Self) -> Self;

    /// Compares two UTxOs to see which is better for the output, the less the better.
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
    let extra_output = output.checked_add(threshold)?;
    let mut goal = extra_output.clone();
    let mut excess = None;

    while excess.is_none() {
        inputs.get(index)?;
        let (_, input, _) = inputs[index..].select_nth_unstable_by(0, |x, y| x.compare(y, &goal));
        total_selected = total_selected.checked_add(input)?;
        goal = goal.saturating_sub(&input);
        index += 1;
        excess = total_selected.checked_sub(&extra_output);
    }

    let (selected, unselected) = inputs.split_at_mut(index);
    let excess = excess?.checked_add(threshold)?;

    Some((selected, unselected, excess))
}

/// Output without native assets (e.g. Bitcoin)
///
/// The algorithm of selection always chooses the largest output.
/// It is expected to use fewer outputs.
#[derive(Clone, Debug, PartialEq)]
pub struct Output<I> {
    pub id: Option<I>,
    pub value: u64,
}

impl<I> Select for Output<I> {
    fn zero() -> Self {
        Self {
            id: None,
            value: u64::MIN,
        }
    }

    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        Some(Self {
            id: None,
            value: self.value.checked_add(rhs.value)?,
        })
    }

    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        Some(Self {
            id: None,
            value: self.value.checked_sub(rhs.value)?,
        })
    }

    fn saturating_sub(&self, rhs: &Self) -> Self {
        Self {
            id: None,
            value: self.value.saturating_sub(rhs.value),
        }
    }

    fn compare(&self, other: &Self, _: &Self) -> Ordering {
        other.value.cmp(&self.value)
    }
}

/// Output with native assets (e.g. Cardano, Ergo)
#[derive(Clone, Debug, PartialEq)]
pub struct ExtOutput<I, K> {
    pub id: Option<I>,
    pub value: u64,
    pub assets: BTreeMap<K, u64>,
}

impl<I, K: Clone + Ord> Select for ExtOutput<I, K> {
    fn zero() -> Self {
        Self {
            id: None,
            value: 0,
            assets: BTreeMap::new(),
        }
    }

    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        let mut assets: BTreeMap<K, u64> = BTreeMap::new();

        for (key, value) in self.assets.iter().chain(rhs.assets.iter()) {
            let value = assets.get(key).unwrap_or(&0).checked_add(*value)?;
            assets.insert(key.clone(), value);
        }

        Some(Self {
            id: None,
            value: self.value.checked_add(rhs.value)?,
            assets,
        })
    }

    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        let mut assets = self.assets.clone();

        for (key, value) in rhs.assets.iter() {
            if let Some(asset) = assets.get(key) {
                let value = asset.checked_sub(*value)?;

                if value > u64::MIN {
                    assets.insert(key.clone(), value);
                } else {
                    assets.remove(key);
                }
            }
        }

        Some(Self {
            id: None,
            value: self.value.checked_sub(rhs.value)?,
            assets,
        })
    }

    fn saturating_sub(&self, rhs: &Self) -> Self {
        let mut assets = self.assets.clone();

        for (key, value) in rhs.assets.iter() {
            if let Some(asset) = assets.get(key) {
                let value = asset.saturating_sub(*value);

                if value > u64::MIN {
                    assets.insert(key.clone(), value);
                } else {
                    assets.remove(key);
                }
            }
        }

        Self {
            id: None,
            value: self.value.saturating_sub(rhs.value),
            assets,
        }
    }

    fn compare(&self, other: &Self, output: &Self) -> Ordering {
        let lhs = self
            .assets
            .keys()
            .filter(|k| !output.assets.contains_key(k))
            .count();
        let rhs = other
            .assets
            .keys()
            .filter(|k| !output.assets.contains_key(k))
            .count();

        lhs.cmp(&rhs).then({
            let lhs = output
                .assets
                .keys()
                .filter(|k| self.assets.contains_key(k))
                .count();
            let rhs = output
                .assets
                .keys()
                .filter(|k| other.assets.contains_key(k))
                .count();

            rhs.cmp(&lhs).then({
                let lhs = self.value;
                let rhs = other.value;

                rhs.cmp(&lhs)
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use std::{cmp::Ordering, collections::BTreeMap};

    use crate::{select, ExtOutput, Output, Select};

    impl<I> From<u64> for Output<I> {
        fn from(value: u64) -> Self {
            Self { id: None, value }
        }
    }

    #[test]
    fn test_output() {
        let output: Output<u8> = 7.into();

        assert_eq!(output.compare(&8.into(), &9.into()), Ordering::Greater)
    }

    #[test]
    fn test_output_select_ok() {
        let mut inputs: [Output<u8>; 5] = [5.into(), 7.into(), 2.into(), 1.into(), 8.into()];

        assert_eq!(
            select(&mut inputs, &13.into(), &Output::zero()),
            Some((
                [8.into(), 7.into()].as_mut_slice(),
                [2.into(), 1.into(), 5.into()].as_mut_slice(),
                2.into()
            ))
        );

        assert_eq!(
            select(&mut inputs, &15.into(), &2.into()),
            Some((
                [8.into(), 7.into(), 5.into()].as_mut_slice(),
                [1.into(), 2.into()].as_mut_slice(),
                5.into()
            ))
        );

        assert_eq!(
            select(&mut inputs, &10.into(), &8.into()),
            Some((
                [8.into(), 7.into(), 5.into()].as_mut_slice(),
                [1.into(), 2.into()].as_mut_slice(),
                10.into()
            ))
        );
    }

    #[test]
    fn test_output_select_failed() {
        let mut inputs: [Output<u8>; 2] = [5.into(), 7.into()];
        let total_output: Output<u8> = 13.into();

        assert_eq!(select(&mut inputs, &total_output, &Output::zero()), None);
    }

    #[test]
    fn test_ext_output() {
        let goal = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 10;
            output.assets.insert(&"asset1", 10);
            output.assets.insert(&"asset2", 20);
            output
        };

        let output = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 20;
            output.assets.insert(&"asset1", 30);
            output.assets.insert(&"asset3", 1);
            output
        };

        assert_eq!(goal.saturating_sub(&output), {
            let mut assets: BTreeMap<&str, u64> = BTreeMap::new();
            assets.insert(&"asset2", 20);

            ExtOutput {
                id: None,
                value: 0,
                assets,
            }
        });

        assert_eq!(goal.checked_sub(&output), None);

        assert_eq!(goal.checked_add(&output), {
            let mut assets: BTreeMap<&str, u64> = BTreeMap::new();
            assets.insert(&"asset1", 40);
            assets.insert(&"asset2", 20);
            assets.insert(&"asset3", 1);

            Some(ExtOutput {
                id: None,
                value: 30,
                assets,
            })
        });

        let output = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 10;
            output.assets.insert(&"asset1", 10);
            output
        };

        assert_eq!(goal.checked_sub(&output), {
            let mut assets: BTreeMap<&str, u64> = BTreeMap::new();
            assets.insert(&"asset2", 20);

            Some(ExtOutput {
                id: None,
                value: 0,
                assets,
            })
        });
    }
}
