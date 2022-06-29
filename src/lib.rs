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

/// Sum the total output, returning `None` if overflow occurred.
pub fn try_sum<T: Select>(outputs: &[T]) -> Option<T> {
    outputs
        .iter()
        .try_fold(T::zero(), |acc, output| acc.checked_add(output))
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
///
/// The algorithm of selection picks the closest.
/// 1. Computes `wanted - unwanted` assets in the outputs, the larger the better.
/// Returns `0` if there are more unwanted assets.
/// 2. If the values of #1 are equal, computes the absolute differences between
/// `wanted` and `unwanted` of each output, the smaller the better.
/// 3. If the values of #2 are equal, the more `wanted` assets the better.
/// 4. If the values of #3 are equal, the fewer `unwanted` assets the better.
/// 5. If the values of #4 are equal, the larger value the better.
///
/// The value of asset should not be `0`.
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
            let value = assets.get(key).unwrap_or(&u64::MIN).checked_add(*value)?;
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
            let value = assets
                .get(key)
                .or(Some(&u64::MIN))
                .and_then(|v| v.checked_sub(*value))?;

            if value > u64::MIN {
                assets.insert(key.clone(), value);
            } else {
                assets.remove(key);
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
            if let Some(value) = assets
                .get(key)
                .and_then(|v| v.saturating_sub(*value).into())
            {
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
        let self_info = AssetInfo::new(output.count_mutual(self), self.count_diff(output));
        let other_info = AssetInfo::new(output.count_mutual(other), other.count_diff(output));

        self_info
            .cmp(&other_info)
            .then_with(|| other.value.cmp(&self.value))
    }
}

impl<I, K: Ord> ExtOutput<I, K> {
    fn count_diff(&self, other: &Self) -> usize {
        self.assets
            .keys()
            .filter(|k| !other.assets.contains_key(k))
            .count()
    }

    fn count_mutual(&self, other: &Self) -> usize {
        self.assets
            .keys()
            .filter(|k| other.assets.contains_key(k))
            .count()
    }

    /// Insert asset value, skip if the value is `zero`.
    pub fn insert_asset(&mut self, key: K, value: u64) {
        if value > u64::MIN {
            self.assets.insert(key, value);
        }
    }
}

#[derive(PartialEq, Eq)]
struct AssetInfo {
    wanted: usize,
    unwanted: usize,
}

impl AssetInfo {
    fn new(wanted: usize, unwanted: usize) -> Self {
        Self { wanted, unwanted }
    }

    fn net_wanted(&self) -> usize {
        self.wanted.saturating_sub(self.unwanted)
    }

    fn abs_diff(&self) -> usize {
        self.wanted.abs_diff(self.unwanted)
    }
}

impl Ord for AssetInfo {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .net_wanted()
            .cmp(&self.net_wanted())
            .then_with(|| self.abs_diff().cmp(&other.abs_diff()))
            .then_with(|| other.wanted.cmp(&self.wanted))
            .then_with(|| self.unwanted.cmp(&other.unwanted))
    }
}

impl PartialOrd for AssetInfo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use std::{cmp::Ordering, collections::BTreeMap};

    use crate::{select, try_sum, AssetInfo, ExtOutput, Output, Select};

    impl<I> From<u64> for Output<I> {
        fn from(value: u64) -> Self {
            Self { id: None, value }
        }
    }

    #[test]
    fn test_output_compare() {
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

        assert_eq!(goal.count_diff(&output), 1);
        assert_eq!(goal.count_mutual(&output), 1);
        assert_eq!(output.count_diff(&goal), 1);
        assert_eq!(output.count_mutual(&goal), 1);

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

        assert_eq!(goal.count_diff(&output), 1);
        assert_eq!(goal.count_mutual(&output), 1);
        assert_eq!(output.count_diff(&goal), 0);
        assert_eq!(output.count_mutual(&goal), 1);

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

    #[test]
    fn test_asset_info_compare() {
        assert!(AssetInfo::new(10, 0) < AssetInfo::new(1, 0));
        assert!(AssetInfo::new(10, 1) < AssetInfo::new(1, 0));
        assert!(AssetInfo::new(4, 2) < AssetInfo::new(5, 10));
        assert!(AssetInfo::new(4, 4) < AssetInfo::new(5, 10));
        assert!(AssetInfo::new(1, 1) == AssetInfo::new(1, 1));
        assert!(AssetInfo::new(1, 1) < AssetInfo::new(0, 1));
        assert!(AssetInfo::new(1, 1) < AssetInfo::new(0, 0));
        assert!(AssetInfo::new(2, 2) < AssetInfo::new(1, 1));
    }

    #[test]
    fn test_ext_output_select_ok() {
        let goal = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 10;
            output.assets.insert(&"asset1", 10);
            output.assets.insert(&"asset2", 20);
            output
        };

        let output0 = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 20;
            output.assets.insert(&"asset1", 30);
            output.assets.insert(&"asset3", 1);
            output
        };

        let output1 = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 3;
            output.assets.insert(&"asset1", 30);
            output
        };

        let output2 = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 3;
            output.assets.insert(&"asset1", 5);
            output.assets.insert(&"asset2", 20);
            output
        };

        let output3 = {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.value = 20;
            output
        };

        let mut inputs = [
            output0.clone(),
            output1.clone(),
            output2.clone(),
            output3.clone(),
        ];

        assert_eq!(
            select(&mut inputs, &goal, &ExtOutput::zero()),
            Some((
                [output2, output1, output3].as_mut_slice(),
                [output0].as_mut_slice(),
                {
                    let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
                    output.value = 16;
                    output.assets.insert(&"asset1", 25);
                    output
                }
            ))
        );
    }

    #[test]
    fn test_ext_output_select_failed() {
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

        assert_eq!(output.checked_sub(&goal), None);

        let mut inputs = [output.clone()];

        assert_eq!(select(&mut inputs, &goal, &ExtOutput::zero()), None);
    }

    #[test]
    fn test_ext_output_insert_asset() {
        let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
        output.insert_asset(&"asset1", 0);
        assert_eq!(output, ExtOutput::zero());

        output.insert_asset(&"asset1", 1);
        assert_eq!(output, {
            let mut output: ExtOutput<u8, &str> = ExtOutput::zero();
            output.assets.insert(&"asset1", 1);
            output
        })
    }

    #[test]
    fn test_try_sum() {
        let inputs: [Output<u8>; 5] = [5.into(), 7.into(), 2.into(), 1.into(), 8.into()];
        assert_eq!(try_sum(&inputs), Some(23.into()));

        let inputs: [Output<u8>; 2] = [1.into(), u64::MAX.into()];
        assert_eq!(try_sum(&inputs), None);
    }
}
